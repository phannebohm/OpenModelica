/*
 * This file is part of OpenModelica.
 *
 * Copyright (c) 1998-CurrentYear, Open Source Modelica Consortium (OSMC),
 * c/o Linköpings universitet, Department of Computer and Information Science,
 * SE-58183 Linköping, Sweden.
 *
 * All rights reserved.
 *
 * THIS PROGRAM IS PROVIDED UNDER THE TERMS OF GPL VERSION 3 LICENSE OR
 * THIS OSMC PUBLIC LICENSE (OSMC-PL) VERSION 1.2.
 * ANY USE, REPRODUCTION OR DISTRIBUTION OF THIS PROGRAM CONSTITUTES
 * RECIPIENT'S ACCEPTANCE OF THE OSMC PUBLIC LICENSE OR THE GPL VERSION 3,
 * ACCORDING TO RECIPIENTS CHOICE.
 *
 * The OpenModelica software and the Open Source Modelica
 * Consortium (OSMC) Public License (OSMC-PL) are obtained
 * from OSMC, either from the above address,
 * from the URLs: http://www.ida.liu.se/projects/OpenModelica or
 * http://www.openmodelica.org, and in the OpenModelica distribution.
 * GNU version 3 is obtained from: http://www.gnu.org/copyleft/gpl.html.
 *
 * This program is distributed WITHOUT ANY WARRANTY; without
 * even the implied warranty of  MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE, EXCEPT AS EXPRESSLY SET FORTH
 * IN THE BY RECIPIENT SELECTED SUBSIDIARY LICENSE CONDITIONS OF OSMC-PL.
 *
 * See the full OSMC Public License conditions for more details.
 *
 */

encapsulated uniontype EGraph
  "An interface to egg, a rust implementation of e-graphs."

protected

  import AbsynUtil;
  import Call = NFCall;
  import ComponentRef = NFComponentRef;
  import Expression = NFExpression;
  import NFFunction.Function;
  import Global;
  import Operator = NFOperator;
  import System;
  import Type = NFType;

public

  function simplifyExp
    input output Expression exp;
  protected
    EGraph egraph;
    String expStr;
    UnorderedMap<Expression, String> crefToId;
    UnorderedMap<String, Expression> idToCref;
    Boolean debug = false;
  algorithm
    // shortcut for crefs
    if Expression.isCref(exp) then return; end if;

    crefToId := UnorderedMap.new<String>(Expression.hash, Expression.isEqual);

    expStr := expToStr(exp, crefToId);
    idToCref := UnorderedMap.invert(crefToId, stringHashDjb2, stringEq);
    if debug then
      print("var map: " + UnorderedMap.toString(crefToId, Expression.toString, Util.id, ", ") + "\n");
      print("inv map: " + UnorderedMap.toString(idToCref, Util.id, Expression.toString, ", ") + "\n");
      print(expStr + "\n");
      System.fflush();
    end if;
    egraph := getEGraph();
    expStr := simplifyExp_impl(egraph.rules, egraph.runner, expStr);
    exp := strToExp(expStr, idToCref);
  end simplifyExp;

protected

  record E_GRAPH
    Rules rules           "";
    Runner runner         "";
//    Extractor extractor   "";
  end E_GRAPH;

  constant Boolean debug = false;

  function getEGraph
    output EGraph egraph;
  protected
    Option<EGraph> ograph = getGlobalRoot(Global.eGraph);
  algorithm
    egraph := match ograph
      case SOME(egraph) then egraph;
      else algorithm
        egraph := E_GRAPH(rules = Rules(), runner = Runner());
        setGlobalRoot(Global.eGraph, SOME(egraph));
      then egraph;
    end match;
  end getEGraph;

  class Rules
    extends ExternalObject;
    function constructor
      output Rules rules;
    external "C"
      rules = egg_make_rules() annotation(Library="omcruntime");
    end constructor;
    function destructor
      input Rules rules;
    external "C"
      egg_free_rules(rules) annotation(Library="omcruntime");
    end destructor;
  end Rules;

  class Runner
    extends ExternalObject;
    function constructor
      output Runner runner;
    external "C"
      runner = egg_make_runner() annotation(Library="omcruntime");
    end constructor;
    function destructor
      input Runner runner;
    external "C"
      egg_free_runner(runner) annotation(Library="omcruntime");
    end destructor;
  end Runner;

  //  class Extractor
  //    extends ExternalObject;
  //  end Extractor;


  // ---------------------------------------------------------------------------
  // MetaModelica Expression to Rust String
  // ---------------------------------------------------------------------------

  function expToStr
    "Prints an Expression in prefix notation, e.g. `2*x+y` is (+ (* 2 x) y)"
    input Expression exp;
    input UnorderedMap<Expression, String> crefToId;
    output String str;
  protected
    Type t;
    //ClockKind clk;
    Expression first, first_inv;
    list<Expression> rest, rest_inv;
  algorithm
    str := match exp
      case Expression.CREF()
        then UnorderedMap.tryAdd(exp, "x" + intString(UnorderedMap.size(crefToId)), crefToId);

      case Expression.INTEGER() then intString(exp.value);
      case Expression.REAL()    then realString(exp.value);
      case Expression.STRING()  then "\"" + System.escapedString(exp.value, false) + "\"";
      case Expression.BOOLEAN() then boolString(exp.value);

      case Expression.ENUM_LITERAL(ty = t as Type.ENUMERATION())
        then AbsynUtil.pathString(t.typePath) + "." + exp.name;

      //case Expression.CLKCONST(clk) then ClockKind.toString(clk);
      case Expression.TYPENAME() then Type.typenameString(Type.arrayElementType(exp.ty));
      case Expression.ARRAY() then "{" + stringDelimitList(list(Expression.toString(e) for e in exp.elements), ", ") + "}";
      case Expression.MATRIX() then "[" + stringDelimitList(list(stringDelimitList(list(Expression.toString(e) for e in el), ", ") for el in exp.elements), "; ") + "]";

      //case Expression.RANGE() then operandString(exp.start, exp, false) +
      //                  (
      //                  if isSome(exp.step)
      //                  then ":" + operandString(Util.getOption(exp.step), exp, false)
      //                  else ""
      //                  ) + ":" + operandString(exp.stop, exp, false);

      //case Expression.TUPLE() then "(" + stringDelimitList(list(Expression.toString(e) for e in exp.elements), ", ") + ")";
      //case Expression.RECORD() then List.toString(exp.elements, Expression.toString, AbsynUtil.pathString(exp.path), "(", ", ", ")", true);

      case Expression.CALL() then callToStr(exp.call, crefToId);

      //case Expression.SIZE() then "size(" + Expression.toString(exp.exp) +
      //                  (
      //                  if isSome(exp.dimIndex)
      //                  then ", " + Expression.toString(Util.getOption(exp.dimIndex))
      //                  else ""
      //                  ) + ")";
      case Expression.END() then "end";

      case Expression.MULTARY() guard(listEmpty(exp.inv_arguments))
        then multaryToStr(exp.arguments, exp.operator, crefToId);

      case Expression.MULTARY() guard(listEmpty(exp.arguments) and Operator.isDashClassification(Operator.getMathClassification(exp.operator)))
        then "(- 0 " + multaryToStr(exp.inv_arguments, exp.operator, crefToId) + ")";

      case Expression.MULTARY() guard(listEmpty(exp.arguments))
        then "(/ 1 " + multaryToStr(exp.inv_arguments, exp.operator, crefToId) + ")";

      case Expression.MULTARY()
        then "(" + Operator.symbol(Operator.invert(exp.operator), "") + " " +
          multaryToStr(exp.arguments, exp.operator, crefToId) + " " +
          multaryToStr(exp.inv_arguments, exp.operator, crefToId) + ")";

      case Expression.BINARY()
        then "(" + Operator.symbol(exp.operator, "") + " " +
          expToStr(exp.exp1, crefToId) + " " + expToStr(exp.exp2, crefToId) + ")";

      case Expression.UNARY()
        then "(" + Operator.symbol(exp.operator, "") + " 0 " +
          expToStr(exp.exp, crefToId) + ")";

      case Expression.LBINARY()
        then "(" + Operator.symbol(exp.operator, "") + " " +
          expToStr(exp.exp1, crefToId) + " " + expToStr(exp.exp2, crefToId) + ")";

      case Expression.LUNARY()
        then "(" + Operator.symbol(exp.operator, "") + " " +
          expToStr(exp.exp, crefToId) + ")";

      case Expression.RELATION()
        then "(" + Operator.symbol(exp.operator, "") + " " +
          expToStr(exp.exp1, crefToId) + " " + expToStr(exp.exp2, crefToId) + ")";

      //case Expression.IF() then "if " + Expression.toString(exp.condition) + " then " + Expression.toString(exp.trueBranch) + " else " + Expression.toString(exp.falseBranch);

      //case Expression.CAST() then if Flags.isSet(Flags.NF_API) then
      //                   Expression.toString(exp.exp)
      //                 else
      //                   "CAST(" + Type.Expression.toString(exp.ty) + ", " + Expression.toString(exp.exp) + ")";

      //case Expression.BOX() then "BOX(" + Expression.toString(exp.exp) + ")";
      //case Expression.UNBOX() then "UNBOX(" + Expression.toString(exp.exp) + ")";
      //case Expression.SUBSCRIPTED_EXP() then Expression.toString(exp.exp) + Subscript.toStringList(exp.subscripts);
      //case Expression.TUPLE_ELEMENT() then Expression.toString(exp.tupleExp) + "[" + intString(exp.index) + "]";
      //case Expression.RECORD_ELEMENT() then Expression.toString(exp.recordExp) + "[field: " + exp.fieldName + "]";
      //case Expression.MUTABLE() then Expression.toString(Mutable.access(exp.exp));
      //case Expression.EMPTY() then "#EMPTY#";
      //case Expression.PARTIAL_FUNCTION_APPLICATION()
      //  then "function " + ComponentRef.toString(exp.fn) + "(" + stringDelimitList(
      //    list(n + " = " + Expression.toString(a) threaded for a in exp.args, n in exp.argNames), ", ") + ")";

      else algorithm
        print("PH: unable to prefix " + Expression.toString(exp) + "\n");
      then "ERROR";
    end match;
  end expToStr;

  function multaryToStr
    input list<Expression> arguments;
    input Operator operator;
    input UnorderedMap<Expression, String> crefToId;
    output String str;
  protected
    Expression first;
    list<Expression> rest;
  algorithm
    first :: rest := arguments;
    if listEmpty(rest) then
      str := expToStr(first, crefToId);
    else
      str := "(" + Operator.symbol(operator, "") + " " +
             expToStr(first, crefToId) + " " +
             multaryToStr(rest, operator, crefToId) + ")";
    end if;
  end multaryToStr;

  function callToStr
    input NFCall call;
    input UnorderedMap<Expression, String> crefToId;
    output String str;
  protected
    String name, arg_str,c;
    Expression argexp;
    //list<InstNode> iters;
  algorithm
    str := match call
      case Call.UNTYPED_CALL()
        algorithm
          name := ComponentRef.toString(call.ref);
          arg_str := stringDelimitList(list(expToStr(arg, crefToId) for arg in call.arguments), " ");
        then
          "(" + name + " " + arg_str + ")";

      case Call.ARG_TYPED_CALL()
        algorithm
          name := ComponentRef.toString(call.ref);
          arg_str := stringDelimitList(list(Expression.toString(arg.value) for arg in call.positional_args), " ");
          for arg in call.named_args loop
            c := if arg_str == "" then "" else ", ";
            arg_str := arg_str + c + Util.getOption(arg.name) + " = " + Expression.toString(arg.value);
          end for;
        then
          "(" + name + " " + arg_str + ")";

      //case Call.UNTYPED_ARRAY_CONSTRUCTOR()
      //  algorithm
      //    name := AbsynUtil.pathString(Function.nameConsiderBuiltin(NFBuiltinFuncs.ARRAY_FUNC));
      //    arg_str := Expression.toString(call.exp);
      //    c := stringDelimitList(list(InstNode.name(Util.tuple21(iter)) + " in " +
      //      Expression.toString(Util.tuple22(iter)) for iter in call.iters), ", ");
      //  then
      //    "{" + arg_str + " for " + c + "}";

      //case Call.UNTYPED_REDUCTION()
      //  algorithm
      //    name := ComponentRef.toString(call.ref);
      //    arg_str := Expression.toString(call.exp);
      //    c := stringDelimitList(list(InstNode.name(Util.tuple21(iter)) + " in " +
      //      Expression.toString(Util.tuple22(iter)) for iter in call.iters), ", ");
      //  then
      //    name + "(" + arg_str + " for " + c + ")";

      case Call.TYPED_CALL()
        algorithm
          name := AbsynUtil.pathString(Function.nameConsiderBuiltin(call.fn));
          arg_str := stringDelimitList(list(expToStr(arg, crefToId) for arg in call.arguments), " ");
        then
          "(" + name + " " + arg_str + ")";

      //case Call.TYPED_ARRAY_CONSTRUCTOR()
      //  algorithm
      //    name := AbsynUtil.pathString(Function.nameConsiderBuiltin(NFBuiltinFuncs.ARRAY_FUNC));
      //    arg_str := Expression.toString(call.exp);
      //    c := stringDelimitList(list(InstNode.name(Util.tuple21(iter)) + " in " +
      //      Expression.toString(Util.tuple22(iter)) for iter in call.iters), ", ");
      //  then
      //    "{" + arg_str + " for " + c + "}";

      //case Call.TYPED_REDUCTION()
      //  algorithm
      //    name := AbsynUtil.pathString(Function.nameConsiderBuiltin(call.fn));
      //    arg_str := Expression.toString(call.exp);
      //    c := stringDelimitList(list(InstNode.name(Util.tuple21(iter)) + " in " +
      //      Expression.toString(Util.tuple22(iter)) for iter in call.iters), ", ");
      //  then
      //    name + "(" + arg_str + " for " + c + ")";

      else algorithm
        print("PH: unable to prefix " + Call.toString(call) + "\n");
      then "ERROR";
    end match;
  end callToStr;

  // ---------------------------------------------------------------------------

  function strToExp
    "Takes a prefix notation and builds an Expression from it."
    input String str;
    input UnorderedMap<String, Expression> idToCref;
    input Integer start = 1                 "start of substring";
    input Integer stop = stringLength(str)  "end of substring";
    output Expression exp;
  algorithm
    if debug then print(getInstanceName() + " parsing " + substring(str, start, stop) + "\n"); end if;
    if stringGet(str, start) == stringCharInt("(") then
      if stringGet(str, stop) == stringCharInt(")") then
        exp := strToExp_call(str, idToCref, start + 1, stop - 1);
      else
        print(getInstanceName() + " error: missing closing parenthesis\n");
        fail();
      end if;
    else
      exp := strToExp_leaf(str, idToCref, start, stop);
    end if;
  end strToExp;

  function strToExp_call
    input String str;
    input UnorderedMap<String, Expression> idToCref;
    input Integer inStart "start of substring";
    input Integer inStop  "end of substring";
    output Expression exp;
  protected
    String call;
    list<Expression> exp_list = {};
    Integer start = inStart;
    Integer stop;
    Integer nesting = 0;
    Integer i;
    constant Integer CHAR_SPACE = stringCharInt(" ");
    constant Integer CHAR_OPEN_PAR = stringCharInt("(");
    constant Integer CHAR_CLOSE_PAR = stringCharInt(")");
  algorithm
    if debug then print(getInstanceName() + " parsing " + substring(str, inStart, inStop) + "\n"); end if;

    // find operator, search from left to first space
    stop := start;
    while stringGet(str, stop+1) <> CHAR_SPACE and stop < inStop loop
      stop := stop + 1;
    end while;

    call := substring(str, start, stop);
    if debug then print(" - call: " + substring(str, start, stop) + "\n"); end if;

    // find all operands, search from right to left
    start := stop; // keep the space in front of first operand
    stop := inStop;

    if debug then print(" - args: " + substring(str, start, stop) + "\n"); end if;

    i := inStop;
    while i >= start loop
      () := match stringGet(str, i)
        case CHAR_CLOSE_PAR algorithm
          nesting := nesting + 1;
        then ();
        case CHAR_OPEN_PAR algorithm
          nesting := nesting - 1;
          if nesting < 0 then
            print(getInstanceName() + " error: too many opening parentheses\n");
            fail();
          end if;
        then ();
        case CHAR_SPACE guard nesting == 0 algorithm
          exp_list := strToExp(str, idToCref, i + 1, stop) :: exp_list;
          stop := i - 1;
        then ();
        else ();
      end match;
      i := i - 1;
    end while;

    // build expression from call and args

    exp := match (call, exp_list)
      local
        Expression arg1, arg2;
      case ("+", {arg1, arg2}) then Expression.repairOperator(Expression.BINARY(arg1, Operator.makeAdd(Expression.typeOf(arg1)), arg2));
      case ("-", {arg1, arg2}) then Expression.repairOperator(Expression.BINARY(arg1, Operator.makeSub(Expression.typeOf(arg1)), arg2));
      case ("*", {arg1, arg2}) then Expression.repairOperator(Expression.BINARY(arg1, Operator.makeMul(Expression.typeOf(arg1)), arg2));
      case ("/", {arg1, arg2}) then Expression.repairOperator(Expression.BINARY(arg1, Operator.makeDiv(Expression.typeOf(arg1)), arg2));
      case ("^", {arg1, arg2}) then Expression.repairOperator(Expression.BINARY(arg1, Operator.makePow(Expression.typeOf(arg1)), arg2));
      case ("sin", {arg1}) then Expression.CALL(Call.makeTypedCall(
          fn          = NFBuiltinFuncs.SIN_REAL,
          args        = {arg1},
          variability = Expression.variability(arg1),
          purity      = NFPrefixes.Purity.PURE
        ));
      else algorithm
        print(getInstanceName() + " error: could not parse operator " + call + " with arguments " + List.toString(exp_list, Expression.toString) + "\n");
      then fail();
    end match;
  end strToExp_call;

  function strToExp_leaf
    "Documentation"
    input String str;
    input UnorderedMap<String, Expression> idToCref;
    input Integer start "start of substring";
    input Integer stop  "end of substring";
    output Expression exp;
  protected
    String s = substring(str, start, stop);
  algorithm
    if debug then print(getInstanceName() + " parsing " + s + "\n"); end if;
    if UnorderedMap.contains(s, idToCref) then
      exp := UnorderedMap.getOrFail(s, idToCref);
    else
      try
        exp := Expression.INTEGER(stringInt(s));
      else
        try
          exp := Expression.REAL(stringReal(s));
        else
          print(getInstanceName() + "error: could not parse " + s + "\n");
          fail();
        end try;
      end try;
    end if;
  end strToExp_leaf;


  // ---------------------------------------------------------------------------
  // RUST FFI
  // ---------------------------------------------------------------------------

  function simplifyExp_impl
    input Rules rules;
    input Runner runner;
    input String e "expression in prefix notation";
    output String res;
    external "C" res = egg_simplify_expr(rules, runner, e) annotation(Library="omcruntime");
  end simplifyExp_impl;

annotation(__OpenModelica_Interface="util");
end EGraph;
