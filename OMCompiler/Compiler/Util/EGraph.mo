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
    EGraph egraph = getEGraph();
  algorithm
    simplifyExp_impl(egraph.rules, toPrefixString(exp));
  end simplifyExp;

protected

  record E_GRAPH
    Rules rules           "";
//    Runner runner         "";
//    Extractor extractor   "";
  end E_GRAPH;

  function getEGraph
    output EGraph egraph;
  protected
    Option<EGraph> ograph = getGlobalRoot(Global.eGraph);
  algorithm
    egraph := match ograph
      case SOME(egraph) then egraph;
      else algorithm
        egraph := E_GRAPH(rules = Rules());
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

//  class Runner
//    extends ExternalObject;
//  end Runner;
//
//  class Extractor
//    extends ExternalObject;
//  end Extractor;


  // ---------------------------------------------------------------------------
  // MetaModelica Expression to Rust String
  // ---------------------------------------------------------------------------



  function toPrefixString
    "Prints an Expression in prefix notation, e.g. `2*x+y` is (+ (* 2 x) y)"
    input Expression exp;
    //input UnorderedMap<> crefMap;
    output String str;
  protected
    Type t;
    //ClockKind clk;
    Expression first, first_inv;
    list<Expression> rest, rest_inv;
  algorithm
    str := match exp
      case Expression.INTEGER() then intString(exp.value);
      case Expression.REAL()    then realString(exp.value);
      case Expression.STRING()  then "\"" + System.escapedString(exp.value, false) + "\"";
      case Expression.BOOLEAN() then boolString(exp.value);

      case Expression.ENUM_LITERAL(ty = t as Type.ENUMERATION())
        then AbsynUtil.pathString(t.typePath) + "." + exp.name;

      //case Expression.CLKCONST(clk) then ClockKind.toString(clk);
      case Expression.CREF() then ComponentRef.toString(exp.cref);
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

      case Expression.CALL() then callPrefixString(exp.call);

      //case Expression.SIZE() then "size(" + Expression.toString(exp.exp) +
      //                  (
      //                  if isSome(exp.dimIndex)
      //                  then ", " + Expression.toString(Util.getOption(exp.dimIndex))
      //                  else ""
      //                  ) + ")";
      case Expression.END() then "end";

      case Expression.MULTARY() guard(listEmpty(exp.inv_arguments))
        then multaryPrefixString(exp.arguments, exp.operator);

      case Expression.MULTARY() guard(listEmpty(exp.arguments) and Operator.isDashClassification(Operator.getMathClassification(exp.operator)))
        then "(- 0 " + multaryPrefixString(exp.inv_arguments, exp.operator) + ")";

      case Expression.MULTARY() guard(listEmpty(exp.arguments))
        then "(/ 1 " + multaryPrefixString(exp.inv_arguments, exp.operator) + ")";

      case Expression.MULTARY()
        then "(" + Operator.symbol(Operator.invert(exp.operator), "") + " " +
          multaryPrefixString(exp.arguments, exp.operator) + " " +
          multaryPrefixString(exp.inv_arguments, exp.operator) + ")";

      case Expression.BINARY()
        then "(" + Operator.symbol(exp.operator, "") + " " +
          toPrefixString(exp.exp1) + " " + toPrefixString(exp.exp2) + ")";

      case Expression.UNARY()
        then "(" + Operator.symbol(exp.operator, "") + " 0 " +
          toPrefixString(exp.exp) + ")";

      case Expression.LBINARY()
        then "(" + Operator.symbol(exp.operator, "") + " " +
          toPrefixString(exp.exp1) + " " + toPrefixString(exp.exp2) + ")";

      case Expression.LUNARY()
        then "(" + Operator.symbol(exp.operator, "") + " " +
          toPrefixString(exp.exp) + ")";

      case Expression.RELATION()
        then "(" + Operator.symbol(exp.operator, "") + " " +
          toPrefixString(exp.exp1) + " " + toPrefixString(exp.exp2) + ")";

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
  end toPrefixString;

  function multaryPrefixString
    input list<Expression> arguments;
    input Operator operator;
    output String str;
  protected
    Expression first;
    list<Expression> rest;
  algorithm
    first :: rest := arguments;
    if listEmpty(rest) then
      str := toPrefixString(first);
    else
      str := "(" + Operator.symbol(operator, "") + " " +
             toPrefixString(first) + " " +
             multaryPrefixString(rest, operator) + ")";
    end if;
  end multaryPrefixString;

  function callPrefixString
    input NFCall call;
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
          arg_str := stringDelimitList(list(toPrefixString(arg) for arg in call.arguments), " ");
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
          arg_str := stringDelimitList(list(toPrefixString(arg) for arg in call.arguments), " ");
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
  end callPrefixString;

  // ---------------------------------------------------------------------------
  // RUST FFI
  // ---------------------------------------------------------------------------

  function simplifyExp_impl
    input Rules r;
    input String e "expression in prefix notation";
    external "C" egg_simplify_expr(r, e) annotation(Library="omcruntime");
  end simplifyExp_impl;

annotation(__OpenModelica_Interface="util");
end EGraph;
