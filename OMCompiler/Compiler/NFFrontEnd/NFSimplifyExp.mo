/*
 * This file is part of OpenModelica.
 *
 * Copyright (c) 1998-2014, Open Source Modelica Consortium (OSMC),
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

encapsulated package NFSimplifyExp

import Expression = NFExpression;
import Operator = NFOperator;
import Type = NFType;
import Call = NFCall;
import Subscript = NFSubscript;
import NFOperator.Op;
import NFPrefixes.{Variability, Purity};
import NFInstNode.InstNode;
import NFEGraph.*;

protected

import Dimension = NFDimension;
import Ceval = NFCeval;
import NFCeval.EvalTarget;
import NFFunction.Function;
import ComponentRef = NFComponentRef;
import ExpandExp = NFExpandExp;
import TypeCheck = NFTypeCheck;
import Absyn;
import AbsynUtil;
import ErrorExt;
import Flags;
import Debug;
import Array;
import MetaModelica.Dangerous.listReverseInPlace;

public

function simplifyDump
  "wrapper function for simplification to allow dumping before and afterwards"
  input Expression exp;
  output Expression res;
  input String name = "";
  input String indent = "";
algorithm
  res := simplify(exp);
  if Flags.isSet(Flags.DUMP_SIMPLIFY) and not Expression.isEqual(exp, res) then
    print(indent + "### dumpSimplify | " + name + " ###\n");
    print(indent + "[BEFORE] " + Expression.toString(exp) + "\n");
    print(indent + "[AFTER ] " + Expression.toString(res) + "\n\n");
  end if;
end simplifyDump;

function simplifyEgraph
  "egraph simplification"
  input Expression exp;
  output Expression res;
protected
  EGraph egraph;
  EClassId baseId;
  Extractor extractor;
  Integer dist, counter, sizestart;
  RuleApplier ruleApplier;
  Boolean saturated;
algorithm
  print("----simplifyEgraph-----\n");
  print("input: " + Expression.toString(exp) + "\n");
  (egraph, baseId) := EGraph.newFromExp(exp, EGraph.new());

  ruleApplier := RuleApplier.RULE_APPLIER({});
  ruleApplier := RuleApplier.addRules(ruleApplier,
   {("(+ ?a 0)", "?a", "neutral-add"),
    ("(* ?a 1)", "?a", "neutral-mul"),
    ("(+ ?a (- ?a))", "0", "inv-add"),
    ("(* ?a (/ ?a))", "1", "inv-mul"),
    ("(+ ?a ?b)", "(+ ?b ?a)", "comm-add"),
    ("(* ?a ?b)", "(* ?b ?a)", "comm-mul"),
    ("(+ ?a (+ ?b ?c))", "(+ (+ ?a ?b) ?c))", "assoc-add"),
    ("(+ ?a ?a)", "(* 2 ?a)", "a+a->2a"),
    ("(* 2 ?a)", "(+ ?a ?a)", "2*a->a+a"),
    ("(+ ?a (* ?b ?a))", "(* (+ ?b 1) ?a)", "a + b*a-> (b+1)a"),
    ("(+ (* ?c ?a) (* ?b ?a))", "(* (+ ?b ?c) ?a)", "distrib1"),
    ("(* (+ ?b ?c) ?a)", "(+ (* ?c ?a) (* ?b ?a))", "distrib2"),
    ("(* ?a (* ?b ?c))", "(* (* ?a ?b) ?c))", "assoc-mul"),
    ("(* 0 ?a)", "0", "0-mul"),
    ("(* ?a ?a)", "(^ ?a 2)", "xx->x^2"),
    ("(^ ?a 0)", "1", "pow-0"),
    ("(^ ?a 1)", "?a", "pow-1"),
    ("(* (^ ?a ?b) (^ ?a ?c))", "(^ ?a (+ ?b ?c))", "pow-rule1"),
    ("(/ (^ ?a ?c))", "(^ ?a (- ?c))", "pow-rule2"),
    ("(- ?a)", "(* -1 ?a)", "uminus=-1")});

  saturated := false;
  counter := 0;
  sizestart := UnorderedMap.size(egraph.eclasses);
  print("Size classes: " + intString(sizestart) + "\n");
  EGraph.graphDump(baseId, egraph, true);
  while not saturated and counter < sizestart loop
    (egraph, saturated) := RuleApplier.matchApplyRules(ruleApplier, egraph);
    EGraph.graphDump(baseId, egraph, false);
    if EGraph.checkInvariantsHashcons(egraph) then
      print("invariants: TRUE " + "\n");
    else
      print("invariants: FALSE " + "\n");
    end if;
    if EGraph.checkInvariantsEClasses(egraph) then
      print("invariants: TRUE " + "\n");
    else
      print("invariants: FALSE " + "\n");
    end if;
    counter := counter + 1;
  end while;
  //EGraph.printAll(baseId, egraph);
  if saturated then print("saturated!\n"); end if;
  print("Iterations: " + intString(counter) + "\n");
  print("Size classes: " + intString(UnorderedMap.size(egraph.eclasses))+ "\n");
  extractor := Extractor.new(egraph);
  (extractor, dist) := Extractor.extract(baseId, extractor);
  print("Distance: " + intString(dist) + "\n");
  res := Extractor.build(baseId, extractor);
  print("return: " + Expression.toString(res) + "\n" + "---------------\n");
end simplifyEgraph;

function simplify
  input output Expression exp;
algorithm
  exp := match exp
    case Expression.CREF()
      algorithm
        exp.cref := ComponentRef.simplifySubscripts(exp.cref);
        exp.ty := ComponentRef.getSubscriptedType(exp.cref);
      then
        exp;

    case Expression.ARRAY()
      algorithm
        exp.elements := Array.map(exp.elements, simplify);
      then
        exp;

    case Expression.RANGE()
      then simplifyRange(exp);

    case Expression.RECORD()
      algorithm
        exp.elements := list(simplify(e) for e in exp.elements);
      then
        exp;

    case Expression.CALL()              then simplifyCall(exp);
    case Expression.SIZE()              then simplifySize(exp);
    case Expression.MULTARY()           then simplifyEgraph(exp);
    case Expression.BINARY()            then simplifyEgraph(exp);
    case Expression.UNARY()             then simplifyEgraph(exp);
    case Expression.LBINARY()           then simplifyLogicBinary(exp);
    case Expression.LUNARY()            then simplifyLogicUnary(exp);
    case Expression.RELATION()          then simplifyRelation(exp);
    case Expression.IF()                then simplifyIf(exp);
    case Expression.CAST()              then simplifyCast(simplify(exp.exp), exp.ty);
    case Expression.UNBOX()             then Expression.UNBOX(simplify(exp.exp), exp.ty);
    case Expression.SUBSCRIPTED_EXP()   then simplifySubscriptedExp(exp);
    case Expression.TUPLE_ELEMENT()     then simplifyTupleElement(exp);
    case Expression.RECORD_ELEMENT()    then simplifyRecordElement(exp);
    case Expression.BOX()               then Expression.BOX(simplify(exp.exp));
    case Expression.MUTABLE()           then simplify(Mutable.access(exp.exp));
                                        else exp;
  end match;
end simplify;

function simplifyOpt
  input output Option<Expression> exp;
protected
  Expression e;
algorithm
  exp := match exp
    case SOME(e) then SOME(simplify(e));
    else exp;
  end match;
end simplifyOpt;

function simplifyRange
  input Expression range;
  output Expression exp;
protected
  Expression start_exp1, stop_exp1, start_exp2, stop_exp2;
  Option<Expression> step_exp1, step_exp2;
  Type ty, ty2;
algorithm
  Expression.RANGE(ty = ty, start = start_exp1, step = step_exp1, stop = stop_exp1) := range;

  start_exp2 := simplify(start_exp1);
  step_exp2 := simplifyOpt(step_exp1);
  stop_exp2 := simplify(stop_exp1);
  ty2 := Type.simplify(ty);

  if referenceEq(start_exp1, start_exp2) and
     referenceEq(step_exp1, step_exp2) and
     referenceEq(stop_exp1, stop_exp2) and
     referenceEq(ty, ty2) then
    exp := range;
  else
    ty := TypeCheck.getRangeType(start_exp2, step_exp2, stop_exp2,
      Type.arrayElementType(ty), AbsynUtil.dummyInfo);
    exp := Expression.RANGE(ty, start_exp2, step_exp2, stop_exp2);
  end if;
end simplifyRange;

function simplifyCall
  input output Expression callExp;
protected
  Call call;
  list<Expression> args;
  Boolean builtin, is_pure;
algorithm
  Expression.CALL(call = call) := callExp;

  callExp := match call
    case Call.TYPED_CALL(arguments = args) guard not Call.isExternal(call)
      algorithm
        if Flags.isSet(Flags.NF_EXPAND_FUNC_ARGS) then
          args := list(if Expression.hasArrayCall(arg) then arg else ExpandExp.expand(arg) for arg in args);
        end if;

        args := list(simplify(arg) for arg in args);
        call.arguments := args;
        builtin := Function.isBuiltin(call.fn);
        is_pure := not Function.isImpure(call.fn);

        // Use Ceval for builtin pure functions with literal arguments.
        if builtin then
          if is_pure and List.all(args, Expression.isLiteral) then
            try
              callExp := Ceval.evalCall(call, EvalTarget.IGNORE_ERRORS());
            else
              callExp := Expression.CALL(call);
            end try;
          else
            // do not expand builtin calls if we should not scalarize
            if Flags.isSet(Flags.NF_SCALARIZE) then
              callExp := simplifyBuiltinCall(Function.nameConsiderBuiltin(call.fn), args, call);
            else
              callExp := Expression.CALL(call);
            end if;
          end if;
        elseif Flags.isSet(Flags.NF_EVAL_CONST_ARG_FUNCS) and is_pure and List.all(args, Expression.isLiteral) then
          callExp := simplifyCall2(call);
        else
          callExp := Expression.CALL(call);
        end if;
      then
        callExp;

    case Call.TYPED_CALL(arguments = args)
      algorithm
        args := list(simplify(arg) for arg in args);
        call.arguments := args;
      then
        Expression.CALL(call);

    case Call.TYPED_ARRAY_CONSTRUCTOR() then simplifyArrayConstructor(call);
    case Call.TYPED_REDUCTION() then simplifyReduction(call);
    else callExp;
  end match;
end simplifyCall;

function simplifyCall2
  input Call call;
  output Expression outExp;
algorithm
  ErrorExt.setCheckpoint(getInstanceName());

  try
    outExp := Ceval.evalCall(call, EvalTarget.IGNORE_ERRORS());
    ErrorExt.delCheckpoint(getInstanceName());
  else
    if Flags.isSet(Flags.FAILTRACE) then
      ErrorExt.delCheckpoint(getInstanceName());
      Debug.traceln("- " + getInstanceName() + " failed to evaluate " + Call.toString(call) + "\n");
    else
      ErrorExt.rollBack(getInstanceName());
    end if;

    outExp := Expression.CALL(call);
  end try;
end simplifyCall2;

function simplifyBuiltinCall
  input Absyn.Path name;
  input list<Expression> args;
  input Call call;
  output Expression exp;
algorithm
  exp := match AbsynUtil.pathFirstIdent(name)
    case "cat"
      algorithm
        exp := ExpandExp.expandBuiltinCat(args, call);
      then
        exp;

    case "der"       then simplifyDer(listHead(args), call);
    case "fill"      then simplifyFill(listHead(args), listRest(args), call);
    case "homotopy"  then simplifyHomotopy(args, call);
    case "max"       then simplifyMinMax(args, call, isMin = false);
    case "min"       then simplifyMinMax(args, call, isMin = true);
    case "ones"      then simplifyFill(Expression.INTEGER(1), args, call);
    case "product"   then simplifySumProduct(listHead(args), call, isSum = false);
    case "sum"       then simplifySumProduct(listHead(args), call, isSum = true);
    case "transpose" then simplifyTranspose(listHead(args), call);
    case "vector"    then simplifyVector(listHead(args), call);
    case "zeros"     then simplifyFill(Expression.INTEGER(0), args, call);

    else Expression.CALL(call);
  end match;
end simplifyBuiltinCall;

function simplifyMinMax
  input list<Expression> args;
  input Call call;
  input Boolean isMin;
  output Expression exp;
protected
  Expression arg;
  Type ty;
algorithm
  if listLength(args) == 1 then
    arg := listHead(args);
    ty := Expression.typeOf(arg);

    if Type.isEmptyArray(ty) then
      ty := Type.arrayElementType(ty);
      exp := if isMin then Expression.makeMaxValue(ty) else
                           Expression.makeMinValue(ty);
    else
      exp := simplifyReducedArrayConstructor(arg, call);
    end if;
  else
    exp := Expression.CALL(call);
  end if;
end simplifyMinMax;

function simplifySumProduct
  input Expression arg;
  input Call call;
  input Boolean isSum;
  output Expression exp;
protected
  Boolean expanded;
  list<Expression> args;
  Type ty;
  Operator op;
algorithm
  (exp, expanded) := ExpandExp.expand(arg);

  if expanded then
    args := Expression.arrayScalarElements(exp);
    ty := Type.arrayElementType(Expression.typeOf(arg));

    if listEmpty(args) then
      exp := if isSum then Expression.makeZero(ty) else Expression.makeOne(ty);
    else
      exp :: args := args;
      op := if isSum then Operator.makeAdd(ty) else
                          Operator.makeMul(ty);

      for e in args loop
        exp := Expression.BINARY(exp, op, e);
      end for;
    end if;
  else
    exp := simplifyReducedArrayConstructor(exp, call);
  end if;
end simplifySumProduct;

function simplifyReducedArrayConstructor
  input Expression arg;
  input Call call;
  output Expression exp;
algorithm
  exp := match arg
    local
      Call arr_call;
      Function fn;
      Type ty;
      Variability var;
      Purity purity;

    case Expression.CALL(call = arr_call as Call.TYPED_ARRAY_CONSTRUCTOR())
      guard Type.dimensionCount(arr_call.ty) == 1
      algorithm
        Call.TYPED_CALL(fn = fn, ty = ty, var = var, purity = purity) := call;
      then
        Expression.CALL(Call.makeTypedReduction(fn, ty, var, purity, arr_call.exp, arr_call.iters, AbsynUtil.dummyInfo));

    else Expression.CALL(call);
  end match;
end simplifyReducedArrayConstructor;

function simplifyTranspose
  input Expression arg;
  input Call call;
  output Expression exp;
protected
  Expression e;
algorithm
  e := if Expression.hasArrayCall(arg) then arg else ExpandExp.expand(arg);

  exp := match e
    case Expression.ARRAY()
      guard Array.all(e.elements, Expression.isArray)
      then Expression.transposeArray(e);

    else Expression.CALL(call);
  end match;
end simplifyTranspose;

function simplifyVector
  input Expression arg;
  input Call call;
  output Expression exp;
protected
  list<Expression> expl;
  Boolean is_literal;
  Type ty;
algorithm
  expl := Expression.arrayScalarElements(arg);
  is_literal := Expression.isLiteral(arg);

  if is_literal then
    // Ranges count as literals, make sure they're expanded.
    expl := ExpandExp.expandList(expl);
  end if;

  if is_literal or List.all(expl, Expression.isScalar) then
    ty := Type.arrayElementType(Expression.typeOf(arg));
    exp := Expression.makeExpArray(listArray(expl), ty);
  else
    exp := Expression.CALL(call);
  end if;
end simplifyVector;

function simplifyFill
  input Expression fillArg;
  input list<Expression> dimArgs;
  input Call call;
  output Expression exp;
algorithm
  if List.all(dimArgs, Expression.isLiteral) then
    exp := Expression.fillArgs(fillArg, dimArgs);
  else
    exp := Expression.CALL(call);
  end if;
end simplifyFill;

function simplifyHomotopy
  input list<Expression> args;
  input Call call;
  output Expression exp;
algorithm
  exp := match Flags.getConfigString(Flags.REPLACE_HOMOTOPY)
    case "actual" then listHead(args);
    case "simplified" then listHead(listRest(args));
    else Expression.CALL(call);
  end match;
end simplifyHomotopy;

function simplifyDer
  input Expression arg;
  input Call call;
  output Expression exp;
algorithm
  if Call.variability(call) < Variability.DISCRETE then
    exp := Expression.makeZero(Expression.typeOf(arg));
  else
    exp := Expression.CALL(call);
  end if;
end simplifyDer;

function simplifyArrayConstructor
  input Call call;
  output Expression outExp;
protected
  Type ty;
  Variability var;
  Purity pur;
  Expression exp, e;
  list<tuple<InstNode, Expression>> iters;
  InstNode iter;
  Dimension dim;
  Integer dim_size;
  Boolean expanded;
algorithm
  Call.TYPED_ARRAY_CONSTRUCTOR(ty, var, pur, exp, iters) := call;
  iters := list((Util.tuple21(i), simplify(Util.tuple22(i))) for i in iters);

  outExp := matchcontinue (iters)
    case {(iter, e)}
      algorithm
        Type.ARRAY(dimensions = {dim}) := Expression.typeOf(e);
        dim_size := Dimension.size(dim);

        if dim_size == 0 then
          // Result is Array[0], return empty array expression.
          outExp := Expression.makeEmptyArray(ty);
        elseif dim_size == 1 then
          // Result is Array[1], return array with the single element.
          e := ExpandExp.expand(e);
          e := Expression.arrayScalarElement(e);
          exp := Expression.replaceIterator(exp, iter, e);
          exp := Expression.makeArray(ty, listArray({exp}));
          outExp := simplify(exp);
        elseif Expression.isLiteral(e) and not Expression.hasNonArrayIteratorSubscript(exp, iter) then
          // If the iterator is only used to subscript array expressions like
          // {{1, 2, 3}[i] in i 1:3}, then we might as well expand it.
          (outExp, expanded) := ExpandExp.expandArrayConstructor(exp, ty, iters);

          if expanded then
            outExp := simplify(outExp);
          end if;
        else
          fail();
        end if;
      then
        outExp;

    else
      algorithm
        exp := simplify(exp);
        ty := Type.simplify(ty);
      then
        Expression.CALL(Call.TYPED_ARRAY_CONSTRUCTOR(ty, var, pur, exp, iters));
  end matchcontinue;
end simplifyArrayConstructor;

function simplifyReduction
  input Call call;
  output Expression outExp;
algorithm
  outExp := match call
    local
      Expression exp, e;
      list<tuple<InstNode, Expression>> iters;
      InstNode iter;
      Dimension dim;
      Integer dim_size;

    case Call.TYPED_REDUCTION()
      algorithm
        iters := list((Util.tuple21(i), simplify(Util.tuple22(i))) for i in call.iters);
      then matchcontinue iters
        case {(iter, e)}
          algorithm
            Type.ARRAY(dimensions = {dim}) := Expression.typeOf(e);
            dim_size := Dimension.size(dim);

            if dim_size == 0 then
              // Iteration range is empty, return default value for reduction.
              SOME(outExp) := call.defaultExp;
            elseif dim_size == 1 then
              // Iteration range is one, return reduction expression with iterator value applied.
              e := ExpandExp.expand(e);
              e := Expression.arrayScalarElement(e);
              outExp := Expression.replaceIterator(call.exp, iter, e);
              outExp := simplify(outExp);
            else
              fail();
            end if;
          then
            outExp;

        case _
          guard call.var <= Variability.STRUCTURAL_PARAMETER
          then Ceval.tryEvalExp(Expression.CALL(call));

        case _
          then simplifyReduction2(AbsynUtil.pathString(Function.name(call.fn)), call.exp, iters);

        else
          algorithm
            call.exp := simplify(call.exp);
            call.iters := iters;
          then
            Expression.CALL(call);

      end matchcontinue;
  end match;
end simplifyReduction;

function simplifyReduction2
  input String name;
  input Expression exp;
  input list<tuple<InstNode, Expression>> iterators;
  output Expression outExp;
protected
  InstNode iter;
  Expression range, default_exp;
  Boolean expanded = true;
  list<tuple<InstNode, Expression>> iters = {};
  Type ty;
  Operator op;
algorithm
  ty := Expression.typeOf(exp);
  // Operator records are problematic since the start value isn't simplified
  // away currently.
  false := Type.isRecord(Type.arrayElementType(ty));

  (default_exp, op) := match name
    case "sum" then (Expression.makeZero(ty), Operator.makeAdd(ty));
    case "product" then (Expression.makeOne(ty), Operator.makeMul(ty));
  end match;

  for i in iterators loop
    (iter, range) := i;
    (range, true) := ExpandExp.expand(range);
    iters := (iter, range) :: iters;
  end for;

  outExp := Expression.foldReduction(simplify(exp), listReverseInPlace(iters),
    default_exp, simplify, function simplifyBinaryOp(op = op));
end simplifyReduction2;

function simplifySize
  input output Expression sizeExp;
algorithm
  sizeExp := match sizeExp
    local
      Expression exp, index;
      Dimension dim;
      list<Dimension> dims;

    case Expression.SIZE(exp, SOME(index))
      algorithm
        index := simplify(index);

        if Expression.isLiteral(index) then
          dim := listGet(Type.arrayDims(Expression.typeOf(exp)), Expression.toInteger(index));

          if Dimension.isKnown(dim) then
            exp := Expression.INTEGER(Dimension.size(dim));
          else
            exp := Expression.SIZE(exp, SOME(index));
          end if;
        else
          exp := Expression.SIZE(exp, SOME(index));
        end if;
      then
        exp;

    case Expression.SIZE()
      algorithm
        dims := Type.arrayDims(Expression.typeOf(sizeExp.exp));

        if List.all(dims, function Dimension.isKnown(allowExp = true)) then
          exp := Expression.makeArray(Type.ARRAY(Type.INTEGER(), {Dimension.fromInteger(listLength(dims))}),
                                      listArray(list(Dimension.sizeExp(d) for d in dims)));
        else
          exp := sizeExp;
        end if;
      then
        exp;

  end match;
end simplifySize;

function optInc
    input Option<Integer> oldValue;
    output Integer value;
algorithm

 value := match oldValue
    local
      Integer i;
    case SOME(i) then i+1;
    else 1;
  end match;
end optInc;

function optDec
    input Option<Integer> oldValue;
    output Integer value;
algorithm

 value := match oldValue
    local
      Integer i;
    case SOME(i) then i-1;
    else -1;
  end match;
end optDec;

// Checks if the expression is a multary with multiplication: adds count to arguments; else BINARY(count, exp)
function packExpr
    input Operator chainOperator;
    input output Expression exp;
    input Integer count;
algorithm
  exp := match exp
    local
      Operator operator;
      list<Expression> arguments, inv_arguments;
      Expression exp1, exp2;
    case Expression.MULTARY(arguments = arguments,inv_arguments = inv_arguments,operator = operator)
      guard(NFOperator.MathClassification.MULTIPLICATION == Operator.getMathClassification(operator)
        and NFOperator.MathClassification.ADDITION == Operator.getMathClassification(chainOperator))
      then if count > 0 then simplifyMultary(Expression.MULTARY(Expression.INTEGER(count) :: arguments, inv_arguments, operator))
        else simplifyMultary(Expression.MULTARY(arguments, Expression.INTEGER(count * (-1)) :: inv_arguments, operator));
    else match chainOperator.op
      case NFOperator.Op.ADD then if count > 0 then Expression.MULTARY({Expression.INTEGER(count),exp}, {}, NFOperator.makeMul(NFType.REAL()))
        else Expression.MULTARY({Expression.INTEGER(count * (-1)), exp}, {}, NFOperator.makeMul(NFType.REAL()));
      case NFOperator.Op.MUL then if count > 0 then Expression.BINARY(exp, NFOperator.makePow(NFType.REAL()),Expression.INTEGER(count))
        else Expression.BINARY(exp, NFOperator.makePow(NFType.REAL()), Expression.INTEGER(count * (-1)));
      end match;
  end match;
end packExpr;

function mapPowExp
  input Expression exp1;
  input output Expression exp2;
  input Operator temp_opertor;
  input UnorderedMap<Expression, Expression> powermap;
  input Integer count;
  algorithm
    exp2 := match UnorderedMap.get(exp1, powermap)
      local
        list<Expression> texp1, texp2;
      case NONE() guard(count == 1) then Expression.MULTARY({exp2}, {}, NFOperator.makeAdd(NFType.REAL()));
      case NONE() guard(count == 0) then Expression.MULTARY({}, {}, NFOperator.makeAdd(NFType.REAL()));
      case NONE() guard(count == -1) then Expression.MULTARY({}, {exp2}, NFOperator.makeAdd(NFType.REAL()));
      case NONE() guard(count > 0) then Expression.MULTARY({Expression.MULTARY(Expression.REAL(count) :: {exp2}, {}, NFOperator.makeMul(NFType.REAL()))}, {}, NFOperator.makeAdd(NFType.REAL()));
      case NONE() guard(count < 0) then Expression.MULTARY({}, {Expression.MULTARY(Expression.REAL(-1*count) :: {exp2}, {}, NFOperator.makeMul(NFType.REAL()))}, NFOperator.makeAdd(NFType.REAL()));
      case SOME(Expression.MULTARY(arguments = texp1,   inv_arguments = texp2))guard(count == 1) then Expression.MULTARY(exp2 :: texp1, texp2, NFOperator.makeAdd(NFType.REAL()));
      case SOME(Expression.MULTARY(arguments = texp1,  inv_arguments = texp2))guard(count == 0) then Expression.MULTARY(texp1, texp2, NFOperator.makeAdd(NFType.REAL()));
      case SOME(Expression.MULTARY(arguments = texp1,  inv_arguments = texp2))guard(count == -1) then Expression.MULTARY(texp1, exp2 :: texp2, NFOperator.makeAdd(NFType.REAL()));
      case SOME(Expression.MULTARY(arguments = texp1,  inv_arguments = texp2))guard(count > 0)
        then Expression.MULTARY(Expression.MULTARY({Expression.REAL(count), exp2}, {}, NFOperator.makeMul(NFType.REAL())) :: texp1, texp2, NFOperator.makeAdd(NFType.REAL()));
      case SOME(Expression.MULTARY(arguments = texp1,  inv_arguments = texp2))guard(count < 0)
        then Expression.MULTARY(texp1, Expression.MULTARY({Expression.REAL(-1*count), exp2}, {}, NFOperator.makeMul(NFType.REAL())) :: texp2, NFOperator.makeAdd(NFType.REAL()));
    end match;
end mapPowExp;

function addmulRealval
  input output Real realval;
  input Expression arg;
  input Operator operator;
  input Boolean inverted; // True if inverted, False if not
algorithm
  realval := match (operator.op, inverted)
    local
    case (NFOperator.Op.ADD, false) then realval + getConstantValue(arg, true);
    case (NFOperator.Op.MUL, false) then realval * getConstantValue(arg, true);
    case (NFOperator.Op.ADD, true) then realval - getConstantValue(arg, true);
    case (NFOperator.Op.MUL, true) then realval / getConstantValue(arg, true);
  end match;
end addmulRealval;

function checkMultaryOperator
  input Expression arg;
  input Operator operator;
  output Boolean b;
algorithm
  b := match arg
      local
       Operator temp_operator;
    case Expression.MULTARY(operator = temp_operator) guard(Operator.compare(temp_operator,operator) == 0) then true;
    else false;
  end match;

end checkMultaryOperator;

function simplifyMultary
  input output Expression exp;
protected
  EGraph egraph;
  ENode temp_node;
  EClassId id1, id2, id3, id4, id5, id6, id7, id8, id9, id10;
  Extractor extractor;
  Integer dist, counter, sizestart;
  UnorderedMap<Integer, EClassId> subs;
  Rule r;
  RuleApplier ruleapplier;
  Boolean saturated;
  NFExpression expr;
algorithm
  /*egraph := EGraph.new();

  temp_node := ENode.NUM(5);
  (egraph,id1) := EGraph.add(temp_node,egraph);

  temp_node := ENode.NUM(0);
  (egraph,id2) := EGraph.add(temp_node,egraph);

  temp_node := ENode.BINARY(id2, id2, BinaryOp.ADD);
  (egraph,id6) := EGraph.add(temp_node, egraph);

  temp_node := ENode.BINARY(id6, id1, BinaryOp.ADD);
  (egraph,id3) := EGraph.add(temp_node, egraph);

  temp_node := ENode.NUM(1);
  (egraph,id4) := EGraph.add(temp_node, egraph);

  temp_node := ENode.BINARY(id3, id4, BinaryOp.MUL);
  (egraph,id5) := EGraph.add(temp_node, egraph);

  temp_node := ENode.BINARY(id5, id1, BinaryOp.MUL);
  (egraph,id7) := EGraph.add(temp_node, egraph);

  temp_node := ENode.SYMBOL("x");
  (egraph,id1) := EGraph.add(temp_node,egraph);
  temp_node := ENode.NUM(7);
  (egraph,id3) := EGraph.add(temp_node,egraph);
  temp_node := ENode.UNARY(id1, UnaryOp.UMINUS);
  (egraph,id2) := EGraph.add(temp_node, egraph);
  temp_node := ENode.BINARY(id1, id3, BinaryOp.ADD);
  (egraph,id4) := EGraph.add(temp_node, egraph);
  temp_node := ENode.BINARY(id4, id2, BinaryOp.ADD);
  (egraph,id6) := EGraph.add(temp_node, egraph);
  temp_node := ENode.BINARY(id6, id6, BinaryOp.ADD);
  (egraph,id7) := EGraph.add(temp_node, egraph);

  // x * ((0 + 0) + x) * 1) -> x * x
  print("\n");

  egraph := EGraph.rebuild(egraph);
  ruleapplier := RuleApplier.RULEAPPLIER({});
  ruleapplier := RuleApplier.addRules(ruleapplier,
  {{"(+ ?a 0)", "?a", "neutral-add"},
  {"(* ?a 1)", "?a","neutral-mul"},
  {"(+ ?a (- ?a))", "0", "inv-add"},
  {"(* ?a (/ ?a))", "1", "inv-mul"},
  {"(+ ?a ?b)", "(+ ?b ?a)", "comm-add"},
  {"(* ?a ?b)", "(* ?b ?a)", "comm-mul"},
  {"(+ ?a (+ ?b ?c))", "(+ (+ ?a ?b) ?c))", "assoc-add"},
  {"(* ?a (* ?b ?c))", "(* (* ?a ?b) ?c))", "assoc-mul"},
  {"(* 0 ?a)", "0", "0-mul"},
  {"(* ?a ?a)","(^ ?a 2)", "xx->x^2"}});
  saturated := false;
  counter := 0;
  sizestart := UnorderedMap.size(egraph.eclasses);
  print("Size classes: " + intString(sizestart) + "\n");
  while not saturated and counter < sizestart loop
    (egraph, saturated) := RuleApplier.matchApplyRules(ruleapplier, egraph);
    counter := counter + 1;

  end while;
  if saturated then print("saturated! \n"); end if;
  print("Iterations: " + intString(counter) + "\n");
  print("Size classes: " + intString(UnorderedMap.size(egraph.eclasses))+ "\n");

  extractor := Extractor.new(egraph);
  (extractor, dist) := Extractor.extract(id7, extractor);
  print("Distance: " + intString(dist) + "\n");
  expr := Extractor.build(id7, extractor);
  print("Build done\n");
  print(Expression.toString(expr));
  print("\n");*/
  exp := match exp
    local
      Operator operator,temp_operator;
      list<Expression> arguments, inv_arguments, const_args, inv_const_args, temp_arguments,temp_inv_arguments, texp1, texp2;
      list<Expression> newarguments, newinv_arguments;
      Expression new_const, tmp, result, exp1, exp2;
      String test;
      Real realval;
      Operator.MathClassification mcl;
      Boolean useConst, isNegative, anyReal = true, isPowBinaryMul;
      UnorderedMap<Expression,Integer> map;
      UnorderedMap<Expression, Expression> powermap;
      Integer count;

    // empty multary with addition -> 0
    case Expression.MULTARY(arguments = {}, inv_arguments = {}, operator = operator)
      guard(Operator.isDashClassification(Operator.getMathClassification(operator)))
    then Expression.makeZero(operator.ty);

    // empty multary with multiplication -> 1
    case Expression.MULTARY(arguments = {}, inv_arguments = {}, operator = operator)
    then Expression.makeOne(operator.ty);

    // multary with only one argument
    case Expression.MULTARY(arguments = {tmp}, inv_arguments = {})
    then tmp;

    // non-empty multaries
    case Expression.MULTARY(arguments = arguments, inv_arguments = inv_arguments, operator = operator) algorithm
      // get math classification
      mcl := Operator.getMathClassification(operator);

      // simplify arguments first
      arguments := list(simplify(arg) for arg in arguments);
      inv_arguments := list(simplify(arg) for arg in inv_arguments);
      (arguments, inv_arguments, isNegative) := simplifyMultarySigns(arguments, inv_arguments, mcl);

      // new map: expression, count: int
      map := UnorderedMap.new<Integer>(Expression.hash, Expression.isEqual);

      // realval is the real factor/sum in a multary
      realval := NFOperator.neutralElement(operator);

      // maps expressions, adds constants
      for arg in arguments loop
        // Mupper: arguments, elem: constant
        if Expression.isConstNumber(arg) then
          realval := addmulRealval(realval, arg, operator, false);
        // if operator of the lower multary is the same as in the upper multary, args and invargs get mapped or get added to the realval
        elseif (checkMultaryOperator(arg, operator)) then
          Expression.MULTARY(arguments = temp_arguments,inv_arguments = temp_inv_arguments, operator = temp_operator) := arg;
          for tmp in temp_arguments loop
            // Mupper: arguments, Mlower: arguments
            if Expression.isConstNumber(tmp) then
              realval := addmulRealval(realval, tmp, operator, false);
            else
              UnorderedMap.addUpdate(tmp, optInc, map);
            end if;
          end for;

          for tmp in temp_inv_arguments loop
            // Mupper: arguments, Mlower: inv_arguments
            if Expression.isConstNumber(tmp) then
              realval := addmulRealval(realval, tmp, operator, true);
            else
              UnorderedMap.addUpdate(tmp, optDec, map);
            end if;
          end for;
        else
          UnorderedMap.addUpdate(arg, optInc, map);
        end if;
      end for;

      // same for inv_arguments
      for invarg in inv_arguments loop
        // Mupper: inv_arguments, elem: constant
        if Expression.isConstNumber(invarg) then
          realval := addmulRealval(realval, invarg, operator, true);
        // if operator of the lower multary is the same as in the upper multary, args and invargs get mapped or get added to the realval
        elseif (checkMultaryOperator(invarg, operator)) then
          Expression.MULTARY(arguments = temp_arguments,inv_arguments = temp_inv_arguments, operator = temp_operator) := invarg;
          for tmp in temp_arguments loop
            // Mupper: inv_arguments, Mlower: arguments
            if Expression.isConstNumber(tmp) then
              realval := addmulRealval(realval, tmp, operator, true);
            else
              UnorderedMap.addUpdate(tmp, optDec, map);
            end if;
          end for;
          // Mupper: inv_arguments, Mlower: inv_arguments
          for tmp in temp_inv_arguments loop
            if Expression.isConstNumber(tmp) then
              realval := addmulRealval(realval, tmp, operator, false);
            else
              UnorderedMap.addUpdate(tmp, optInc, map);
            end if;
          end for;
        else
          UnorderedMap.addUpdate(invarg, optDec, map);
        end if;
      end for;

      newarguments := {};
      newinv_arguments := {};
      // separate map: base -> (count1 * exponent1 + ...)
      powermap := UnorderedMap.new<Expression>(Expression.hash, Expression.isEqual);

      // packing of the arguments
      for elem in UnorderedMap.toList(map) loop
        (tmp, count) := elem;

        isPowBinaryMul := match tmp
          case Expression.BINARY(_, NFOperator.OPERATOR(_,NFOperator.Op.POW), _) guard(operator.op == NFOperator.Op.MUL) then true;
          else false;
        end match;

        if isPowBinaryMul then
          Expression.BINARY(exp1 = exp1, operator = temp_operator, exp2 = exp2):= tmp;
          exp2 := simplify(combineBinaries(exp2)); // apparently the exponent is always a binary, therefore a multary is created and simplified
          exp2 := mapPowExp(exp1, exp2, temp_operator, powermap, count);
          UnorderedMap.add(exp1, exp2, powermap);
        elseif count > 0 then
          if count == 1 then
            newarguments := tmp :: newarguments;
          else
            newarguments := packExpr(operator, tmp, count) :: newarguments;
          end if;
        elseif count < 0 then
          if count == -1 then
            newinv_arguments := tmp :: newinv_arguments;
          else
            newinv_arguments := packExpr(operator, tmp, count) :: newinv_arguments;
          end if;
        end if;
      end for;
      // packing of all power terms
      for elem in UnorderedMap.toList(powermap) loop
        (exp1, exp2) := elem;
        // simplifyBinary to insure cases like base^0 or base^1 are covered
        newarguments := simplifyBinary(Expression.BINARY(exp1, NFOperator.makePow(NFType.REAL()), exp2)) :: newarguments;
      end for;

      // replacing arguments/inv_arguments
      arguments := newarguments;
      inv_arguments := newinv_arguments;

      // split them into constant and non constant arguments
      (const_args, arguments) := List.splitOnTrue(arguments, Expression.isConstNumber);
      (inv_const_args, inv_arguments) := List.splitOnTrue(inv_arguments, Expression.isConstNumber);

      // combine the constants
      new_const := combineConstantNumbers(const_args, inv_const_args, mcl);

      // return combined multary expression and check for trivial replacements

      // check if the constant is used
      useConst := match mcl
        case NFOperator.MathClassification.ADDITION guard(Expression.isZero(new_const)) then false;
        case NFOperator.MathClassification.MULTIPLICATION guard(Expression.isOne(new_const)) then false;
        else true;
      end match;

      result := match (mcl, arguments, inv_arguments)
        // const + {} - {} = const
        // const * {} / {} = const
        case (_, {}, {}) then new_const;

        // 0 + {cr} - {} = cr
        // 1 * {cr} / {} = cr
        case (_, {tmp}, {}) guard(not useConst) then tmp;

        // 0 + {} - {cr} = - cr
        case (NFOperator.MathClassification.ADDITION, {}, {tmp}) guard(not useConst)
        then Expression.negate(tmp);

        // 0 * {...} / {...} = 0
        case (NFOperator.MathClassification.MULTIPLICATION, _, _) guard(Expression.isZero(new_const)) then new_const;

        // THIS SEEMS LIKE A BAD IDEA STRUCTURALLY
        // apply negative constant to inverse list for addition
        //case (NFOperator.MathClassification.ADDITION, _, _) guard(Expression.isNegative(new_const) and useConst)
        //then Expression.MULTARY(
        //    arguments     = arguments,
        //    inv_arguments = Expression.negate(new_const) :: inv_arguments,
        //    operator      = operator
        //  );

        else Expression.MULTARY(
            arguments     = if useConst then new_const :: arguments else arguments,
            inv_arguments = inv_arguments,
            operator      = operator
          );
      end match;

      // negate the expression if there was an odd number of negative arguments (only multiplication)
    then if isNegative then Expression.negate(result) else result;

    else algorithm
      Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed for expression: " + Expression.toString(exp)});
    then fail();
  end match;
end simplifyMultary;

function simplifyMultarySigns
  input list<Expression> arguments;
  input list<Expression> inv_arguments;
  input Operator.MathClassification mcl;
  output list<Expression> new_arguments = {};
  output list<Expression> new_inv_arguments = {};
  output Boolean isNegative = false; // only relevant for multiplication
algorithm
  _ := match mcl
    case NFOperator.MathClassification.ADDITION algorithm
      // check if arguments are negative
      // negate them and swap them to the other list
      for arg in listReverse(arguments) loop
        if Expression.isNegative(arg) then
          new_inv_arguments := Expression.negate(arg) :: new_inv_arguments;
        else
          new_arguments := arg :: new_arguments;
        end if;
      end for;
      for arg in listReverse(inv_arguments) loop
        if Expression.isNegative(arg) then
          new_arguments := Expression.negate(arg) :: new_arguments;
        else
          new_inv_arguments := arg :: new_inv_arguments;
        end if;
      end for;
    then ();

    case NFOperator.MathClassification.MULTIPLICATION algorithm
      // check if arguments are negative and negate them.
      // track if there is an even or odd number of negative arguments
      for arg in listReverse(arguments) loop
        if Expression.isNegative(arg) then
          new_arguments := Expression.negate(arg) :: new_arguments;
          isNegative := not isNegative;
        else
          new_arguments := arg :: new_arguments;
        end if;
      end for;
      for arg in listReverse(inv_arguments) loop
        if Expression.isNegative(arg) then
          new_inv_arguments := Expression.negate(arg) :: new_inv_arguments;
          isNegative := not isNegative;
        else
          new_inv_arguments := arg :: new_inv_arguments;
        end if;
      end for;
    then ();

    else algorithm
      Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed."});
    then fail();
  end match;
end simplifyMultarySigns;

function simplifyBinary
  input output Expression binaryExp;
protected
  Expression e1, e2, se1, se2;
  Operator op;
algorithm
  Expression.BINARY(e1, op, e2) := binaryExp;
  se1 := simplify(e1);
  se2 := simplify(e2);

  binaryExp := simplifyBinaryOp(se1, op, se2);

  if Flags.isSet(Flags.NF_EXPAND_OPERATIONS) and not Expression.hasArrayCall(binaryExp) then
    binaryExp := ExpandExp.expand(binaryExp);
  end if;
end simplifyBinary;

function simplifyBinaryOp
  input Expression exp1;
  input Operator op;
  input Expression exp2;
  output Expression outExp;

  import NFOperator.Op;
algorithm
  if Expression.isLiteral(exp1) and Expression.isLiteral(exp2) then
    outExp := Ceval.evalBinaryOp(ExpandExp.expand(exp1), op, ExpandExp.expand(exp2));
  else
    outExp := match op.op
      case Op.ADD then simplifyBinaryAdd(exp1, op, exp2);
      case Op.SUB then simplifyBinarySub(exp1, op, exp2);
      case Op.MUL then simplifyBinaryMul(exp1, op, exp2);
      case Op.DIV then simplifyBinaryDiv(exp1, op, exp2);
      case Op.POW then simplifyBinaryPow(exp1, op, exp2);
      else Expression.BINARY(exp1, op, exp2);
    end match;
  end if;
end simplifyBinaryOp;

function simplifyBinaryAdd
  input Expression exp1;
  input Operator op;
  input Expression exp2;
  output Expression outExp;
algorithm
  if Expression.isZero(exp1) then
    // 0 + e = e
    outExp := exp2;
  elseif Expression.isZero(exp2) then
    // e + 0 = e
    outExp := exp1;
  elseif Expression.isNegated(exp2) then
    // e1 + -(e2) = e1 - e2
    outExp := Expression.BINARY(exp1, Operator.invert(op), Expression.negate(exp2));
  else
    outExp := Expression.BINARY(exp1, op, exp2);
  end if;
end simplifyBinaryAdd;

function simplifyBinarySub
  input Expression exp1;
  input Operator op;
  input Expression exp2;
  output Expression outExp;
algorithm
  if Expression.isZero(exp1) then
    // 0 - e = -e
    outExp := Expression.UNARY(Operator.makeUMinus(Operator.typeOf(op)), exp2);
  elseif Expression.isZero(exp2) then
    // e - 0 = e
    outExp := exp1;
  elseif Expression.isNegated(exp2) then
    // e1 - -(e2) = e1 + e2
    outExp := Expression.BINARY(exp1, Operator.invert(op), Expression.negate(exp2));
  else
    outExp := Expression.BINARY(exp1, op, exp2);
  end if;
end simplifyBinarySub;

function simplifyBinaryMul
  input Expression exp1;
  input Operator op;
  input Expression exp2;
  input Boolean switched = false;
  output Expression outExp;
algorithm
  outExp := match exp1
    // 0 * e = 0
    case Expression.INTEGER(value = 0) then exp1;
    case Expression.REAL(value = 0.0) then exp1;

    // 1 * e = e
    case Expression.INTEGER(value = 1) then exp2;
    case Expression.REAL(value = 1.0) then exp2;

    else
      if switched then
        Expression.BINARY(exp2, op, exp1)
      else
        simplifyBinaryMul(exp2, op, exp1, true);
  end match;
end simplifyBinaryMul;

function simplifyBinaryDiv
  input Expression exp1;
  input Operator op;
  input Expression exp2;
  output Expression outExp;
algorithm
  // fix constants
  // e / 1 = e
  // e / (-1) = -e
  // 0 / e = 0 (e <> 0)
  outExp :=
    if Expression.isOne(exp2) then exp1
    elseif Expression.isMinusOne(exp2) then Expression.negate(exp1)
    elseif Expression.isZero(exp1) and not Expression.isZero(exp2) then exp1
    // fix minus signs
    // (-e1)/(-e2) = e1/e2
    // e1/(-e2) = -(e1/e2)
    // (-e1)/e2 = -(e1/e2)
    // e1/e2 = e1/e2
    else match (Expression.isNegative(exp1), Expression.isNegative(exp1))
      case (true, true)     then Expression.BINARY(Expression.negate(exp1), op, Expression.negate(exp2));
      case (false, true)    then Expression.negate(Expression.BINARY(exp1, op, Expression.negate(exp2)));
      case (true, false)    then Expression.negate(Expression.BINARY(Expression.negate(exp1), op, exp2));
      case (false, false)   then Expression.BINARY(exp1, op, exp2);
    end match;
end simplifyBinaryDiv;

function simplifyBinaryPow
  input Expression exp1;
  input Operator op;
  input Expression exp2;
  output Expression outExp;
algorithm
  if Expression.isZero(exp2) then
    outExp := Expression.makeOne(Operator.typeOf(op));
  elseif Expression.isOne(exp2) then
    outExp := exp1;
  else
    outExp := Expression.BINARY(exp1, op, exp2);
  end if;
end simplifyBinaryPow;

function simplifyUnary
  input output Expression unaryExp;
protected
  Expression e, se;
  Operator op;
algorithm
  unaryExp := match unaryExp
    case Expression.UNARY(_, Expression.UNARY(_, e))
    then simplify(e);

    case Expression.UNARY(op, e) algorithm
      se := simplify(e);
    then simplifyUnaryOp(se, op);

    else algorithm
      Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed."});
    then fail();
  end match;

  if Flags.isSet(Flags.NF_EXPAND_OPERATIONS) and not Expression.hasArrayCall(unaryExp) then
    unaryExp := ExpandExp.expand(unaryExp);
  end if;
end simplifyUnary;

function simplifyUnaryOp
  input Expression exp;
  input Operator op;
  output Expression outExp;
algorithm
  if Expression.isLiteral(exp) then
    outExp := Ceval.evalUnaryOp(exp, op);
  else
    outExp := simplifyUnarySign(exp, true);
  end if;
end simplifyUnaryOp;

function simplifyUnarySign
  input output Expression unaryExp;
  input Boolean isNegative = false;
algorithm
  unaryExp := match unaryExp
    case Expression.UNARY() then simplifyUnarySign(unaryExp.exp, not isNegative);
    else if isNegative then Expression.negate(unaryExp) else unaryExp;
  end match;
end simplifyUnarySign;

function simplifyLogicBinary
  input output Expression binaryExp;
protected
  Expression e1, e2, se1, se2;
  Operator op;
algorithm
  Expression.LBINARY(e1, op, e2) := binaryExp;
  se1 := simplify(e1);
  se2 := simplify(e2);

  binaryExp := match op.op
    case Op.AND then simplifyLogicBinaryAnd(se1, op, se2);
    case Op.OR then simplifyLogicBinaryOr(se1, op, se2);
  end match;
end simplifyLogicBinary;

function simplifyLogicBinaryAnd
  input Expression exp1;
  input Operator op;
  input Expression exp2;
  output Expression exp;
algorithm
  exp := match (exp1, exp2)
    local
      list<Expression> expl;
      Operator o;
      array<Expression> arr;

    // false and e => false
    case (Expression.BOOLEAN(false), _) then exp1;
    // e and false => false
    case (_, Expression.BOOLEAN(false)) then exp2;
    // true and e => e
    case (Expression.BOOLEAN(true), _)  then exp2;
    // e and true => e
    case (_, Expression.BOOLEAN(true))  then exp1;

    case (Expression.ARRAY(), Expression.ARRAY())
      algorithm
        o := Operator.unlift(op);
        arr := Array.threadMap(exp1.elements, exp2.elements,
          function simplifyLogicBinaryAnd(op = o));
      then
        Expression.makeArray(Operator.typeOf(op), arr);

    else Expression.LBINARY(exp1, op, exp2);
  end match;
end simplifyLogicBinaryAnd;

function simplifyLogicBinaryOr
  input Expression exp1;
  input Operator op;
  input Expression exp2;
  output Expression exp;
algorithm
  exp := match (exp1, exp2)
    local
      list<Expression> expl;
      Operator o;
      array<Expression> arr;

    // true or e => true
    case (Expression.BOOLEAN(true), _) then exp1;
    // e or true => true
    case (_, Expression.BOOLEAN(true)) then exp2;
    // false or e => e
    case (Expression.BOOLEAN(false), _) then exp2;
    // e or false => e
    case (_, Expression.BOOLEAN(false)) then exp1;

    case (Expression.ARRAY(), Expression.ARRAY())
      algorithm
        o := Operator.unlift(op);
        arr := Array.threadMap(exp1.elements, exp2.elements,
          function simplifyLogicBinaryOr(op = o));
      then
        Expression.makeArray(Operator.typeOf(op), arr);

    else Expression.LBINARY(exp1, op, exp2);
  end match;
end simplifyLogicBinaryOr;

function simplifyLogicUnary
  input output Expression unaryExp;
protected
  Expression e, se;
  Operator op;
algorithm
  Expression.LUNARY(op, e) := unaryExp;
  se := simplify(e);

  if Expression.isLiteral(se) then
    unaryExp := Ceval.evalLogicUnaryOp(se, op);
  elseif not referenceEq(e, se) then
    unaryExp := Expression.LUNARY(op, se);
  end if;
end simplifyLogicUnary;

function simplifyRelation
  input output Expression relationExp;
protected
  Expression e1, e2, se1, se2;
  Operator op;
algorithm
  Expression.RELATION(e1, op, e2) := relationExp;
  se1 := simplify(e1);
  se2 := simplify(e2);

  if Expression.isLiteral(se1) and Expression.isLiteral(se2) then
    relationExp := Ceval.evalRelationOp(se1, op, se2);
  elseif not (referenceEq(e1, se1) and referenceEq(e2, se2)) then
    relationExp := Expression.RELATION(se1, op, se2);
  end if;
end simplifyRelation;

function simplifyIf
  input output Expression ifExp;
protected
  Type ty;
  Expression cond, tb, fb;
  Boolean tb_val;
algorithm
  Expression.IF(ty, cond, tb, fb) := ifExp;
  cond := simplify(cond);

  ifExp := match cond
    case Expression.BOOLEAN()
      then simplify(if cond.value then tb else fb);

    else
      algorithm
        tb := simplify(tb);
        fb := simplify(fb);

        if Expression.isEqual(tb, fb) then
          // if cond then x else x => x
          ifExp := tb;
        elseif Expression.isBoolean(tb) and Expression.isBoolean(fb) then
          // if cond then true else false => cond
          // if cond then false else true => not cond
          Expression.BOOLEAN(value = tb_val) := tb;
          ifExp := if tb_val then cond else Expression.logicNegate(cond);
        else
          ifExp := Expression.IF(ty, cond, tb, fb);
        end if;
      then
        ifExp;

  end match;
end simplifyIf;

function simplifyCast
  input Expression exp;
  input Type ty;
  output Expression castExp;
algorithm
  castExp := match (ty, exp)
    local
      Type ety;

    case (Type.REAL(), Expression.INTEGER())
      then Expression.REAL(intReal(exp.value));

    case (Type.ARRAY(elementType = Type.REAL()), Expression.ARRAY())
      algorithm
        ety := Type.unliftArray(ty);
        exp.elements := Array.map(exp.elements, function simplifyCast(ty = ety));
        exp.ty := Type.setArrayElementType(exp.ty, Type.arrayElementType(ty));
      then
        exp;

    else Expression.CAST(ty, exp);
  end match;
end simplifyCast;

function simplifySubscriptedExp
  input output Expression subscriptedExp;
protected
  Expression e;
  list<Subscript> subs;
  Type ty;
  Boolean split;
algorithm
  Expression.SUBSCRIPTED_EXP(e, subs, ty, split) := subscriptedExp;
  subscriptedExp := simplify(e);
  subs := Subscript.simplifyList(subs, Type.arrayDims(Expression.typeOf(e)));

  if split then
    subscriptedExp := Expression.SUBSCRIPTED_EXP(subscriptedExp, subs, ty, split);
  else
    subscriptedExp := Expression.applySubscripts(subs, subscriptedExp);
  end if;
end simplifySubscriptedExp;

function simplifyTupleElement
  input output Expression tupleExp;
protected
  Expression e;
  Integer index;
  Type ty;
algorithm
  Expression.TUPLE_ELEMENT(e, index, ty) := tupleExp;
  e := simplify(e);
  tupleExp := Expression.tupleElement(e, ty, index);
end simplifyTupleElement;

function simplifyRecordElement
  input output Expression exp;
protected
  Expression e, e2;
  Integer idx;
  Type ty;
algorithm
  Expression.RECORD_ELEMENT(e, idx, _, ty) := exp;
  e2 := simplify(e);

  if not referenceEq(e, e2) then
    exp := Expression.nthRecordElement(idx, e2);
  end if;
end simplifyRecordElement;

public function combineConstantNumbers
  input list<Expression> const      "has to be a list of REAL(), INTEGER() and/or CAST()";
  input list<Expression> inv_const  "has to be a list of REAL(), INTEGER() and/or CAST()";
  input Operator.MathClassification mcl;
  output Expression res;
protected
  Real tmp, result;
  Boolean anyReal = false         "true if any element in the list is of type REAL() (or cast to one)";
algorithm
  result := match mcl

    case NFOperator.MathClassification.ADDITION algorithm
      result := 0.0;
      // sum all constants
      for exp in const loop
        (tmp, anyReal) := getConstantValue(exp, anyReal);
        result := result + tmp;
      end for;
      // subtract all inverse constants
      for exp in inv_const loop
        (tmp, anyReal) := getConstantValue(exp, anyReal);
        result := result - tmp;
      end for;
    then result;

    case NFOperator.MathClassification.MULTIPLICATION algorithm
      result := 1.0;
      // multiply all constants
      for exp in const loop
        (tmp, anyReal) := getConstantValue(exp, anyReal);
        result := result * tmp;
      end for;
      // devide all inverse constants
      for exp in inv_const loop
        (tmp, anyReal) := getConstantValue(exp, anyReal);
        result := result / tmp;
      end for;
    then result;

    else algorithm
      Error.assertion(false, getInstanceName() + " detected non-commutative operator in MULTARY(): [" + Operator.mathSymbol(mcl) +
       "]\n with following arguments: " + stringDelimitList(list(Expression.toString(e) for e in const), ", ") +
       "\n and following inverse arguments: " + stringDelimitList(list(Expression.toString(e) for e in inv_const), ", "),
       sourceInfo());
    then fail();

  end match;

  res := if anyReal then Expression.REAL(result) else Expression.INTEGER(realInt(result));
end combineConstantNumbers;

protected function getConstantValue
  input Expression exp "REAL(), INTEGER(), CAST(), UNARY()";
  output Real value;
  input output Boolean anyReal;
algorithm
  (value, anyReal) := match exp
    local
      Real r;
      Integer i;
      Boolean b;
    case Expression.REAL(value = r)    then (r, true);
    case Expression.INTEGER(value = i) then (intReal(i), anyReal);
    case Expression.CAST() algorithm
      (r, b) := getConstantValue(exp.exp, anyReal);
      // negate b because it has been cast
    then (r, anyReal or (not b));
    case Expression.UNARY(operator = Operator.OPERATOR(op = NFOperator.Op.UMINUS)) algorithm
      (r, b) := getConstantValue(exp.exp, anyReal);
      // negate r because it has a minus sign
    then (-r, anyReal or b);
    else algorithm
      Error.assertion(false, getInstanceName() + " expression is not known to be a constant number: " + Expression.toString(exp), sourceInfo());
    then fail();
  end match;
end getConstantValue;

public function combineBinaries
  "just a wrapper to remove the interface for traversal"
  input output Expression exp;
algorithm
  exp := combineBinariesExp(exp);
end combineBinaries;

protected function combineBinariesExp
  "author: kabdelhak 09-2020
  Combines binaries for better handling in the backend.
  NOTE: 1. does not do any other simplification
        2. also combines inverse operations
  e.g. BINARY(BINARY(2, /, y^2), *, BINARY(3, *, x))
   --> MULTARY({2, 3, x}, {y^2},*)"
  input Expression exp;
  input Option<Operator> optOperator = NONE();
  input output Expression result = Expression.EMPTY(Expression.typeOf(exp));
  input Boolean inverse = false;
algorithm
  result := match (optOperator, exp)
    local
      Operator op;
      list<Expression> tmp, tmp_inv;
      list<Expression> final_stack = {};
      list<Expression> final_inverse_stack = {};
      Expression new_exp;
      ComponentRef cref;
      Call call;

    // #######################################################
    //          Building MULTARY() recursively
    // #######################################################

    // case 1.0 binary SOME(op) same operator (+, *)
    case (SOME(op), Expression.BINARY()) guard(Operator.compare(op, exp.operator) == 0) algorithm
      result := combineBinariesExp(exp.exp1, SOME(op), result, inverse);
      result := combineBinariesExp(exp.exp2, SOME(op), result, inverse);
    then result;

    // case 1.1 multary SOME(op) same operator (+, *)
    case (SOME(op), Expression.MULTARY()) guard(Operator.compare(op, exp.operator) == 0) algorithm
      for arg in exp.arguments loop
        result := combineBinariesExp(arg, SOME(exp.operator), result, inverse);
      end for;
      for arg in exp.inv_arguments loop
        result := combineBinariesExp(arg, SOME(exp.operator), result, not inverse);
      end for;
    then result;

    // case 2.0 binary SOME(op) inverse operator (-, :)
    case (SOME(op), Expression.BINARY()) guard(Operator.isCombineable(op, exp.operator)) algorithm
      result := combineBinariesExp(exp.exp1, SOME(op), result, inverse);
      result := combineBinariesExp(exp.exp2, SOME(op), result, not inverse);
    then result;

    // case 2.1 multary SOME(op) inverse operator (-, :)
    case (SOME(op), Expression.MULTARY()) guard(Operator.isCombineable(op, exp.operator)) algorithm
      for arg in exp.arguments loop
        result := combineBinariesExp(arg, SOME(exp.operator), result, inverse);
      end for;
      for arg in exp.inv_arguments loop
        result := combineBinariesExp(arg, SOME(exp.operator), result, not inverse);
      end for;
    then result;

    // ##########################################################
    //                 Starts a new MULTARY()
    // previous not compatible or no MULTARY on the stack at all
    // ##########################################################

   // case 3.0 _ binary | commutative operator (+, *)
    case (_, Expression.BINARY()) guard(Operator.isCommutative(exp.operator)) algorithm
      new_exp := Expression.MULTARY({}, {}, exp.operator);
      new_exp := combineBinariesExp(exp.exp2, SOME(exp.operator), new_exp, false);
      new_exp := combineBinariesExp(exp.exp1, SOME(exp.operator), new_exp, false);
    then addArgument(result, new_exp, inverse);

    // case 3.1 _ multary | commutative operator (+, *)
    case (_, Expression.MULTARY()) guard(Operator.isCommutative(exp.operator)) algorithm
      new_exp := Expression.MULTARY({}, {}, exp.operator);
      for arg in exp.arguments loop
        new_exp := combineBinariesExp(arg, SOME(exp.operator), new_exp, false);
      end for;
      for arg in exp.inv_arguments loop
        new_exp := combineBinariesExp(arg, SOME(exp.operator), new_exp, true);
      end for;
    then addArgument(result, new_exp, inverse);

    // case 4.0 _ binary | soft commutative operator (-, :)
    case (_, Expression.BINARY()) guard(Operator.isSoftCommutative(exp.operator)) algorithm
      op := Operator.invert(exp.operator);
      new_exp := Expression.MULTARY({}, {}, op);
      new_exp := combineBinariesExp(exp.exp1, SOME(op), new_exp, false);
      new_exp := combineBinariesExp(exp.exp2, SOME(op), new_exp, true);
    then addArgument(result, new_exp, inverse);

    // case 4.1 _ multary soft | commutative operator (-, :)
    // THIS IS NOT ALLOWED TO EXIST!

    // #######################################################
    //      Other expressions that do not get combined
    // #######################################################

    // going deeper on the different expression types

    case (_, Expression.CREF(cref = cref as ComponentRef.CREF())) algorithm
      cref.subscripts := list(combineBinariesSubscript(sub) for sub in cref.subscripts);
      exp.cref := cref;
    then addArgument(result, exp, inverse);

    case (_, Expression.ARRAY()) algorithm
      exp.elements := Array.map(exp.elements,
        function combineBinariesExp(optOperator = NONE(),
          result = Expression.EMPTY(Expression.typeOf(exp)), inverse = false));
    then addArgument(result, exp, inverse);

    case (_, Expression.RANGE()) algorithm
      exp.start := combineBinariesExp(exp.start);
      exp.stop := combineBinariesExp(exp.stop);
      if Util.isSome(exp.step) then
        exp.step := SOME(combineBinariesExp(Util.getOption(exp.step)));
      end if;
    then addArgument(result, exp, inverse);

    case (_, Expression.TUPLE()) algorithm
      exp.elements := list(combineBinariesExp(element) for element in exp.elements);
    then addArgument(result, exp, inverse);

    case (_, Expression.RECORD()) algorithm
      exp.elements := list(combineBinariesExp(element) for element in exp.elements);
    then addArgument(result, exp, inverse);

    case (_, Expression.CALL(call = call as Call.TYPED_CALL())) algorithm
      call.arguments := list(combineBinariesExp(arg) for arg in call.arguments);
      exp.call := call;
    then addArgument(result, exp, inverse);

    case (_, Expression.SIZE()) algorithm
      exp.exp := combineBinariesExp(exp.exp);
      if Util.isSome(exp.dimIndex) then
        exp.dimIndex := SOME(combineBinariesExp(Util.getOption(exp.dimIndex)));
      end if;
    then addArgument(result, exp, inverse);

    case (_, Expression.UNARY()) algorithm
      exp.exp := combineBinariesExp(exp.exp);
    then addArgument(result, exp, inverse);

    // ToDo: rules for logical operators (LMULTARY ?)
    // For now leave them as is and traverse branches
    case (_, Expression.LBINARY()) algorithm
      exp.exp1 := combineBinariesExp(exp.exp1);
      exp.exp2 := combineBinariesExp(exp.exp2);
    then addArgument(result, exp, inverse);

    case (_, Expression.LUNARY()) algorithm
      exp.exp := combineBinariesExp(exp.exp);
    then addArgument(result, exp, inverse);

    case (_, Expression.RELATION()) algorithm
      exp.exp1 := combineBinariesExp(exp.exp1);
      exp.exp2 := combineBinariesExp(exp.exp2);
    then addArgument(result, exp, inverse);

    case (_, Expression.IF()) algorithm
      exp.condition := combineBinariesExp(exp.condition);
      exp.trueBranch := combineBinariesExp(exp.trueBranch);
      exp.falseBranch := combineBinariesExp(exp.falseBranch);
    then addArgument(result, exp, inverse);

    case (_, Expression.CAST()) algorithm
      exp.exp := combineBinariesExp(exp.exp);
    then addArgument(result, exp, inverse);

    case (_, Expression.BOX()) algorithm
      exp.exp := combineBinariesExp(exp.exp);
    then addArgument(result, exp, inverse);

    case (_, Expression.UNBOX()) algorithm
      exp.exp := combineBinariesExp(exp.exp);
    then addArgument(result, exp, inverse);

    case (_, Expression.SUBSCRIPTED_EXP()) algorithm
      exp.exp := combineBinariesExp(exp.exp);
      exp.subscripts := list(combineBinariesSubscript(sub) for sub in exp.subscripts);
    then addArgument(result, exp, inverse);

    case (_, Expression.TUPLE_ELEMENT()) algorithm
      exp.tupleExp := combineBinariesExp(exp.tupleExp);
    then addArgument(result, exp, inverse);

    case (_, Expression.RECORD_ELEMENT()) algorithm
      exp.recordExp := combineBinariesExp(exp.recordExp);
    then addArgument(result, exp, inverse);

    case (_, Expression.MUTABLE()) algorithm
      Mutable.update(exp.exp, combineBinariesExp(Mutable.access(exp.exp)));
    then addArgument(result, exp, inverse);

    case (_, Expression.PARTIAL_FUNCTION_APPLICATION()) algorithm
      exp.args := list(combineBinariesExp(arg) for arg in exp.args);
    then addArgument(result, exp, inverse);

    // done on this branch
    else addArgument(result, exp, inverse);
  end match;
end combineBinariesExp;

protected function combineBinariesSubscript
  input output Subscript subscript;
algorithm
  subscript := match subscript
    case Subscript.UNTYPED() algorithm
      subscript.exp := combineBinariesExp(subscript.exp);
    then subscript;

    case Subscript.INDEX() algorithm
      subscript.index := combineBinariesExp(subscript.index);
    then subscript;

    case Subscript.SLICE() algorithm
      subscript.slice := combineBinariesExp(subscript.slice);
    then subscript;

    case Subscript.EXPANDED_SLICE() algorithm
      subscript.indices := list(combineBinariesSubscript(sub) for sub in subscript.indices);
    then subscript;

    else subscript;
  end match;
end combineBinariesSubscript;

protected function addArgument
  input output Expression exp;
  input Expression arg;
  input Boolean inverse;
algorithm
  exp := match exp
    // add to inverse arguments
    case Expression.MULTARY() guard(inverse) algorithm
      exp.inv_arguments := arg :: exp.inv_arguments;
    then exp;

    // add to arguments
    case Expression.MULTARY() algorithm
      exp.arguments := arg :: exp.arguments;
    then exp;

    // no multary on the stack, just return the expression
    case Expression.EMPTY() then arg;

    // cannot be parsed
    else algorithm
      Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed to add : " +
        Expression.toString(arg) + " to " + Expression.toString(exp) + ". Only works for MULTARY()!"});
    then fail();
  end match;
end addArgument;

annotation(__OpenModelica_Interface="frontend");
end NFSimplifyExp;
