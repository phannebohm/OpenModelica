encapsulated package NFUnitCheck
" file:        NFUnitCheck.mo
  package:     UnitCheck
  description: This package provides everything for advanced unit checking:
                 - for all variables unspecified units get calculated if possible
                 - inconsistent equations get reported in a user friendly way
               authors: Jan Hagemann and Lennart Ochel (FH Bielefeld, Germany)"

public
import Absyn;
import AbsynUtil;
//import DAE;
import FlatModel = NFFlatModel;
import FunctionTree = NFFlatten.FunctionTree;

protected
import ComponentRef = NFComponentRef;
import Ceval = NFCeval;
import ElementSource;
import Equation = NFEquation;
import ExecStat.execStat;
import ExpressionDump;
import Expression = NFExpression;
import Binding = NFBinding;
import Call = NFCall;
import Component = NFComponent;
import NFFunction.Function;
import NFInstNode.InstNode;
import Operator = NFOperator;
import Type = NFType;
import Unit = NFUnit;
import Variable = NFVariable;
import Variability = NFPrefixes.Variability;

uniontype Functionargs
  record FUNCTIONUNITS
    String name;
    list<String> invars;
    list<String> outvars;
    list<String> inunits;
    list<String> outunits;
  end FUNCTIONUNITS;
end Functionargs;

type FunctionUnitCache = UnorderedMap<String, Functionargs>;

public
function checkUnits
  input output FlatModel flatModel;
protected
  Unit.CrefToUnitTable htCr2U1, htCr2U2;
  Unit.StringToUnitTable htS2U;
  Unit.UnitToStringTable htU2S;
  FunctionUnitCache fn_cache;
algorithm
  if not (Flags.getConfigBool(Flags.UNIT_CHECKING) or Flags.getConfigBool(Flags.CHECK_MODEL)) then
    return;
  end if;

  try
    htCr2U1 := Unit.newCrefUnitTable(Util.nextPrime(integer(10 + 1.4*listLength(flatModel.variables))));
    htS2U := Unit.getKnownUnits();
    htU2S := Unit.getKnownUnitsInverse();
    fn_cache := UnorderedMap.new<Functionargs>(stringHashDjb2, stringEq);

    for v in flatModel.variables loop
      convertUnitStringToUnit(v, htCr2U1, htS2U, htU2S);
    end for;

    htCr2U2 := UnorderedMap.copy(htCr2U1);
    htCr2U2 := checkModelConsistency(flatModel.variables, flatModel.equations,
      flatModel.initialEquations, htCr2U2, htS2U, htU2S, fn_cache);

    if Flags.isSet(Flags.DUMP_UNIT) then
      print(UnorderedMap.toString(htCr2U2, ComponentRef.toString, Unit.unit2string));
      print("\n######## UnitCheck COMPLETED ########\n");
    end if;

    notification(htCr2U1, htCr2U2, htU2S);

    flatModel := updateModel(flatModel, htCr2U2, htU2S);
  else
    Error.addInternalError(getInstanceName() + ": unit check module failed", sourceInfo());
  end try;

  execStat(getInstanceName());
end checkUnits;

protected
function updateModel
  "Updates all variables without units with their calculated units."
  input output FlatModel flatModel;
  input Unit.CrefToUnitTable htCr2U;
  input Unit.UnitToStringTable htU2S;
algorithm
  flatModel.variables := list(updateVariable(v, htCr2U, htU2S) for v in flatModel.variables);
end updateModel;

function updateVariable
  "Updates a variable without unit with its calculated unit."
  input output Variable var;
  input Unit.CrefToUnitTable htCr2U;
  input Unit.UnitToStringTable htU2S;
protected
  String name, unit_str;
  Binding binding;
  Integer unit_idx = 0;
  Unit.Unit unit;
algorithm
  if Type.isReal(var.ty) then
    for attr in var.typeAttributes loop
      (name, binding) := attr;
      unit_idx := unit_idx + 1;

      if name == "unit" then
        if Binding.isBound(binding) then
          // Variable already has a unit, keep it.
          return;
        else
          // Variable has an empty unit, replace it.
          var.typeAttributes := listDelete(var.typeAttributes, unit_idx);
          break;
        end if;
      end if;
    end for;

    try
      // Look up the variable's unit in the table.
      unit := UnorderedMap.getOrFail(var.name, htCr2U);

      if Unit.isUnit(unit) then
        // Add the unit string to the variable's type attributes.
        unit_str := Unit.unitString(unit, htU2S);
        binding := Binding.makeFlat(Expression.STRING(unit_str), Variability.CONSTANT, NFBinding.Source.GENERATED);
        var.typeAttributes := ("unit", binding) :: var.typeAttributes;
      end if;
    else
    end try;
  end if;
end updateVariable;

function notification "dumps the calculated units"
  input Unit.CrefToUnitTable inHtCr2U1;
  input Unit.CrefToUnitTable inHtCr2U2;
  input Unit.UnitToStringTable inHtU2S;
protected
  String str;
  list<tuple<ComponentRef, Unit.Unit>> lt1;
algorithm
  lt1 := UnorderedMap.toList(inHtCr2U1);
  str := notification2(lt1, inHtCr2U2, inHtU2S);
  if Flags.isSet(Flags.DUMP_UNIT) and str<>"" then
    Error.addCompilerNotification(str);
  end if;
end notification;

protected function notification2 "help-function"
  input list<tuple<ComponentRef, Unit.Unit>> inLt1;
  input Unit.CrefToUnitTable inHtCr2U2;
  input Unit.UnitToStringTable inHtU2S;
  output String outS;
protected
  ComponentRef cr1 = ComponentRef.EMPTY();
  Real factor1=0;
  Integer i1=0, i2=0, i3=0, i4=0, i5=0, i6=0, i7=0;
algorithm
  outS := stringAppendList(list(
  // We already assigned the variables before
  "\"" + ComponentRef.toString(cr1) + "\" has the Unit \"" + Unit.unitString(Unit.UNIT(factor1, i1, i2, i3, i4, i5, i6, i7), inHtU2S) + "\"\n"
  // Do the filtering and unboxing stuff at the same time; then we only need one hashtable call
  // And we only use a try-block for MASTER nodes
  for t1 guard match t1 local Boolean b; case (cr1,Unit.MASTER()) algorithm
    b := false;
    try
      Unit.UNIT(factor1, i1, i2, i3, i4, i5, i6, i7) :=
        UnorderedMap.getOrFail(ComponentRef.stripSubscripts(cr1), inHtCr2U2);
      b := true;
    else
    end try;
  then b; else false; end match in inLt1
  ));
end notification2;

function checkModelConsistency
  input list<Variable> variables;
  input list<Equation> equations;
  input list<Equation> initialEquations;
  input output Unit.CrefToUnitTable htCr2U;
  input Unit.StringToUnitTable htS2U;
  input Unit.UnitToStringTable htU2S;
  input FunctionUnitCache fnCache;
protected
  Boolean dump_eq_unit = Flags.isSet(Flags.DUMP_EQ_UNIT_STRUCT);
algorithm
  for v in variables loop
    foldBindingExp(v, htCr2U, htS2U, htU2S, fnCache, dump_eq_unit);

    for c in v.children loop
      foldBindingExp(c, htCr2U, htS2U, htU2S, fnCache, dump_eq_unit);
    end for;
  end for;

  for eq in equations loop
    foldEquation(eq, htCr2U, htS2U, htU2S, fnCache, dump_eq_unit);
  end for;

  for ieq in initialEquations loop
    foldEquation(ieq, htCr2U, htS2U, htU2S, fnCache, dump_eq_unit);
  end for;
end checkModelConsistency;

function foldBindingExp
  input Variable var;
  input Unit.CrefToUnitTable htCr2U;
  input Unit.StringToUnitTable htS2U;
  input Unit.UnitToStringTable htU2S;
  input FunctionUnitCache fnCache;
  input Boolean dumpEqInitStruct;
protected
  Expression binding_exp;
  Equation eq;
algorithm
  if Type.isReal(var.ty) and Binding.isBound(var.binding) then
    binding_exp := Binding.getTypedExp(var.binding);
    eq := Equation.makeEquality(Expression.fromCref(var.name), binding_exp, var.ty,
      InstNode.EMPTY_NODE(), ElementSource.createElementSource(var.info));
    foldEquation(eq, htCr2U, htS2U, htU2S, fnCache, dumpEqInitStruct);
  end if;
end foldBindingExp;

function foldEquation
  "Folds the equation or returns the error message of inconsistent equations."
  input Equation eq;
  input Unit.CrefToUnitTable htCr2U;
  input Unit.StringToUnitTable htS2U;
  input Unit.UnitToStringTable htU2S;
  input FunctionUnitCache fnCache;
  input Boolean dumpEqInitStruct;
protected
  list<list<tuple<Expression, Unit.Unit>>> inconsistent_units;
algorithm
  inconsistent_units := foldEquation2(eq, dumpEqInitStruct, htCr2U, htS2U, htU2S, fnCache);

  for u in inconsistent_units loop
    Errorfunction(u, eq, htU2S);
  end for;
end foldEquation;

function foldEquation2 "help function to foldEquation"
  input Equation eq;
  input Boolean dumpEqInitStruct;
  input Unit.CrefToUnitTable htCr2U;
  input Unit.StringToUnitTable htS2U;
  input Unit.UnitToStringTable htU2S;
  input FunctionUnitCache fnCache;
        output list<list<tuple<Expression, Unit.Unit>>> inconsistentUnits;
algorithm
  inconsistentUnits := match eq
    local
      list<list<tuple<Expression, Unit.Unit>>> icu1, icu2;
      Expression lhs, rhs, temp;
      String fn_name, formal_args, formal_var;
      list<String> out_vars, out_units;
      Unit.Unit unit1, unit2;
      list<Equation> eql;
      Boolean b;

    case Equation.EQUALITY(lhs = lhs as Expression.TUPLE(),
                           rhs = rhs as Expression.CALL())
      guard not Function.isBuiltin(Call.typedFunction(rhs.call))
      algorithm
        fn_name := AbsynUtil.pathString(AbsynUtil.makeNotFullyQualified(Call.functionName(rhs.call)));
        (_, out_vars, _, out_units) := getCallUnits(fn_name, rhs.call, fnCache);
        icu1 := foldCallArg1(lhs.elements, htCr2U, htS2U, htU2S, fnCache, Unit.MASTER({}), out_units, out_vars, fn_name);
        (_, icu2) := insertUnitInEquation(rhs, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
      then
        List.append_reverse(icu1, icu2);

    case Equation.EQUALITY(rhs = rhs as Expression.CALL())
      guard not Function.isBuiltin(Call.typedFunction(rhs.call))
      algorithm
        fn_name := AbsynUtil.pathString(AbsynUtil.makeNotFullyQualified(Call.functionName(rhs.call)));
        (_, out_vars, _, out_units) := getCallUnits(fn_name, rhs.call, fnCache);
        unit1 := insertUnitInEquation(eq.lhs, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
        formal_args := listHead(out_units);
        formal_var := listHead(out_vars);

        unit2 := if formal_args == "NONE" then Unit.MASTER({}) else Unit.parseUnitString(formal_args, htS2U, Equation.info(eq));

        b := unitTypesEqual(unit1, unit2, htCr2U);
        if b then
          icu1 := {};
        else
          icu1 := {{(eq.lhs, unit1), (makeNewCref(formal_var, fn_name), unit2)}};
        end if;

        (_, icu2) := insertUnitInEquation(rhs, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
      then
        List.append_reverse(icu1, icu2);

    case Equation.EQUALITY()
      algorithm
        temp := Expression.BINARY(eq.rhs, Operator.makeSub(Type.REAL()), eq.lhs);

        if dumpEqInitStruct then
          ExpressionDump.dumpExp(Expression.toDAE(temp));
        end if;

        (_, inconsistentUnits) := insertUnitInEquation(temp, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
      then
        inconsistentUnits;

    case Equation.ARRAY_EQUALITY()
      algorithm
        temp := Expression.BINARY(eq.rhs, Operator.makeSub(Type.REAL()), eq.lhs);

        if dumpEqInitStruct then
          ExpressionDump.dumpExp(Expression.toDAE(temp));
        end if;

        (_, inconsistentUnits) :=
          insertUnitInEquation(temp, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
      then
        inconsistentUnits;

    case Equation.WHEN(branches = Equation.Branch.BRANCH(body = eql) :: _)
      algorithm
        inconsistentUnits := {};

        for e in eql loop
          icu1 := foldEquation2(e, dumpEqInitStruct, htCr2U, htS2U, htU2S, fnCache);
          inconsistentUnits := List.append_reverse(icu1, inconsistentUnits);
        end for;
      then
        inconsistentUnits;

    case Equation.NORETCALL()
      algorithm
        (_, inconsistentUnits) := insertUnitInEquation(eq.exp, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
      then
        inconsistentUnits;

    else {};
  end match;
end foldEquation2;

function makeNewCref
  input String paramName;
  input String fnName;
  output Expression outExp;
algorithm
  outExp := Expression.CREF(Type.UNKNOWN(),
    ComponentRef.prefixCref(InstNode.NAME_NODE(paramName), Type.UNKNOWN(), {},
      ComponentRef.fromNode(InstNode.NAME_NODE(fnName + "()"), Type.UNKNOWN())));
end makeNewCref;

function insertUnitInEquation
  "Inserts the units in the equation and checks if the equation is consistent or not."
  input Expression eq;
  input output Unit.Unit unit;
  input Unit.CrefToUnitTable htCr2U;
  input Unit.StringToUnitTable htS2U;
  input Unit.UnitToStringTable htU2S;
  input FunctionUnitCache fnCache;
        output list<list<tuple<Expression, Unit.Unit>>> inconsistentUnits;
protected
  import NFOperator.Op;
algorithm
  (unit, inconsistentUnits) := matchcontinue eq
    local
      Expression exp1, exp2;
      Unit.Unit unit1, unit2, op_unit;
      list<list<tuple<Expression, Unit.Unit>>> icu1, icu2;
      list<ComponentRef> vars;
      Integer i;
      Boolean b;

    // SUB equal summands
    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.SUB), exp2)
      algorithm
        (unit2 as Unit.UNIT(), icu2) := insertUnitInEquation(exp2, unit, htCr2U, htS2U, htU2S, fnCache);
        (unit1, icu1) := insertUnitInEquation(exp1, unit2, htCr2U, htS2U, htU2S, fnCache);
        (true, op_unit) := unitTypesEqual(unit1, unit2, htCr2U);
      then
        (op_unit, List.append_reverse(icu1, icu2));

    // SUB equal summands
    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.SUB), exp2)
      algorithm
        (unit1, icu2) := insertUnitInEquation(exp1, unit, htCr2U, htS2U, htU2S, fnCache);
        (unit2, icu1) := insertUnitInEquation(exp2, unit1, htCr2U, htS2U, htU2S, fnCache);
        (true, op_unit) := unitTypesEqual(unit1, unit2, htCr2U);
      then
        (op_unit, List.append_reverse(icu1, icu2));

    // SUB unequal summands
    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.SUB), exp2)
      algorithm
        (unit2 as Unit.UNIT(), icu2) := insertUnitInEquation(exp2, unit, htCr2U, htS2U, htU2S, fnCache);
        (unit1, icu1) := insertUnitInEquation(exp1, unit2, htCr2U, htS2U, htU2S, fnCache);
        (false, _) := unitTypesEqual(unit1, unit2, htCr2U);
      then
        (Unit.MASTER({}), {(exp1, unit1), (exp2, unit2)} :: List.append_reverse(icu1, icu2));

    // SUB unequal summands
    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.SUB), exp2)
      algorithm
        (unit1, icu2) := insertUnitInEquation(exp1, unit, htCr2U, htS2U, htU2S, fnCache);
        (unit2, icu1) := insertUnitInEquation(exp2, unit1, htCr2U, htS2U, htU2S, fnCache);
        (false, _) := unitTypesEqual(unit1, unit2, htCr2U);
      then
        (Unit.MASTER({}), {(exp1, unit1), (exp2, unit2)} :: List.append_reverse(icu1, icu2));

    // ADD equal summands
    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.ADD), exp2)
      algorithm
        (unit2 as Unit.UNIT(), icu2) := insertUnitInEquation(exp2, unit, htCr2U, htS2U, htU2S, fnCache);
        (unit1, icu1) := insertUnitInEquation(exp1, unit2, htCr2U, htS2U, htU2S, fnCache);
        (true, op_unit) := unitTypesEqual(unit1, unit2, htCr2U);
      then
        (op_unit, List.append_reverse(icu1, icu2));

    // ADD equal summands
    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.ADD), exp2)
      algorithm
        (unit1, icu2) := insertUnitInEquation(exp1, unit, htCr2U, htS2U, htU2S, fnCache);
        (unit2, icu1) := insertUnitInEquation(exp2, unit1, htCr2U, htS2U, htU2S, fnCache);
        (true, op_unit) := unitTypesEqual(unit1, unit2, htCr2U);
      then
        (op_unit, List.append_reverse(icu1, icu2));

    // ADD unequal summands
    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.ADD), exp2)
      algorithm
        (unit2 as Unit.UNIT(), icu2) := insertUnitInEquation(exp2, unit, htCr2U, htS2U, htU2S, fnCache);
        (unit1, icu1) := insertUnitInEquation(exp1, unit2, htCr2U, htS2U, htU2S, fnCache);
        (false, _) := unitTypesEqual(unit1, unit2, htCr2U);
      then
        (Unit.MASTER({}), {(exp1, unit1), (exp2, unit2)} :: List.append_reverse(icu1, icu2));

    // ADD unequal summands
    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.ADD), exp2)
      algorithm
        (unit1, icu2) := insertUnitInEquation(exp1, unit, htCr2U, htS2U, htU2S, fnCache);
        (unit2, icu1) := insertUnitInEquation(exp2, unit1, htCr2U, htS2U, htU2S, fnCache);
        (false, _) := unitTypesEqual(unit1, unit2, htCr2U);
      then
        (Unit.MASTER({}), {(exp1, unit1), (exp2, unit2)} :: List.append_reverse(icu1, icu2));

    // MUL
    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.MUL), exp2)
      algorithm
        (unit1 as Unit.UNIT(), icu1) := insertUnitInEquation(exp1, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
        (unit2 as Unit.UNIT(), icu2) := insertUnitInEquation(exp2, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
        op_unit := Unit.unitMul(unit1, unit2);
        insertUnitString(op_unit, htS2U, htU2S);
      then
        (op_unit, List.append_reverse(icu1, icu2));

    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.MUL), exp2)
      guard Unit.isMaster(unit)
      algorithm
        (unit1 as Unit.MASTER(), icu1) := insertUnitInEquation(exp1, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
        (unit2 as Unit.UNIT(), icu2) := insertUnitInEquation(exp2, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
      then
        (Unit.MASTER({}), List.append_reverse(icu1, icu2));

    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.MUL), exp2)
      guard Unit.isUnit(unit)
      algorithm
        (Unit.MASTER(varList = vars), icu1) := insertUnitInEquation(exp1, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
        (unit2 as Unit.UNIT(), icu2) := insertUnitInEquation(exp2, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
        op_unit := Unit.unitDiv(unit, unit2);
        List.map2_0(vars, updateHtCr2U, op_unit, htCr2U);
        insertUnitString(op_unit, htS2U, htU2S);
      then
        (unit, List.append_reverse(icu1, icu2));

    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.MUL), exp2)
      guard Unit.isMaster(unit)
      algorithm
        (Unit.UNIT(), icu1) := insertUnitInEquation(exp1, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
        (Unit.MASTER(), icu2) := insertUnitInEquation(exp2, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
      then
        (Unit.MASTER({}), List.append_reverse(icu1, icu2));

    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.MUL), exp2)
      guard Unit.isUnit(unit)
      algorithm
        (unit2 as Unit.UNIT(), icu1) := insertUnitInEquation(exp1, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
        (Unit.MASTER(varList = vars), icu2) := insertUnitInEquation(exp2, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
        op_unit := Unit.unitDiv(unit, unit2);
        List.map2_0(vars, updateHtCr2U, op_unit, htCr2U);
        insertUnitString(op_unit, htS2U, htU2S);
      then
        (unit, List.append_reverse(icu1, icu2));

    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.MUL), exp2)
      algorithm
        (Unit.MASTER(), icu1) := insertUnitInEquation(exp1, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
        (Unit.MASTER(), icu2) := insertUnitInEquation(exp2, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
      then
        (Unit.MASTER({}), List.append_reverse(icu1, icu2));

    // DIV
    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.DIV), exp2)
      algorithm
        (unit1 as Unit.UNIT(), icu1) := insertUnitInEquation(exp1, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
        (unit2 as Unit.UNIT(), icu2) := insertUnitInEquation(exp2, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
        op_unit := Unit.unitDiv(unit1, unit2);
        insertUnitString(op_unit, htS2U, htU2S);
      then
        (op_unit, List.append_reverse(icu1, icu2));

    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.DIV), exp2)
      guard Unit.isMaster(unit)
      algorithm
        (Unit.MASTER(), icu1) := insertUnitInEquation(exp1, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
        (Unit.UNIT(), icu2) := insertUnitInEquation(exp2, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
        inconsistentUnits := List.append_reverse(icu1, icu2);
      then
        (Unit.MASTER({}), List.append_reverse(icu1, icu2));

    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.DIV), exp2)
      guard Unit.isUnit(unit)
      algorithm
        (Unit.MASTER(varList = vars), icu1) := insertUnitInEquation(exp1, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
        (unit2 as Unit.UNIT(), icu2) := insertUnitInEquation(exp2, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
        op_unit := Unit.unitMul(unit, unit2);
        List.map2_0(vars, updateHtCr2U, op_unit, htCr2U);
        insertUnitString(op_unit, htS2U, htU2S);
      then
        (unit, List.append_reverse(icu1, icu2));

    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.DIV), exp2)
      guard Unit.isMaster(unit)
      algorithm
        (Unit.UNIT(), icu1) := insertUnitInEquation(exp1, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
        (Unit.MASTER(), icu2) := insertUnitInEquation(exp2, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
      then
        (Unit.MASTER({}), List.append_reverse(icu1, icu2));

    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.DIV), exp2)
      guard Unit.isUnit(unit)
      algorithm
        (unit2 as Unit.UNIT(), icu1) := insertUnitInEquation(exp1, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
        (Unit.MASTER(varList = vars), icu2) := insertUnitInEquation(exp2, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
        op_unit := Unit.unitDiv(unit2, unit);
        List.map2_0(vars, updateHtCr2U, op_unit, htCr2U);
        insertUnitString(op_unit, htS2U, htU2S);
      then
        (unit, List.append_reverse(icu1, icu2));

    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.DIV), exp2)
      algorithm
        (Unit.MASTER(), icu1) := insertUnitInEquation(exp1, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
        (Unit.MASTER(), icu2) := insertUnitInEquation(exp2, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
      then
        (Unit.MASTER({}), List.append_reverse(icu1, icu2));

    // POW
    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.POW), exp2 as Expression.REAL())
      algorithm
        (unit1 as Unit.UNIT(), icu1) := insertUnitInEquation(exp1, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
        i := realInt(exp2.value);
        true := realEq(exp2.value, i);
        op_unit := Unit.unitPow(unit1, i);
        insertUnitString(op_unit, htS2U, htU2S);
      then
        (op_unit, icu1);

    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.POW), exp2 as Expression.REAL())
      guard Unit.isUnit(unit)
      algorithm
        (Unit.MASTER(varList = vars), icu1) := insertUnitInEquation(exp1, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
        op_unit := Unit.unitRoot(unit, exp2.value);
        List.map2_0(vars, updateHtCr2U, op_unit, htCr2U);
        insertUnitString(op_unit, htS2U, htU2S);
      then
        (unit, icu1);

    case Expression.BINARY(exp1, Operator.OPERATOR(op = Op.POW), Expression.REAL())
      algorithm
        (_, icu1) := insertUnitInEquation(exp1, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
      then
        (Unit.MASTER({}), icu1);

    // Call
    case Expression.CALL()
      algorithm
        (op_unit, icu1) := insertUnitInEquationCall(eq.call, unit, htCr2U, htS2U, htU2S, fnCache);
      then
        (op_unit, icu1);

    case Expression.IF()
      algorithm
        (unit1, icu1) := insertUnitInEquation(eq.trueBranch, unit, htCr2U, htS2U, htU2S, fnCache);
        (unit2, icu2) := insertUnitInEquation(eq.falseBranch, unit1, htCr2U, htS2U, htU2S, fnCache);
        (b, op_unit) := unitTypesEqual(unit1, unit2, htCr2U);
        inconsistentUnits := List.append_reverse(icu1, icu2);

        if not b then
          inconsistentUnits := {(eq.trueBranch, unit1), (eq.falseBranch, unit2)} :: inconsistentUnits;
          op_unit := Unit.MASTER({});
        end if;
      then
        (op_unit, inconsistentUnits);

    case Expression.RELATION()
      algorithm
        (unit1, icu1) := insertUnitInEquation(eq.exp1, unit, htCr2U, htS2U, htU2S, fnCache);
        (unit2, icu2) := insertUnitInEquation(eq.exp2, unit, htCr2U, htS2U, htU2S, fnCache);
        (b, op_unit) := unitTypesEqual(unit1, unit2, htCr2U);
        inconsistentUnits := List.append_reverse(icu1, icu2);

        if not b then
          inconsistentUnits := {(eq.exp1, unit1), (eq.exp2, unit2)} :: inconsistentUnits;
          op_unit := Unit.MASTER({});
        end if;
      then
        (op_unit, inconsistentUnits);

    case Expression.UNARY(operator = Operator.OPERATOR(op = Op.UMINUS))
      algorithm
        (op_unit, icu1) := insertUnitInEquation(eq.exp, unit, htCr2U, htS2U, htU2S, fnCache);
      then
        (op_unit, icu1);

    case Expression.CREF()
      guard ComponentRef.isTime(eq.cref)
      algorithm
        op_unit := Unit.UNIT(1e0, 0, 0, 0, 1, 0, 0, 0);
        addUnit2HtS2U("time", op_unit, htS2U);
        addUnit2HtU2S("time", op_unit, htU2S);
      then
        (op_unit, {});

    case Expression.CREF(ty = Type.REAL())
      then (UnorderedMap.getOrFail(ComponentRef.stripSubscripts(eq.cref), htCr2U), {});

    else (Unit.MASTER({}), {});
  end matchcontinue;
end insertUnitInEquation;

function insertUnitInEquationCall
  "Inserts the units in the equation and checks if the equation is consistent or not."
  input Call call;
  input output Unit.Unit unit;
  input Unit.CrefToUnitTable htCr2U;
  input Unit.StringToUnitTable htS2U;
  input Unit.UnitToStringTable htU2S;
  input FunctionUnitCache fnCache;
        output list<list<tuple<Expression, Unit.Unit>>> inconsistentUnits;
protected
  Absyn.Path fn_path;
  String fn_name;
  list<Expression> call_args;
  Unit.Unit op_unit;
  list<ComponentRef> vars;
  list<String> var_names, unit_names;
algorithm
  fn_path := Call.functionName(call);
  call_args := Call.arguments(call);

  (unit, inconsistentUnits) := matchcontinue fn_path
    case Absyn.IDENT("pre")
      algorithm
        (op_unit, inconsistentUnits) :=
          insertUnitInEquation(listHead(call_args), unit, htCr2U, htS2U, htU2S, fnCache);
      then
        (Unit.MASTER({}), inconsistentUnits);

    case Absyn.IDENT("der")
      algorithm
        (op_unit, inconsistentUnits) :=
          insertUnitInEquation(listHead(call_args), Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);

        if Unit.isUnit(op_unit) then
          op_unit := Unit.unitDiv(op_unit, Unit.UNIT(1e0, 0, 0, 0, 1, 0, 0, 0));
          insertUnitString(op_unit, htS2U, htU2S);
        elseif Unit.isUnit(unit) then
          Unit.MASTER(varList = vars) := op_unit;
          op_unit := Unit.unitMul(unit, Unit.UNIT(1e0, 0, 0, 0, 1, 0, 0, 0));
          List.map2_0(vars, updateHtCr2U, op_unit, htCr2U);
          insertUnitString(op_unit, htS2U, htU2S);
        else
          op_unit := Unit.MASTER({});
        end if;
      then
        (op_unit, inconsistentUnits);

    case Absyn.IDENT("sqrt")
      algorithm
        (op_unit, inconsistentUnits) :=
          insertUnitInEquation(listHead(call_args), Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);

        if Unit.isUnit(op_unit) then
          op_unit := Unit.unitRoot(op_unit, 2.0);
          insertUnitString(op_unit, htS2U, htU2S);
        elseif Unit.isUnit(unit) then
          Unit.MASTER(varList = vars) := op_unit;
          op_unit := Unit.unitPow(unit, 2);
          List.map2_0(vars, updateHtCr2U, op_unit, htCr2U);
          insertUnitString(op_unit, htS2U, htU2S);
          op_unit := unit;
        else
          op_unit := Unit.MASTER({});
        end if;
      then
        (op_unit, inconsistentUnits);

    case Absyn.IDENT()
      guard Function.isBuiltin(Call.typedFunction(call))
      algorithm
        inconsistentUnits := foldCallArg(call_args, htCr2U, htS2U, htU2S, fnCache);
      then
        (Unit.MASTER({}), inconsistentUnits);

    case _
      algorithm
        fn_name := AbsynUtil.pathString(AbsynUtil.makeNotFullyQualified(fn_path));
        (var_names, _, unit_names) := getCallUnits(fn_name, call, fnCache);
        inconsistentUnits := foldCallArg1(call_args, htCr2U, htS2U, htU2S, fnCache, unit, unit_names, var_names, fn_name);
      then
        (Unit.MASTER({}), inconsistentUnits);

    else (Unit.MASTER({}), {});
  end matchcontinue;
end insertUnitInEquationCall;

function insertUnitString
  input Unit.Unit unit;
  input Unit.StringToUnitTable htS2U;
  input Unit.UnitToStringTable htU2S;
protected
  String unit_str;
algorithm
  unit_str := Unit.unitString(unit, htU2S);
  addUnit2HtS2U(unit_str, unit, htS2U);
  addUnit2HtU2S(unit_str, unit, htU2S);
end insertUnitString;

function getCallUnits
  input String fnName;
  input Call call;
  input FunctionUnitCache fnCache;
  output list<String> inputVars;
  output list<String> outputVars;
  output list<String> inputUnits;
  output list<String> outputUnits;
protected
  Option<Functionargs> opt_args;
  Functionargs args;
algorithm
  opt_args := UnorderedMap.get(fnName, fnCache);

  if isSome(opt_args) then
    SOME(args) := opt_args;
  else
    args := parseFunctionUnits(fnName, Call.typedFunction(call));
    UnorderedMap.addUnique(fnName, args, fnCache);
  end if;

  Functionargs.FUNCTIONUNITS(_, inputVars, outputVars, inputUnits, outputUnits) := args;
end getCallUnits;

function parseFunctionUnits
  input String funcName;
  input Function func;
  output Functionargs outArgs;
protected
  String fn_name;
  list<String> in_units, out_units, in_args, out_args;
algorithm
  in_units := list(Component.getUnitAttribute(InstNode.component(p), "NONE") for p in func.inputs);
  out_units := list(Component.getUnitAttribute(InstNode.component(p), "NONE") for p in func.outputs);
  in_args := list(InstNode.name(p) for p in func.inputs);
  out_args := list(InstNode.name(p) for p in func.outputs);
  outArgs := FUNCTIONUNITS(funcName, in_args, out_args, in_units, out_units);
end parseFunctionUnits;

function unitTypesEqual
  "Checks equality of two units."
  input Unit.Unit unit1;
  input Unit.Unit unit2;
  input Unit.CrefToUnitTable htCr2U;
  output Boolean isEqual;
  output Unit.Unit outUnit;
algorithm
  (isEqual, outUnit) := match (unit1, unit2)
    local
      Real r;
      list<ComponentRef> vars1, vars2;
      String s1, s2;

    case (Unit.UNIT(), Unit.UNIT())
      algorithm
        isEqual := realEq(unit1.factor, unit2.factor);

        if not isEqual then
          r := realMax(realAbs(unit1.factor), realAbs(unit2.factor));
          isEqual := realLe(realDiv(realAbs(realSub(unit1.factor, unit2.factor)), r), 1e-3);
        end if;

        isEqual := isEqual and
                   unit1.mol == unit2.mol and
                   unit1.cd  == unit2.cd  and
                   unit1.m   == unit2.m   and
                   unit1.s   == unit2.s   and
                   unit1.A   == unit2.A   and
                   unit1.K   == unit2.K   and
                   unit1.g   == unit2.g;
      then
        (isEqual, unit1);

    case (Unit.UNIT(), Unit.MASTER(varList = vars2))
      algorithm
        List.map2_0(vars2, updateHtCr2U, unit1, htCr2U);
      then
        (true, unit1);

    case (Unit.MASTER(varList = vars1), Unit.UNIT())
      algorithm
        List.map2_0(vars1, updateHtCr2U, unit2, htCr2U);
      then
        (true, unit2);

    case (Unit.MASTER(varList = vars1), Unit.MASTER(varList = vars2))
      algorithm
        vars2 := List.append_reverse(vars1, vars2);
      then
        (true, Unit.MASTER(vars2));

    case (Unit.UNKNOWN(unit = s1), Unit.UNKNOWN(unit = s2))
      then (s1 == s2, unit1);

    case (Unit.UNKNOWN(), _) then (true, unit1);
    case (_, Unit.UNKNOWN()) then (true, unit2);
    else (false, unit1);
  end match;
end unitTypesEqual;

function updateHtCr2U
  input ComponentRef cref;
  input Unit.Unit unit;
  input Unit.CrefToUnitTable htCr2U;
algorithm
  UnorderedMap.tryAdd(NFUnit.UPDATECREF, Unit.MASTER({}), htCr2U);
  UnorderedMap.add(cref, unit, htCr2U);
end updateHtCr2U;

protected function Errorfunction "returns the inconsistent Equation with sub-expression"
  input list<tuple<Expression, Unit.Unit>> inexpList;
  input Equation inEq;
  input Unit.UnitToStringTable inHtU2S;
algorithm
  _ := match(inexpList, inEq, inHtU2S)
    local
      String s, s1, s2, s3, s4;
      list<tuple<Expression, Unit.Unit>> expList;
      Expression exp1, exp2;
      Integer i;
      SourceInfo info;
    case (expList, _, _)
      equation
        info=Equation.info(inEq);
        s = Equation.toString(inEq);
        s1 = Errorfunction2(expList, inHtU2S);
        s2="The following equation is INCONSISTENT due to specified unit information: " + s +"\n";
        Error.addSourceMessage(Error.COMPILER_WARNING,{s2},info);
        Error.addCompilerWarning("The units of following sub-expressions need to be equal:\n" + s1);

        /*
        Error.addCompilerWarning("The following NEWFRONTEND UNIT CHECK equation is INCONSISTENT due to specified unit information: " + s + "\n" +
          "The units of following sub-expressions need to be equal:\n" + s1 );*/
      then ();
  end match;
end Errorfunction;

protected function Errorfunction2 "help-function"
  input list<tuple<Expression, Unit.Unit>> inexpList;
  input Unit.UnitToStringTable inHtU2S;
  output String outS;
algorithm
  outS := match(inexpList, inHtU2S)
    local
      list<tuple<Expression, Unit.Unit>> expList;
      Expression exp;
      Unit.Unit ut;
      String s, s1, s2;

    case ((exp, ut)::{}, _) equation
      s = Expression.toString(exp);
      s1 = Unit.unitString(ut, inHtU2S);
      s = "- sub-expression \"" + s + "\" has unit \"" + s1 + "\"";
    then s;

    case ((exp, ut)::expList, _) equation
      s = Expression.toString(exp);
      s1 = Unit.unitString(ut, inHtU2S);
      s2 = Errorfunction2(expList, inHtU2S);
      s = "- sub-expression \"" + s + "\" has unit \"" + s1 + "\"\n" + s2;
    then s;
  end match;
end Errorfunction2;


protected function foldCallArg "help-function for CALL case in function insertUnitInEquation"
  input list<Expression> args;
  input Unit.CrefToUnitTable htCr2U;
  input Unit.StringToUnitTable htS2U;
  input Unit.UnitToStringTable htU2S;
  input FunctionUnitCache fnCache;
  output list<list<tuple<Expression, Unit.Unit>>> inconsistentUnits = {};
protected
  list<list<tuple<Expression, Unit.Unit>>> icu;
algorithm
  for exp in args loop
    (_, icu) :=
      insertUnitInEquation(exp, Unit.MASTER({}), htCr2U, htS2U, htU2S, fnCache);
    inconsistentUnits := List.append_reverse(icu, inconsistentUnits);
  end for;

  inconsistentUnits := listReverse(inconsistentUnits);
end foldCallArg;

function foldCallArg1
  "Help function for CALL case in userdefinde top level function insertUnitInEquation"
  input list<Expression> args;
  input Unit.CrefToUnitTable htCr2U;
  input Unit.StringToUnitTable htS2U;
  input Unit.UnitToStringTable htU2S;
  input FunctionUnitCache fnCache;
  input Unit.Unit inUnit;
  input list<String> units;
  input list<String> vars;
  input String fnName;
  output list<list<tuple<Expression, Unit.Unit>>> inconsistentUnits = {};
protected
  String unit, var;
  list<String> rest_units = units, rest_vars = vars;
  Unit.Unit op_unit, op_unit2;
  list<list<tuple<Expression, Unit.Unit>>> icu;
  Expression temp;
  Boolean b;
algorithm
  for arg in args loop
    var :: rest_vars := rest_vars;
    unit :: rest_units := rest_units;

    (op_unit, icu) := insertUnitInEquation(arg, inUnit, htCr2U, htS2U, htU2S, fnCache);

    if unit == "NONE" then
      op_unit2 := Unit.MASTER({});
    else
      op_unit2 := Unit.parseUnitString(unit, htS2U);
    end if;

    (b, op_unit) := unitTypesEqual(op_unit, op_unit2, htCr2U);

    if b then
      icu := {};
    else
      temp := makeNewCref(var, fnName);
      icu := {{(arg, op_unit), (temp, op_unit2)}};
    end if;

    inconsistentUnits := List.append_reverse(icu, inconsistentUnits);
  end for;
end foldCallArg1;

protected function addUnit2HtS2U
  input String name;
  input Unit.Unit unit;
  input Unit.StringToUnitTable inHtS2U;
algorithm
  UnorderedMap.add(name, unit, inHtS2U);
end addUnit2HtS2U;

protected function addUnit2HtU2S
  input String name;
  input Unit.Unit unit;
  input Unit.UnitToStringTable htU2S;
algorithm
  UnorderedMap.tryAdd(unit, name, htU2S);
end addUnit2HtU2S;

function convertUnitStringToUnit
  "converts String to unit"
  input Variable var;
  input Unit.CrefToUnitTable htCr2U;
  input Unit.StringToUnitTable htS2U;
  input Unit.UnitToStringTable htU2S;
protected
  Binding unit_binding;
  Option<Expression> unit_exp;
  String unit_string;
  Unit.Unit unit;
algorithm
  unit_binding := Variable.lookupTypeAttribute("unit", var);
  unit_exp := Binding.typedExp(unit_binding);
  unit_string := if isSome(unit_exp) then getUnitStringFromExp(Util.getOption(unit_exp)) else "";

  if stringEmpty(unit_string) then
    UnorderedMap.add(var.name, Unit.MASTER({var.name}), htCr2U);
    addUnit2HtS2U("-", Unit.MASTER({var.name}), htS2U);
    addUnit2HtU2S("-", Unit.MASTER({var.name}), htU2S);
  else
    unit := parse(unit_string, var.name, htS2U, htU2S, var.info);
    UnorderedMap.add(var.name, unit, htCr2U);
  end if;
end convertUnitStringToUnit;

function getUnitStringFromExp
  input Expression unitExp;
  output String unitString;
protected
  Expression exp;
algorithm
  unitString := match unitExp
    // A literal string expression, return the string.
    case Expression.STRING() then unitExp.value;

    // A literal array. This happens for array variables, assume each variable
    // has the same unit for now.
    case Expression.ARRAY(literal = true)
      guard Expression.isLiteral(unitExp) and not Type.isEmptyArray(Expression.typeOf(unitExp))
      then getUnitStringFromExp(Expression.arrayFirstScalar(unitExp));

    // A fill call. Will generate an array where all elements are the same, so
    // no need to evaluate it.
    case Expression.CALL(Call.TYPED_CALL(arguments = exp :: _))
      guard Call.isNamed(unitExp.call, "fill")
      then getUnitStringFromExp(exp);

    // A non-literal expression, evaluate it and try again if it could be evaluated.
    case _
      guard not Expression.isLiteral(unitExp)
      algorithm
        exp := Ceval.tryEvalExp(unitExp);
      then
        if Expression.isLiteral(exp) then getUnitStringFromExp(exp) else "";

    else "";
  end match;
end getUnitStringFromExp;

protected function parse "author: lochel"
  input String unitString;
  input ComponentRef cref;
  input Unit.StringToUnitTable htS2U;
  input Unit.UnitToStringTable htU2S;
  input SourceInfo info;
  output Unit.Unit unit;
algorithm
  if stringEmpty(unitString) then
    unit := Unit.MASTER({cref});
    return;
  end if;
  try
    unit := UnorderedMap.getOrFail(unitString, htS2U);
  else
    try
      unit := Unit.parseUnitString(unitString, htS2U, info);
    else
      unit := Unit.UNKNOWN(unitString);
    end try;
    addUnit2HtS2U(unitString, unit, htS2U);
    addUnit2HtU2S(unitString, unit, htU2S);
  end try;
end parse;

annotation(__OpenModelica_Interface="frontend");
end NFUnitCheck;
