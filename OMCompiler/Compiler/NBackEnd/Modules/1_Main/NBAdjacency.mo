/*
* This file is part of OpenModelica.
*
* Copyright (c) 1998-2020, Open Source Modelica Consortium (OSMC),
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
encapsulated package NBAdjacency
"file:        NBAdjacency.mo
 package:     NBAdjacency
 description: This file contains the functions which will create adjacency matrices.
"
public
  // self import
  import Adjacency = NBAdjacency;

protected
  // NF imports
  import ComponentRef = NFComponentRef;
  import FunctionTree = NFFlatten.FunctionTree;
  import Variable = NFVariable;

  // NB imports
  import Differentiate = NBDifferentiate;
  import BEquation = NBEquation;
  import NBEquation.Equation;
  import NBEquation.EquationAttributes;
  import NBEquation.EquationPointers;
  import BVariable = NBVariable;
  import NBVariable.VariablePointers;

  // Util import
  import BuiltinSystem = System;

  // SetBased Graph imports
  import SBGraph.BipartiteIncidenceList;
  import SBGraph.VertexDescriptor;
  import SBGraph.SetType;
  import SBInterval;
  import SBMultiInterval;
  import SBPWLinearMap;
  import SBSet;
  import NBGraphUtil.{SetVertex, SetEdge};

public
  type MatrixType        = enumeration(SCALAR, ARRAY);
  type MatrixStrictness  = enumeration(FULL, LINEAR, STATE_SELECT, INIT);
  type BipartiteGraph             = BipartiteIncidenceList<SetVertex, SetEdge>;

  uniontype Matrix
    record ARRAY_ADJACENCY_MATRIX
      "no transposed set matrix needed since the graph represents all vertices equally"
      BipartiteGraph graph                        "set based graph";
      UnorderedMap<SetVertex, Integer> vertexMap  "map to get the vertex index";
      UnorderedMap<SetEdge, Integer> edgeMap      "map to get the edge index";
      MatrixStrictness st;
      /* Maybe add optional markings here */
    end ARRAY_ADJACENCY_MATRIX;

    record SCALAR_ADJACENCY_MATRIX
      array<list<Integer>> m        "eqn -> list<var>";
      array<list<Integer>> mT       "var -> list<eqn>";
      MatrixStrictness st;
    end SCALAR_ADJACENCY_MATRIX;

    record EMPTY_ADJACENCY_MATRIX
    end EMPTY_ADJACENCY_MATRIX;

    function create
      input VariablePointers vars;
      input EquationPointers eqs;
      input MatrixType ty;
      input MatrixStrictness st = MatrixStrictness.FULL;
      output Matrix adj;
      input output Option<FunctionTree> funcTree = NONE() "only needed for LINEAR without existing derivatives";
    algorithm
      (adj, funcTree) := match ty
        case MatrixType.SCALAR then createScalar(vars, eqs, st, funcTree);
        case MatrixType.ARRAY  then createArray(vars, eqs, st, funcTree);
        else algorithm
          Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed because of unknown adjacency matrix type."});
        then fail();
      end match;
    end create;

    function update
      "Updates specified rows of the adjacency matrix.
      Updates everything by default and if the index
      list is equal to {-1}."
      input output Matrix adj;
      input VariablePointers vars;
      input EquationPointers eqs;
      input list<Integer> idx_lst = {-1};
      input output Option<FunctionTree> funcTree = NONE() "only needed for LINEAR without existing derivatives";
    algorithm
      (adj, funcTree) := match (adj, idx_lst)
        local
          array<list<Integer>> m, mT;
        case (SCALAR_ADJACENCY_MATRIX(), {-1})  then create(vars, eqs, MatrixType.SCALAR, adj.st);
        case (ARRAY_ADJACENCY_MATRIX(), {-1})   then create(vars, eqs, MatrixType.ARRAY, adj.st);

        case (SCALAR_ADJACENCY_MATRIX(m = m, mT = mT), _) algorithm
          (m, mT) := updateScalar(m, mT, adj.st, vars, eqs, idx_lst, funcTree);
          adj.m := m;
          adj.mT := mT;
        then (adj, funcTree);

        case (ARRAY_ADJACENCY_MATRIX(), _) algorithm
          // ToDo
        then (adj, funcTree);

        else algorithm
          Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed because of unknown adjacency matrix type."});
        then fail();
      end match;
    end update;

    function toString
      input Matrix adj;
      input output String str = "";
    algorithm
      str := StringUtil.headline_2(str + "AdjacencyMatrix") + "\n";
      str := match adj
        case ARRAY_ADJACENCY_MATRIX() then str + "\n ARRAY NOT YET SUPPORTED \n";
        case SCALAR_ADJACENCY_MATRIX() algorithm
          if arrayLength(adj.m) > 0 then
            str := str + StringUtil.headline_4("Normal Adjacency Matrix (row = equation)");
            str := str + toStringSingle(adj.m);
          end if;
          str := str + "\n";
          if arrayLength(adj.mT) > 0 then
            str := str + StringUtil.headline_4("Transposed Adjacency Matrix (row = variable)");
            str := str + toStringSingle(adj.mT);
          end if;
          str := str + "\n";
        then str;
        case EMPTY_ADJACENCY_MATRIX() then str + StringUtil.headline_4("Empty Adjacency Matrix") + "\n";
        else algorithm
          Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed because of unknown adjacency matrix type."});
        then fail();
      end match;
    end toString;

  protected
    function toStringSingle
      input array<list<Integer>> m;
      output String str = "";
    algorithm
      for row in 1:arrayLength(m) loop
        str := str + "\t(" + intString(row) + ")\t" + List.toString(m[row], intString) + "\n";
      end for;
    end toStringSingle;

    function createScalar
      input VariablePointers vars;
      input EquationPointers eqs;
      input MatrixStrictness st = MatrixStrictness.FULL;
      output Matrix adj;
      input output Option<FunctionTree> funcTree = NONE() "only needed for LINEAR without existing derivatives";
    protected
      Pointer<Differentiate.DifferentiationArguments> diffArgs_ptr;
      Differentiate.DifferentiationArguments diffArgs;
      list<Pointer<BEquation.Equation>> eqn_lst;
      array<list<Integer>> m, mT;
      Integer eqn_idx = 1;
    algorithm
      if ExpandableArray.getNumberOfElements(vars.varArr) > 0 or ExpandableArray.getNumberOfElements(eqs.eqArr) > 0 then
        if Util.isSome(funcTree) then
          diffArgs_ptr := Pointer.create(Differentiate.DifferentiationArguments.default(NBDifferentiate.DifferentiationType.TIME, Util.getOption(funcTree)));
        end if;

        eqn_lst := EquationPointers.toList(eqs);
        // create empty adjacency matrix and traverse equations to fill it
        m := arrayCreate(listLength(eqn_lst), {});
        for eqn_ptr in eqn_lst loop
          (m, eqn_idx) := createScalarRow(eqn_ptr, diffArgs_ptr, st, vars, m, eqn_idx, funcTree);
        end for;

        // also sorts the matrix
        mT := transposeScalar(m, ExpandableArray.getLastUsedIndex(vars.varArr));

        // after proper sorting fixup the indices for STATE_SELECT and INIT
        if st > MatrixStrictness.LINEAR then
          m := absoluteMatrix(m);
          mT := absoluteMatrix(mT);
        end if;
        if Util.isSome(funcTree) then
          diffArgs := Pointer.access(diffArgs_ptr);
          funcTree := SOME(diffArgs.funcTree);
        end if;

        adj := SCALAR_ADJACENCY_MATRIX(m, mT, st);
      else
        adj := EMPTY_ADJACENCY_MATRIX();
      end if;
    end createScalar;

    function updateScalar
      input output array<list<Integer>> m;
      input output array<list<Integer>> mT;
      input MatrixStrictness st;
      input VariablePointers vars;
      input EquationPointers eqns;
      input list<Integer> idx_lst;
      input output Option<FunctionTree> funcTree = NONE() "only needed for LINEAR without existing derivatives";
    protected
      Pointer<Differentiate.DifferentiationArguments> diffArgs_ptr;
      Differentiate.DifferentiationArguments diffArgs;
    algorithm
      if Util.isSome(funcTree) then
        diffArgs_ptr := Pointer.create(Differentiate.DifferentiationArguments.default(NBDifferentiate.DifferentiationType.TIME, Util.getOption(funcTree)));
      end if;

      for i in idx_lst loop
        (m, _) := createScalarRow(EquationPointers.getEqnAt(eqns, i), diffArgs_ptr, st, vars, m, i, funcTree);
      end for;

      // also sorts the matrix
      mT := transposeScalar(m, ExpandableArray.getLastUsedIndex(vars.varArr));

      // after proper sorting fixup the indices for STATE_SELECT and INIT
      if st > MatrixStrictness.LINEAR then
        m := absoluteMatrix(m);
        mT := absoluteMatrix(mT);
      end if;
      if Util.isSome(funcTree) then
        diffArgs := Pointer.access(diffArgs_ptr);
        funcTree := SOME(diffArgs.funcTree);
      end if;
    end updateScalar;

    function createScalarRow
      input Pointer<Equation> eqn_ptr;
      input Pointer<Differentiate.DifferentiationArguments> diffArgs_ptr;
      input MatrixStrictness st;
      input VariablePointers vars;
      input output array<list<Integer>> m;
      input output Integer eqn_idx;
      input Option<FunctionTree> funcTree = NONE() "only needed for LINEAR without existing derivatives";
    protected
      Equation eqn;
      list<ComponentRef> dependencies, state_dependencies, nonlinear_dependencies;
      BEquation.EquationAttributes attr;
      Pointer<Equation> derivative;
    algorithm
      eqn := Pointer.access(eqn_ptr);
      dependencies := BEquation.Equation.collectCrefs(eqn, function getDependentCref(map = vars.map));

        // INIT
      if (st == MatrixStrictness.INIT) then
        // for initialization all regular rules apply but states have to be
        // sorted to be at the end
        (state_dependencies, dependencies) := List.extractOnTrue(dependencies, function BVariable.checkCref(func = BVariable.isState));
        m[eqn_idx] := getDependentCrefIndices(state_dependencies, vars.map, true);

      // LINEAR and STATE SELECT
      elseif (st > MatrixStrictness.FULL) then
        attr := Equation.getAttributes(eqn);
        if Util.isSome(attr.derivative) then
          derivative := Util.getOption(attr.derivative);
        elseif Util.isSome(funcTree) then
          derivative := Differentiate.differentiateEquationPointer(eqn_ptr, diffArgs_ptr);
        else
          Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed because no derivative is saved and no function tree is given for linear adjacency matrix!"});
        end if;
        // if we only want linear dependencies, try to look if there is a derivative saved. remove all dependencies
        // of that equation because those are the nonlinear ones.
        // for now fail if there is no derivative, possible fallback: differentiate eq and save it
        nonlinear_dependencies := BEquation.Equation.collectCrefs(Pointer.access(derivative), function getDependentCref(map = vars.map));
        dependencies := List.setDifferenceOnTrue(dependencies, nonlinear_dependencies, ComponentRef.isEqual);
        if st == MatrixStrictness.STATE_SELECT then
          // if we are preparing for state selection we only search for linear occurences. One exception
          // are StateSelect.NEVER variables, which are allowed to appear nonlinear. but they have to be
          // the last checked option, so they have a negative index and are afterwards sorted to be at the end
          // of the list.
            (nonlinear_dependencies, _) := List.extractOnTrue(nonlinear_dependencies, function BVariable.checkCref(func = function BVariable.isStateSelect(stateSelect = NFBackendExtension.StateSelect.NEVER)));
            m[eqn_idx] := getDependentCrefIndices(nonlinear_dependencies, vars.map, true);
        end if;
      end if;

      // create the actual matrix row. Append because STATE_SELECT and INIT
      // have already added certain variables with negative index
      m[eqn_idx] := listAppend(getDependentCrefIndices(dependencies, vars.map), m[eqn_idx]);
      eqn_idx := eqn_idx + 1;
    end createScalarRow;

    function transposeScalar
      input array<list<Integer>> m      "original matrix";
      input Integer size                "size of the transposed matrix (does not have to be square!)";
      output array<list<Integer>> mT    "transposed matrix";
    algorithm
      mT := arrayCreate(size, {});
      // loop over all elements and store them in reverse
      for row in 1:arrayLength(m) loop
        for idx in m[row] loop
          try
            if idx > 0 then
              mT[idx] := row :: mT[idx];
            else
              mT[intAbs(idx)] := -row :: mT[intAbs(idx)];
            end if;
          else
            Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed for variable index " + intString(idx) + ".
              The variables have to be dense (without empty spaces) for this to work!"});
          end try;
        end for;
      end for;
      // sort the transposed matrix
      // bigger to lower such that negative entries are at the and
      for row in 1:arrayLength(mT) loop
        mT[row] := List.sort(mT[row], intLt);
      end for;
    end transposeScalar;

    function absoluteMatrix
      input output array<list<Integer>> m;
    algorithm
      for row in 1:arrayLength(m) loop
        m[row] := list(intAbs(i) for i in m[row]);
      end for;
    end absoluteMatrix;

    function createArray
      input VariablePointers vars;
      input EquationPointers eqs;
      input MatrixStrictness st = MatrixStrictness.FULL;
      output Matrix adj;
      input output Option<FunctionTree> funcTree = NONE() "only needed for LINEAR without existing derivatives";
    protected
      BipartiteIncidenceList<SetVertex, SetEdge> graph;
      Pointer<Integer> max_dim = Pointer.create(1);
      Vector<Integer> vCount, eCount;
      UnorderedMap<SetVertex, Integer> vertexMap;
      UnorderedMap<SetEdge, Integer> edgeMap;
    algorithm
      // reset unique tick index to 0
      BuiltinSystem.tmpTickReset(0);

      // create empty set based graph and map
      graph := BipartiteIncidenceList.new(SetVertex.isEqual, SetEdge.isEqual, SetVertex.toString, SetEdge.toString);
      vertexMap := UnorderedMap.new<Integer>(SetVertex.hash, SetVertex.isEqual, VariablePointers.size(vars) + EquationPointers.size(eqs));
      edgeMap := UnorderedMap.new<Integer>(SetEdge.hash, SetEdge.isEqual, VariablePointers.size(vars) + EquationPointers.size(eqs)); // make better size approx here

      // find maximum number of dimensions
      VariablePointers.mapPtr(vars, function maxDimTraverse(max_dim = max_dim));
      EquationPointers.mapRes(eqs, function maxDimTraverse(max_dim = max_dim)); // maybe unnecessary?
      vCount := Vector.newFill(Pointer.access(max_dim), 1);
      eCount := Vector.newFill(Pointer.access(max_dim), 1);

      // create vertices for variables
      VariablePointers.mapPtr(vars, function SetVertex.createTraverse(graph = graph, vCount = vCount, ST = SetType.U, vertexMap = vertexMap));

      // create vertices for equations and create edges
      EquationPointers.map(eqs, function SetEdge.fromEquation(
        graph       = graph,
        vCount      = vCount,
        eCount      = eCount,
        map         = vars.map,
        vertexMap   = vertexMap,
        edgeMap     = edgeMap,
        eqn_tpl_opt = NONE()
      ));

      if Flags.isSet(Flags.DUMP_SET_BASED_GRAPHS) then
        print(BipartiteIncidenceList.toString(graph));
      end if;

      adj := ARRAY_ADJACENCY_MATRIX(graph, vertexMap, edgeMap, st);
    end createArray;

    function maxDimTraverse
      input Pointer<Variable> var_ptr;
      input Pointer<Integer> max_dim;
    protected
      Integer dim_size;
    algorithm
      dim_size := listLength(BVariable.getDimensions(var_ptr));
      if Pointer.access(max_dim) < dim_size then
        Pointer.update(max_dim, dim_size);
      end if;
    end maxDimTraverse;

    function getDependentCref
      input output ComponentRef cref                "the cref to check";
      input Pointer<list<ComponentRef>> acc         "accumulator for relevant crefs";
      input UnorderedMap<ComponentRef, Integer> map "unordered map to check for relevance";
    algorithm
      if UnorderedMap.contains(cref, map) then
        Pointer.update(acc, cref :: Pointer.access(acc));
      end if;
    end getDependentCref;

    function getDependentCrefIndices
      input list<ComponentRef> dependencies         "dependent var crefs";
      input UnorderedMap<ComponentRef, Integer> map "hash table to check for relevance";
      input Boolean negate = false;
      output list<Integer> indices = {};
    algorithm
      if negate then
        for cref in dependencies loop
          indices := -UnorderedMap.getSafe(cref, map) :: indices;
        end for;
      else
        for cref in dependencies loop
          indices := UnorderedMap.getSafe(cref, map) :: indices;
        end for;
      end if;
      // remove duplicates and sort
      indices := List.sort(List.unique(indices), intLt);
    end getDependentCrefIndices;
  end Matrix;

  annotation(__OpenModelica_Interface="backend");
end NBAdjacency;
