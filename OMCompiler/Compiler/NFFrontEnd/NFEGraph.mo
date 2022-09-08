/*
 * This file is part of OpenModelica.
 *
 * Copyright (c) 1998-2022, Linköping University,
 * Department of Computer and Information Science,
 * SE-58183 Linköping, Sweden.
 *
 * All rights reserved.
 *
 * THIS PROGRAM IS PROVIDED UNDER THE TERMS OF GPL VERSION 3
 * AND THIS OSMC PUBLIC LICENSE (OSMC-PL).
 * ANY USE, REPRODUCTION OR DISTRIBUTION OF THIS PROGRAM CONSTITUTES RECIPIENT'S
 * ACCEPTANCE OF THE OSMC PUBLIC LICENSE.
 *
 * The OpenModelica software and the Open Source Modelica
 * Consortium (OSMC) Public License (OSMC-PL) are obtained
 * from Linköping University, either from the above address,
 * from the URLs: http://www.ida.liu.se/projects/OpenModelica or
 * http://www.openmodelica.org, and in the OpenModelica distribution.
 * GNU version 3 is obtained from: http://www.gnu.org/copyleft/gpl.html.
 *
 * This program is distributed WITHOUT ANY WARRANTY; without
 * even the implied warranty of  MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE, EXCEPT AS EXPRESSLY SET FORTH
 * IN THE BY RECIPIENT SELECTED SUBSIDIARY LICENSE CONDITIONS
 * OF OSMC-PL.
 *
 * See the full OSMC Public License conditions for more details.
 *
 */

encapsulated package NFEGraph
  // NF imports
  import ComponentRef = NFComponentRef;
  import Expression = NFExpression;
  import NFOperator.Op;
  import Operator = NFOperator;

  // Util imports
  import Array;
  import System;
  import UnorderedMap;
  import UnorderedSet;

protected
  import EGraph = NFEGraph;

public

  //TODO: Multary? Restrictions? Assoc
  //   + better hashes
  //   restructuring of the analysis would improve the performance


  type EClassId = Integer;

  type UnaryOp = enumeration(
    UMINUS,
    UDIV
  );

  type BinaryOp = enumeration(
    ADD,
    MUL,
    POW
  );

  function unaryOpToString
    input UnaryOp uop;
    output String op;
  algorithm
    op := match uop
      case UnaryOp.UMINUS then "-";
      case UnaryOp.UDIV then "1/"; // doesn't really make sense since there is no unary 1/x op in Operator
    end match;
  end unaryOpToString;

  function binaryOpToString
    input BinaryOp bop;
    output String op;
  algorithm
    op := match bop
      case BinaryOp.ADD then "+";
      case BinaryOp.MUL then "*";
      case BinaryOp.POW then "^";
    end match;
  end binaryOpToString;

  function unaryOpToOperator
    input UnaryOp uop;
    output Operator op;
  algorithm
    op := match uop
      case UnaryOp.UMINUS then Operator.makeUMinus(NFType.REAL());
      case UnaryOp.UDIV then Operator.makeDiv(NFType.REAL()); // doesn't really make sense since there is no unary 1/x op in Operator
    end match;
  end unaryOpToOperator;

  function binaryOpToOperator
    input BinaryOp bop;
    output Operator op;
  algorithm
    op := match bop
      case BinaryOp.ADD then Operator.makeAdd(NFType.REAL());
      case BinaryOp.MUL then Operator.makeMul(NFType.REAL());
      case BinaryOp.POW then Operator.makePow(NFType.REAL());
    end match;
  end binaryOpToOperator;

  function hashUnaryOp
    input UnaryOp uop;
    output Integer hash;
  algorithm
    hash := match uop
      case UnaryOp.UMINUS then 1;
      case UnaryOp.UDIV then 2;
    end match;
  end hashUnaryOp;

  function hashBinaryOp
    input BinaryOp bop;
    output Integer hash;
  algorithm
    hash := match bop
      case BinaryOp.ADD then 1;
      case BinaryOp.MUL then 2;
      case BinaryOp.POW then 3;
    end match;
  end hashBinaryOp;

  function neutralElementBinaryOp
    input BinaryOp bop;
    output ENode node;
  algorithm
    node := match bop
      case BinaryOp.ADD
        then ENode.NUM(0);
      case BinaryOp.MUL
        then ENode.NUM(1);
      else fail(); // later more e.g. unit matrix, operator record; use Type in general
    end match;
  end neutralElementBinaryOp;

  encapsulated uniontype ENode
    import NFEGraph.*;

  public
    record NUM
      Real num;
    end NUM;

    record SYMBOL
      ComponentRef cref;
    end SYMBOL;

    record UNARY
      EClassId id;
      UnaryOp op;
    end UNARY;

    record BINARY
      EClassId id1;
      EClassId id2;
      BinaryOp op;
    end BINARY;

    function isEqual
      input ENode node1;
      input ENode node2;
      output Boolean isEqual;
    algorithm
      isEqual := match (node1, node2)
        case (NUM(),    NUM())    then node1.num == node2.num;
        case (SYMBOL(), SYMBOL()) then ComponentRef.isEqual(node1.cref, node2.cref);
        case (UNARY(),  UNARY())  then node1.id == node2.id and node1.op == node2.op;
        case (BINARY(), BINARY()) then node1.id1 == node2.id1 and
                                       node1.id2 == node2.id2 and
                                       node1.op  == node2.op;
                                  else false;
      end match;
    end isEqual;

    function isEqualPtr
      input Pointer<ENode> node1;
      input Pointer<ENode> node2;
      output Boolean b = isEqual(Pointer.access(node1), Pointer.access(node2));
    end isEqualPtr;

    function hash
      input ENode node;
      input Integer mod;
      output Integer hash;
    algorithm
      hash := match node
        local
          EClassId id1, id2;
        case NUM()               then stringHashDjb2Mod(realString(node.num), mod);
        case SYMBOL()            then ComponentRef.hash(node.cref, mod);
        case UNARY()             then intMod(node.id * 3 + 7 * hashUnaryOp(node.op) + 1, mod);
        case BINARY(id1, id2, _) then intMod(div((id1 + id2) * (id1 + id2 + 1), 2) + id1 + hashBinaryOp(node.op), mod);
      end match;
    end hash;

    function hashPtr
      input Pointer<ENode> node;
      input Integer mod;
      output Integer h = hash(Pointer.access(node), mod);
    end hashPtr;

    function children
      "Returns a list of all unique child EClassIds of an ENode."
      input ENode node;
      output list<EClassId> children;
    algorithm
      children := match node
        case UNARY()  then {node.id};
        case BINARY() then if node.id1 == node.id2
                           then {node.id1}
                           else {node.id1, node.id2};
                      else {};
      end match;
    end children;

    function make
      input output ENode node;
      input list<EClassId> children;
    // TODO incorporate egraph analysis here?
    algorithm
      node := match (node, children)
        local
          EClassId id1, id2;
        case (NUM(),    {})         then node;
        case (SYMBOL(), {})         then node;
        case (UNARY(),  {id1})      then UNARY(id1, node.op);
        case (BINARY(), {id1})      then BINARY(id1, id1, node.op);
        case (BINARY(), {id1, id2}) then BINARY(id1, id2, node.op);
        else node;
      end match;
    end make;
  end ENode;

  uniontype EClass
    import NFEGraph.*;

  public
    record ECLASS
      UnorderedSet<Pointer<ENode>> nodes;
      list<tuple<Pointer<ENode>, EClassId>> parents;
      Option<Real> num;
      //Option<Expression> value;
    end ECLASS;
  end EClass;

  uniontype UnionFind
    "UnionFind is a forrest structure for grouping things with a root representative.
     It is used to tell if two nodes are equivalent and to find a canonical root."

  public
    record UNION_FIND
      array<Integer> nodes;
      Integer nodeCount;
    end UNION_FIND;

    function new
      output UnionFind unionfind = UNION_FIND(arrayCreate(1, -1), 0);
    end new;

    function make
      "Creates a new root node and returns its index. Might trigger an array expand."
      input output UnionFind unionfind;
      output Integer index;
    algorithm
      unionfind.nodeCount := unionfind.nodeCount + 1;
      index := unionfind.nodeCount;
      if arrayLength(unionfind.nodes) < index then
        unionfind.nodes := Array.expand(realInt(intReal(index) * 1.4), unionfind.nodes, -1);
      end if;
      unionfind.nodes[index] := index;
    end make;

    function find
      "finds the root of index"
      input UnionFind unionfind;
      input Integer index;
      input String origin "debug, origin of call";
      output Integer root = index;
    protected
      Integer count = 0;
    algorithm
      // follow the path to the root
      while root <> unionfind.nodes[root] loop
        root := unionfind.nodes[root];
        count := count + 1;
      end while;
      // set to root for future calls so the paths don't grow so much.
      unionfind.nodes[index] := root;
      // DEBUG
      //if count > 0 and substring(origin, 1, 6) == "repair" then
      //  print("[find] " + origin + ": " + intString(index) + " --> "+ intString(root) + " (" + intString(count) + " steps)\n");
      //end if;
    end find;

    function union
      "Given two root ids, unions the classes making root1 the leader of root2"
      input Integer index1;
      input Integer index2;
      input UnionFind unionfind;
    algorithm
      unionfind.nodes[index2] := index1;
    end union;
  end UnionFind;

  encapsulated uniontype EGraph
    import NFEGraph.*;

  public
    record EGRAPH
      UnorderedMap<Pointer<ENode>, EClassId> hashcons "maps every ENode to its containing EClassId";
      UnionFind unionfind "forrest structure for equivalent EClasses";
      UnorderedMap<EClassId, EClass> eclasses;
      list<EClassId> worklist;
    end EGRAPH;

    function new
      output EGraph egraph;
    algorithm
      egraph := EGRAPH(
        hashcons   = UnorderedMap.new<EClassId>(ENode.hashPtr, ENode.isEqualPtr),
        unionfind  = UnionFind.new(),
        eclasses   = UnorderedMap.new<EClass>(intMod,intEq),
        worklist   = {}
      );
    end new;

    function binaryByOperator
      input Expression exp1, exp2;
      input Operator op;
      input output EGraph graph;
      output EClassId id;
    algorithm
      (graph, id) :=  match op.op
        local
          EClassId id1, id2, id3;
        case Op.ADD algorithm
          (graph, id1) := newFromExp(exp1, graph);
          (graph, id2) := newFromExp(exp2, graph);
        then add(ENode.BINARY(id1, id2, BinaryOp.ADD), graph);
        case Op.SUB algorithm
          (graph, id1) := newFromExp(exp1, graph);
          (graph, id2) := newFromExp(exp2, graph);
          (graph, id3) := add(ENode.UNARY(id2, UnaryOp.UMINUS), graph);
        then add(ENode.BINARY(id1, id3, BinaryOp.ADD), graph);
        case Op.MUL algorithm
          (graph, id1) := newFromExp(exp1, graph);
          (graph, id2) := newFromExp(exp2, graph);
        then EGraph.add(ENode.BINARY(id1, id2, BinaryOp.MUL), graph);
        case Op.DIV algorithm
          (graph, id1) := newFromExp(exp1, graph);
          (graph, id2) := newFromExp(exp2, graph);
          (graph, id3) := add(ENode.UNARY(id2, UnaryOp.UDIV), graph);
        then add(ENode.BINARY(id1, id3, BinaryOp.MUL), graph);
        case Op.POW algorithm
          (graph, id1) := newFromExp(exp1, graph);
          (graph, id2) := newFromExp(exp2, graph);
        then add(ENode.BINARY(id1, id2, BinaryOp.POW), graph);
        else algorithm
          Error.addInternalError(getInstanceName() + " failed.", sourceInfo());
        then fail();
      end match;
    end binaryByOperator;

    function unaryByOperator
      input Expression exp;
      input Operator op;
      input output EGraph graph;
      output EClassId id;
    algorithm
      (graph, id) :=  match op.op
        local
          EClassId tmpId;
        case Op.UMINUS algorithm
          (graph, tmpId) := newFromExp(exp, graph);
        then add(ENode.UNARY(tmpId, UnaryOp.UMINUS), graph);
        else fail();
      end match;
    end unaryByOperator;

    function multaryByOperator
      input list<Expression> arguments, inv_arguments;
      input Operator op;
      input output EGraph graph;
      output EClassId id;
    protected
      EClassId idNew;
      BinaryOp chainOp;
      UnaryOp invOp;
    algorithm
      (chainOp, invOp) := match op.op
        case Op.ADD then (BinaryOp.ADD, UnaryOp.UMINUS);
        case Op.MUL then (BinaryOp.MUL, UnaryOp.UDIV);
        else fail();
      end match;

      (graph, id) := match (arguments, inv_arguments)
        local
          Expression exp;
        case ({}, {}) then add(neutralElementBinaryOp(chainOp), graph);
        case ({exp}, {}) then newFromExp(exp, graph);
        case ({}, {exp}) then newFromExp(exp, graph); // is this correct? there should be an inversion
        else algorithm
          id := -1;
          for arg in arguments loop
            (graph, idNew) :=  newFromExp(arg, graph);
            if id == -1 then
              id := idNew;
            else
              (graph, id) := add(ENode.BINARY(id, idNew, chainOp), graph);
            end if;
          end for;
          for inv_arg in inv_arguments loop
            (graph, idNew) := newFromExp(inv_arg, graph);
            (graph, idNew) := add(ENode.UNARY(idNew, invOp), graph);
            if id == -1 then
              id := idNew;
            else
              (graph, id) := add(ENode.BINARY(id, idNew, chainOp), graph);
            end if;
          end for;
        then (graph, id);
      end match;
    end multaryByOperator;

    function newFromExp
      input Expression exp;
      input output EGraph graph = new();
      output EClassId id;
    algorithm
      (graph, id) := match exp
        local
          Expression exp1, exp2;
          Operator op;
          Real num;
          Integer i;
          ComponentRef cref;
          list<Expression> arguments, inv_arguments;
        case Expression.MULTARY(arguments, inv_arguments, op) then multaryByOperator(arguments, inv_arguments, op, graph);
        case Expression.BINARY(exp1, op, exp2)                then binaryByOperator(exp1, exp2, op, graph);
        case Expression.UNARY(op, exp1)                       then unaryByOperator(exp1, op, graph);
        case Expression.REAL(num)                             then add(ENode.NUM(num), graph);
        case Expression.INTEGER(i)                            then add(ENode.NUM(intReal(i)), graph);
        case Expression.CREF(cref = cref)                     then add(ENode.SYMBOL(cref), graph);
        else algorithm
          Error.addInternalError(getInstanceName() + " failed for expression: " + Expression.toString(exp), sourceInfo());
        then fail();
      end match;
    end newFromExp;

    function add
      "Adds an ENode to the EGraph. If the node is already in the EGraph, returns the ENode's id,
      otherwise adds the id to both maps and extends the unionfind."
      input ENode node;
      input output EGraph graph;
      output EClassId id;
    protected
      Pointer<ENode> node_ptr;
      UnionFind unionfind;
      UnorderedSet<Pointer<ENode>> nodeSet;
      EClass child_class;
      EClassId numid;
      Option<Real> optnum;
      Real num;
      type ENodePointer = Pointer<ENode>;
    algorithm
      node_ptr := Pointer.create(node);
      EGraph.canonicalize(graph, node_ptr);
      try
        SOME(id) := UnorderedMap.get(node_ptr, graph.hashcons);
        id := find(graph, id, "add_try");
      else
        (unionfind, id) := UnionFind.make(graph.unionfind);
        graph.unionfind := unionfind;
        UnorderedMap.add(node_ptr, id, graph.hashcons);
        optnum := getNum(graph, Pointer.access(node_ptr));
        nodeSet := UnorderedSet.new<ENodePointer>(ENode.hashPtr, ENode.isEqualPtr);
        UnorderedSet.add(node_ptr, nodeSet);
        UnorderedMap.add(id, ECLASS(nodeSet, {}, optnum), graph.eclasses);
        for child_id in ENode.children(Pointer.access(node_ptr)) loop
          child_id := find(graph, child_id, "add_else");
          child_class := UnorderedMap.getSafe(child_id, graph.eclasses, sourceInfo());
          child_class.parents := (node_ptr, id) :: child_class.parents;
          UnorderedMap.add(child_id, child_class, graph.eclasses);
        end for;

        // analysis part
        if isSome(optnum) then
          SOME(num) := optnum;
          (graph, numid) := add(ENode.NUM(num), graph);
          //print("ANALYSIS UNION: " + intString(id) + "-> " + intString(EGraph.find(graph,numid)) + "\n");
          (graph, _) := union(id, numid, graph);
        end if;
      end try;
    end add;

    function find
      "Returns the root element of an EClassId."
      input EGraph graph;
      input output EClassId id;
      input String origin "debug";
    algorithm
      id := UnionFind.find(graph.unionfind, id, origin);
    end find;

    function union
      input EClassId id1;
      input EClassId id2;
      input output EGraph graph;
      output Boolean changed;
    protected
      EClassId newId1, newId2;
      EClass class1, class2;
      Option<Real> numNew;
      ENode node;
    algorithm
      newId1 := EGraph.find(graph, id1, "union1");
      newId2 := EGraph.find(graph, id2, "union2");
      changed := newId1 <> newId2;
      if changed then
        class1 :=  UnorderedMap.getSafe(newId1, graph.eclasses, sourceInfo());
        class2 :=  UnorderedMap.getSafe(newId2, graph.eclasses, sourceInfo());
        // short part for the analysis
        numNew := match (class1.num, class2.num)
          local
            Real num1, num2;
          case (NONE(), SOME(num2)) then SOME(num2);
          case (SOME(num1), NONE()) then SOME(num1);
          case (SOME(num1), SOME(num2)) algorithm
            if num1 <> num2 then // error case
              print("constants not equal error" + realString(num1) + " <> " + realString(num2) + "\n");
              fail();
            end if;
            then SOME(num1);
          else NONE();
        end match;
        // end of analysis part
        if listLength(class1.parents) >= listLength(class2.parents) then
          graph := unionOrdered(newId1, newId2, class1, class2, numNew, graph);
        else
          graph := unionOrdered(newId2, newId1, class2, class1, numNew, graph);
        end if;
      end if;
    end union;

    function unionOrdered
    "part of EGraph.union, id1 and id2 need to be roots, |class1.nodes| >= |class2.nodes|"
      input EClassId id1, id2;
      input EClass class1, class2;
      input Option<Real> numNew;
      input output EGraph graph;
    algorithm
      UnionFind.union(id1, id2, graph.unionfind);
      class1.parents := listAppend(class1.parents, class2.parents);
      for node in UnorderedSet.toList(class2.nodes) loop
        UnorderedSet.add(node, class1.nodes);
      end for;
      class1.num := numNew;
      graph.worklist := id1 :: graph.worklist;
      UnorderedMap.remove(id2, graph.eclasses); // non-root class is unneeded
      UnorderedMap.add(id1, class1, graph.eclasses);
    end unionOrdered;

    function canonicalize
      "new children of an ENode will become the root elements of the old children"
      input EGraph graph;
      input output Pointer<ENode> node;
    protected
      list<EClassId> children;
    algorithm
      children := list(find(graph, id, "canonicalize") for id in ENode.children(Pointer.access(node)));
      Pointer.update(node, ENode.make(Pointer.access(node), children));
    end canonicalize;

    function rebuild
      input output EGraph graph;
    protected
      UnorderedSet<EClassId> workset;
    algorithm
      workset := UnorderedSet.new<EClassId>(intMod, intEq);
      for eclassid in graph.worklist loop
        UnorderedSet.add(find(graph, eclassid, "rebuild"), workset);
      end for;
      graph := UnorderedSet.fold(workset, repair, graph);
      graph.worklist := {};
    end rebuild;

    function repair
      input EClassId eclassid; // must be a root id
      input output EGraph graph;
    protected
      EClass elem, node_elem;
      Pointer<ENode> node;
      EClassId id;
      UnorderedMap<Pointer<ENode>, EClassId> new_parents;
    algorithm
      elem := UnorderedMap.getSafe(find(graph, eclassid, "repair0"), graph.eclasses, sourceInfo());
      for tup in elem.parents loop
        (node, id) := tup;
        node_elem := UnorderedMap.getSafe(find(graph, id, "repair1"), graph.eclasses, sourceInfo());
        UnorderedSet.remove(node, node_elem.nodes);
        UnorderedMap.remove(node, graph.hashcons);
        node := canonicalize(graph, node);
        UnorderedMap.add(node, find(graph, id, "repair2"), graph.hashcons);
        UnorderedSet.add(node, node_elem.nodes);
      end for;
      new_parents := UnorderedMap.new<EClassId>(ENode.hashPtr, ENode.isEqualPtr);
      elem := UnorderedMap.getSafe(find(graph, eclassid, "repair3"), graph.eclasses, sourceInfo()); // get it again in case it changed as its own parent?
      for tup in elem.parents loop
        (node, id) := tup;
        node := canonicalize(graph, node);
        if UnorderedMap.contains(node, new_parents) then
          _ := union(id, UnorderedMap.getOrFail(node, new_parents), graph);
        end if;
        UnorderedMap.add(node, find(graph, id, "repair4"), new_parents);
      end for;
      elem.parents := UnorderedMap.toList(new_parents);
      UnorderedMap.add(eclassid, elem, graph.eclasses);
    end repair;

    function getNum
      "Checks if an ENode is actually a constant expression and returns Option of that value
      - core element of the analysis (combining constants when enodes/classes
      are added or when two classes get unioned)"
      input EGraph egraph;
      input ENode node;
      output Option<Real> num;
    algorithm
      num := match node
        local
          EClass eclass1, eclass2;
          EClassId id1,id2;
          Real num1,num2;
          BinaryOp bop;
          UnaryOp uop;
          Option<Real> numtemp;
        case ENode.BINARY(id1, id2, bop) algorithm
          id1 := find(egraph, id1, "getNum_binary1");
          id2 := find(egraph, id2, "getNUm_binary2");
          eclass1 := UnorderedMap.getSafe(id1, egraph.eclasses, sourceInfo());
          eclass2 := UnorderedMap.getSafe(id2, egraph.eclasses, sourceInfo());
          numtemp := match (eclass1.num, eclass2.num, bop)
            case (SOME(num1), SOME(num2), BinaryOp.ADD) then
              SOME(num1 + num2);
            case (SOME(num1), SOME(num2), BinaryOp.MUL) then
              SOME(num1 * num2);
            case (SOME(num1), SOME(num2), BinaryOp.POW) then
              SOME(num1 ^ num2);
            else NONE();
          end match;
          then numtemp;
        case ENode.UNARY(id1, uop) algorithm
          id1 := find(egraph, id1, "getNum_unary");
          eclass1 := UnorderedMap.getOrFail(id1, egraph.eclasses);
          numtemp := match (eclass1.num, uop)
            case (SOME(num1), UnaryOp.UDIV) guard (num1 <> 0) then
              SOME(1/num1);
            case (SOME(num1), UnaryOp.UMINUS) then
              SOME(-num1);
            else NONE();
          end match;
          then numtemp;
        case ENode.SYMBOL(_) then NONE();
        case ENode.NUM(num1) then SOME(num1);
        else NONE();
      end match;
    end getNum;

    function printAll
    "function to print all expressions of the egraph"
      input EClassId id;
      input EGraph egraph;
    protected
      list<String> allstrings;
    algorithm
      allstrings := allExpressions(id, egraph);
      print("All expressions:\n");
      print("size: " + intString(listLength(allstrings)) + "\n");
      for tempString in allstrings loop
        print(tempString  + "\n");
      end for;
    end printAll;

    function allExpressions
      input EClassId id;
      input EGraph egraph;
      output list<String> allstrings;
    protected
      EClass eclass;
      ENode node;
      EClassId root_id;
      String out;
      list<String> tempList;
      Boolean b;
    algorithm
      allstrings := {};
      root_id := find(egraph, id, "allExpressions");
      eclass := UnorderedMap.getOrFail(root_id, egraph.eclasses);
      for node_ptr in UnorderedSet.toList(eclass.nodes) loop
        node := Pointer.access(node_ptr);
        b := match node
          local
            ComponentRef cref;
            EClassId id1,id2;
            BinaryOp bop;
            UnaryOp uop;
            String tempString1, tempString2, tempString3;
            Real num;
            list<String> list1, list2;
          case (ENode.BINARY(id1, id2, bop)) algorithm
            list1 := allExpressions(id1, egraph);
            list2 := allExpressions(id2, egraph);
            for tempString1 in list1 loop
              for tempString2 in list2 loop
                tempString3 := "(" +  binaryOpToString(bop) + " " + tempString1 + " " + tempString2 + ")";
                allstrings := tempString3 :: allstrings;
              end for;
            end for;
            then true;
          case (ENode.UNARY(id1, uop)) algorithm
            list1 := allExpressions(id1, egraph);
            for tempString1 in list1 loop
              tempString3 := "(" + unaryOpToString(uop) + " " + tempString1 + ")";
              allstrings := tempString3 :: allstrings;
            end for;
            then true;
          case ENode.SYMBOL(cref) algorithm
            allstrings := NFComponentRef.toString(cref) :: allstrings;
            then true;
          case ENode.NUM(num) algorithm
            allstrings := realString(num) :: allstrings;
            then true;
          else false;
        end match;
      end for;
    end allExpressions;

    function graphDump
      input EClassId baseId;
      input EGraph egraph;
      input Boolean init;
    protected
      Integer nodeId;
      Option<Integer> biasValue;
      EClassId classId;
      EClass clazz;
      String nodeStr;
      UnorderedMap<EClassId, Integer> bias;
    algorithm
    //print("\n-------------------------------\n");
    //print("      Graph Dump \n");
    //print("-------------------------------\n\n");
    if not init then
      print("!\n");
    end if;
    print(intString(find(egraph, baseId, "graphDump_base")) + "\n");
    bias := UnorderedMap.new<EClassId>(intMod,intEq);
    for cl in UnorderedMap.toList(egraph.eclasses) loop
      (classId, clazz) := cl;
      //classId := find(egraph, classId, "graphDump_id");
      biasValue := UnorderedMap.get(classId, bias);
      nodeId := match biasValue
        local
          Integer b;
        case SOME(b) then b;
        else 0;
      end match;
      for node in UnorderedSet.toList(clazz.nodes) loop
        nodeId := nodeId + 1;
        nodeStr := nodeGraphDump(Pointer.access(node), egraph);
        print(intString(classId) + "," + intString(nodeId) + "," + nodeStr + "\n");
      end for;
      UnorderedMap.add(classId, nodeId, bias);
    end for;
    end graphDump;

    function nodeGraphDump
      input ENode node;
      input EGraph egraph;
      output String outStr;
    algorithm
      outStr := match node
        local
          Real x;
          ComponentRef cref;
          EClassId id1, id2;
          UnaryOp uop;
          BinaryOp bop;
        case ENode.NUM(x)                then (realString(x) + ",,");
        case ENode.SYMBOL(cref)          then (NFComponentRef.toString(cref) + ",,");
        case ENode.UNARY(id1, uop)       then (unaryOpToString(uop) + "," + intString(id1) + ",");
        case ENode.BINARY(id1, id2, bop) then (binaryOpToString(bop) + "," + intString(id1) + ";" + intString(id2) + ",");
        else fail();    // multary not implemented yet.
      end match;
    end nodeGraphDump;

    function checkInvariantsHashcons
      input EGraph G;
      output Boolean correct;
    protected
      Integer rootId;
      list<tuple<EClassId, EClassId>> err;
    algorithm
      print("----------------------------\nINVARIANTSHASHCONS\n");
      correct := true;
      err := {};
      for node in UnorderedMap.keyList(G.hashcons) loop
        for childId in ENode.children(Pointer.access(node)) loop
          rootId := find(G, childId, "checkInvariantsHashcons");
          if childId <> rootId then
            correct := false;
            err := (childId, rootId) :: err;
            print(intString(childId) + " --> " + intString(rootId) + "\n");
          end if;
        end for;
      end for;
      print("ERRLISTLEN: " + intString(listLength(err)) + "\n");
      print("----------------------------\n");
    end checkInvariantsHashcons;

    function checkInvariantsEClasses
      input EGraph G;
      output Boolean correct;
    protected
      Integer rootId;
      list<tuple<EClassId, EClassId>> err;
    algorithm
      print("----------------------------\nINVARIANTSCLASSES\n");
      correct := true;
      err := {};
      for eclass in UnorderedMap.valueList(G.eclasses) loop
        for node in UnorderedSet.toList(eclass.nodes) loop
          for childId in ENode.children(Pointer.access(node)) loop
            rootId := find(G, childId, "checkInvariantsEClasses");
            if childId <> rootId then
              correct := false;
              err := (childId, rootId) :: err;
              print(intString(childId) + " --> " + intString(rootId) + "\n");
            end if;
          end for;
        end for;
      end for;
      print("ERRLISTLEN: " + intString(listLength(err)) + "\n");
      print("----------------------------\n");
    end checkInvariantsEClasses;
  end EGraph;

  uniontype Extractor
    import NFEGraph.*;

  public
    record EXTRACTOR
      EGraph egraph                            "the EGraph from where we extract";
      UnorderedMap<EClassId, ENode> best_nodes "best ENode in each EClass";
      UnorderedMap<EClassId, Integer> dist     "cost of each EClass, lower is better";
    end EXTRACTOR;

    function new
      input EGraph egraph;
      output Extractor extractor;
    algorithm
      extractor := EXTRACTOR(
        egraph     = egraph,
        best_nodes = UnorderedMap.new<ENode>(intMod, intEq),
        dist       = UnorderedMap.new<Integer>(intMod, intEq)
      );
    end new;

    function extract
      input EClassId id;
      input output Extractor extractor;
      output Integer distance;
    protected
      EClass eclass;
      EClassId root_id;
    algorithm
      root_id := EGraph.find(extractor.egraph, id, "extract1");
      (distance, extractor) := match UnorderedMap.get(root_id, extractor.dist)
        local
          Integer dist, child_dist, best_dist;
          Pointer<ENode> best_node;

        case SOME(dist) then (dist, extractor);

        else algorithm
          // why did we do this again (something with recursion)?
          UnorderedMap.add(root_id, UnorderedMap.size(extractor.egraph.hashcons), extractor.dist);

          root_id := EGraph.find(extractor.egraph, root_id, "extract2"); // this looks unnecessary, see first line

          eclass := UnorderedMap.getOrFail(root_id, extractor.egraph.eclasses);
          best_dist := System.intMaxLit();
          for node in UnorderedSet.toList(eclass.nodes) loop
            dist := 1; // TODO cost depending on the node kind
            for class_child in ENode.children(Pointer.access(node)) loop
              (extractor, child_dist) := extract(class_child, extractor);
              dist := dist + child_dist;
            end for;
            if dist < best_dist then
              best_dist := dist;
              best_node := node;
            end if;
          end for;
          UnorderedMap.add(root_id, best_dist, extractor.dist);
          UnorderedMap.add(root_id, Pointer.access(best_node), extractor.best_nodes);
        then (best_dist, extractor);
      end match;
    end extract;

    function build
      input EClassId start;
      input Extractor extractor;
      output Expression exp;
    protected
      EClassId temp_start;
      ENode node;
    algorithm
      temp_start := EGraph.find(extractor.egraph, start, "build");
      node := UnorderedMap.getOrFail(temp_start, extractor.best_nodes);
      exp := match node
        local
          Real num;
          EClassId id1,id2;
          UnaryOp uop;
          BinaryOp bop;
          ComponentRef cref;
        case ENode.NUM(num)
          then Expression.REAL(num);
        case ENode.SYMBOL(cref)
          then Expression.CREF(NFType.REAL(), cref);
        case ENode.UNARY(id1, uop) guard(uop <> UnaryOp.UDIV)
          then Expression.UNARY(
            unaryOpToOperator(uop),
            Extractor.build(id1,extractor));
        case ENode.UNARY(id1, uop) guard(uop <> UnaryOp.UDIV)
          then Expression.BINARY(
            Expression.REAL(1),
            Operator.makeDiv(NFType.REAL()),
            Extractor.build(id1,extractor));
        case ENode.BINARY(id1,id2,bop)
          then Expression.BINARY(
            Extractor.build(id1,extractor),
            binaryOpToOperator(bop),
            Extractor.build(id2,extractor));
        else algorithm
          print("Else Error\n");
          then fail();
      end match;
    end build;
  end Extractor;

  encapsulated uniontype Pattern
  import NFEGraph.*;
  public

    record NUM
      Real value;
    end NUM;

    record VAR
      Integer id;
    end VAR;

    record SYMBOL
      String str;
    end SYMBOL;

    record BINARY
      Pattern child1;
      Pattern child2;
      BinaryOp op;
    end BINARY;

    record UNARY
      Pattern child;
      UnaryOp op;
    end UNARY;

    function fromStringHelper
      "helper for parsing: String -> Rule"
      input output StringReader sr;
      input output UnorderedMap<String,Integer> vars = UnorderedMap.new<Integer>(stringHashDjb2Mod, stringEqual);
      output Pattern pattern;
    protected
      Integer char;
      Real num;
      String strVar, strOp;
      BinaryOp bop;
      UnaryOp uop;
      Option<BinaryOp> optbop;
      Option<UnaryOp> optuop;
      Pattern p1, p2;
    algorithm
      (sr, char) := StringReader.consume(sr);
      if char == stringCharInt("(") then
        strOp := "";
        while StringReader.getNext(sr) <> 32 loop // whitespace
          (sr, char) := StringReader.consume(sr);
          strOp := stringAppend(strOp, intStringChar(char));
        end while;
        (optbop,optuop) := operatorType(strOp);
        pattern := match (optbop, optuop)
          case (SOME(bop), _) algorithm
            sr := StringReader.consumeSpaces(sr);
            (sr, vars, p1) := fromStringHelper(sr, vars);
            sr := StringReader.consumeSpaces(sr);
            (sr, vars, p2) := fromStringHelper(sr, vars);
            sr := StringReader.consumeSpaces(sr);
            (sr, char) := StringReader.consume(sr);
            if char <> stringCharInt(")")
              then fail();
            end if;
            then BINARY(p1, p2, bop);
          case (_, SOME(uop)) algorithm
            sr := StringReader.consumeSpaces(sr);
            (sr, vars, p1) := fromStringHelper(sr, vars);
            sr := StringReader.consumeSpaces(sr);
            (sr, char) := StringReader.consume(sr);
            if char <> stringCharInt(")") then
              print("missing ')' \n");
              fail();
            end if;
            then UNARY(p1, uop);
          else fail();
        end match;
      elseif char == stringCharInt("?") then
        strVar := "";
        while isAlpha(StringReader.getNext(sr)) loop
          (sr, char) := StringReader.consume(sr);
          strVar := stringAppend(strVar, intStringChar(char));
        end while;
        pattern := VAR(UnorderedMap.tryAdd(strVar, UnorderedMap.size(vars), vars));
      elseif char >= stringCharInt("0") and char <= stringCharInt("9") then
        num := char - stringCharInt("0");
        while isNumeric(StringReader.getNext(sr)) loop
          (sr, char) := StringReader.consume(sr);
          num := 10*num  + char - stringCharInt("0");
        end while;
        pattern := NUM(num);
      elseif char == stringCharInt("-") then
        num := 0;
        while isNumeric(StringReader.getNext(sr)) loop
          (sr, char) := StringReader.consume(sr);
          num := 10*num  + char - stringCharInt("0");
        end while;
        pattern := NUM(-num);
      else
        print("Unexpected character fail");
        fail();
      end if;
    end fromStringHelper;

    function hash
      input Pattern p;
      input Integer mod;
      output Integer out;
    algorithm
      out := match p
        local
          Integer varId;
          Real num;
          BinaryOp bop;
          UnaryOp uop;
          Pattern temp_pattern1,temp_pattern2;
          String str;
        case VAR(varId)
          then 17*varId + 1000;
        case NUM(num)
          then 13*(realInt(num) + 7);
        case SYMBOL(str)
          then stringHashDjb2Mod(str, mod);
        case BINARY(temp_pattern1, temp_pattern2, bop)
          then hash(temp_pattern1, mod) + hash(temp_pattern2, mod) + EGraph.hashBinaryOp(bop);
        case UNARY(temp_pattern1, uop)
          then hash(temp_pattern1, mod) + EGraph.hashUnaryOp(uop);
      end match;
    end hash;

    function matchPattern
      input Pointer<ENode> node_ptr;
      input EClassId id;
      input EGraph egraph;
      input Pattern pattern;
      output list<UnorderedMap<Integer, EClassId>> subs;
    protected
      ENode node = Pointer.access(node_ptr);
    algorithm
      subs := match (pattern, node)
        case (BINARY(), ENode.BINARY()) guard(pattern.op == node.op)
          then matchPatternRecurse(node.id2, egraph, pattern.child2, matchPatternRecurse(node.id1, egraph, pattern.child1));
        case (UNARY(), ENode.UNARY()) guard(pattern.op == node.op)
          then matchPatternRecurse(node.id, egraph, pattern.child);
        /* are there ever singleton rules? (x -> ???) */
        else {};
      end match;
    end matchPattern;

    function matchPatternRecurse
      input EClassId id;
      input EGraph egraph;
      input Pattern pattern;
      input list<UnorderedMap<Integer, EClassId>> subs_in = {UnorderedMap.new<EClassId>(intMod,intEq)};
      output list<UnorderedMap<Integer, EClassId>> subs_out;
    protected
      EClass eclass;
      EClassId root_id;
      UnorderedMap<Integer, EClassId> temp_map;
      list<UnorderedMap<Integer, EClassId>> temp_list, node_list;
      ENode node;
    algorithm
      root_id := EGraph.find(egraph,id, "matchPatternRecurse");
      eclass := UnorderedMap.getOrFail(root_id,egraph.eclasses);
      subs_out := {};
      for node_ptr in UnorderedSet.toList(eclass.nodes) loop
        node := Pointer.access(node_ptr);
        node_list := {};
        for map in subs_in loop
          node_list := UnorderedMap.copy(map) :: node_list;
        end for;
        node_list :=  match (pattern, node)
          local
            Integer varId;
            Real num1, num2;
            BinaryOp bop1,bop2;
            UnaryOp uop1,uop2;
            EClassId temp_id1,temp_id2;
            Pattern temp_pattern1,temp_pattern2;
            String str1, str2;
            Boolean ok;
          case (Pattern.VAR(varId), _) algorithm
            // case for common subexpression: e.g. (3*x + 1) + (3*x + 1) -> 2 * (3*x + 1)
            temp_list := {};
            for temp_map in node_list loop
              ok := match UnorderedMap.get(varId,temp_map)
                case SOME(temp_id1) then temp_id1 == root_id;
                else algorithm
                  UnorderedMap.add(varId,root_id,temp_map);
                then true;
              end match;
              if ok then
                temp_list := temp_map :: temp_list;
              end if;
            end for;
            then temp_list;
          case (Pattern.NUM(num1), ENode.NUM(num2))
            then if num1 == num2 then node_list else {};
          /*case (Pattern.SYMBOL(str1), ENode.SYMBOL(str2)) algorithm
            // case to insure that a hard coded symbol in the pattern corresponds to a enode symbol
            // special case of VAR
            if str1 == str2 then temp_list := node_list; else temp_list := {}; end if;
            then temp_list;*/ // TODO MAYBE
          // simple recursion
          case (Pattern.BINARY(temp_pattern1,temp_pattern2,bop1),ENode.BINARY(temp_id1,temp_id2,bop2))
            guard(bop1 == bop2)
            then matchPatternRecurse(temp_id2,egraph,temp_pattern2, matchPatternRecurse(temp_id1,egraph,temp_pattern1,node_list));
          case (Pattern.UNARY(temp_pattern1,uop1),ENode.UNARY(temp_id1,uop2))
            guard(uop1 == uop2) then matchPatternRecurse(temp_id1,egraph,temp_pattern1,node_list);
          else {};
        end match;
        subs_out := listAppend(node_list,subs_out);
      end for;
    end matchPatternRecurse;

    function apply
      input Pattern pattern;
      input UnorderedMap<Integer, EClassId> sub;
      input output EGraph egraph;
      output EClassId eclassid;
    protected
      ENode temp_node;
      list<ENode> node_list;
    algorithm
      (egraph, eclassid) := match pattern
        local
          Integer varId;
          EClassId id1, id2;
          String str;
        case Pattern.NUM() then EGraph.add(ENode.NUM(pattern.value), egraph);
        //case Pattern.SYMBOL(str) then EGraph.add(ENode.SYMBOL(str), egraph); TODO MAYBE

        case Pattern.BINARY() algorithm
          (egraph, id1) := apply(pattern.child1, sub, egraph);
          (egraph, id2) := apply(pattern.child2, sub, egraph);
        then EGraph.add(ENode.BINARY(EGraph.find(egraph,id1, "apply1"), EGraph.find(egraph,id2, "apply2"), pattern.op), egraph);

        case Pattern.UNARY() algorithm
          (egraph, id1) := apply(pattern.child, sub, egraph);
        then EGraph.add(ENode.UNARY(EGraph.find(egraph,id1, "apply3"), pattern.op), egraph);

        case Pattern.VAR(varId) then (egraph, UnorderedMap.getOrFail(varId, sub));
      end match;
    end apply;
  end Pattern;

  uniontype Rule
  import NFEGraph.*;
  public

    record RULE
      Pattern pattern_in, pattern_out;
      String name;
    end RULE;

    function hash
      input Rule rule;
      input Integer mod;
      output Integer out;
    algorithm
      out :=  intMod(Pattern.hash(rule.pattern_in, mod) + 10*Pattern.hash(rule.pattern_out, mod) + 1, mod);
    end hash;

    function fromString
      "rule parser: e.g. '(+ ?a 0)', '?a' <=> a + 0 = a"
      input String pattern_in;
      input String pattern_out;
      input String name;
      output Rule rule;
    protected
      StringReader sr_in;
      StringReader sr_out;
      Pattern p1, p2;
      UnorderedMap<String,Integer> vars;
    algorithm
      sr_in := StringReader.new(pattern_in);
      sr_out := StringReader.new(pattern_out);
      (, vars, p1) := Pattern.fromStringHelper(sr_in);
      (, , p2) := Pattern.fromStringHelper(sr_out, vars);
      rule := Rule.RULE(p1, p2, name);
    end fromString;
  end Rule;

  uniontype RuleApplier
    import NFEGraph.*;

  public
    record RULE_APPLIER
      list<Rule> rules;
    end RULE_APPLIER;

    function matchApplyRules
      input RuleApplier ruleapplier;
      input output EGraph egraph;
      output Boolean saturated;
    protected
      list<tuple<Rule, EClassId, list<UnorderedMap<Integer, EClassId>>>> subs;
      list<UnorderedMap<Integer, EClassId>> subs_part;
      EClassId exId, newId;
      Pointer<ENode> node;
      Rule rule;
      Boolean changed;
      constant Boolean debug = false;
    algorithm
      // 1st phase: matching of all rules with all eclasses
      subs := {};
      if debug then print("--matching rules--\n"); end if;
      // TODO try to swap the order of loops here -> speed up?
      for rule in ruleapplier.rules loop
        if debug then print("match rule name: " + rule.name + "\n"); end if;
        for tpl in UnorderedMap.toList(egraph.hashcons) loop
          (node, exId) := tpl;
          subs_part := Pattern.matchPattern(node, exId, egraph, rule.pattern_in);
          if not listEmpty(subs_part) then
            subs := (rule, exId, subs_part) :: subs;
          end if;
        end for;
      end for;
      // 2nd phase: applying of the found patterns
      saturated := true;
      changed := false;
      if debug then print("--applying rules--\n"); end if;
      for sub in subs loop
        (rule, exId, subs_part) := sub;
        for map in subs_part loop
          (egraph, newId) := Pattern.apply(rule.pattern_out, map, egraph);
          (egraph, changed) := EGraph.union(exId, newId, egraph);
          if debug and changed then
            print("apply rule name: " + rule.name + "\n");
          end if;
          saturated := saturated and (not changed);
        end for;
      end for;
      // 3rd phase: rebuild the invariants of the egraph
      egraph := EGraph.rebuild(egraph);
    end matchApplyRules;

    function addRule
      "Adds one rule to an applier: (+ ?a 0), ?a, neutral-add "
      input String pattern_in;
      input String pattern_out;
      input String name;
      input output RuleApplier ra;
    algorithm
      ra.rules := Rule.fromString(pattern_in, pattern_out, name) :: ra.rules;
    end addRule;

    function addRules
      "Adds multiple rules to an applier: {((+ ?a 0), ?a, neutral-add),((+ ?a ?b), (+ ?b ?a), comm-add)}"
      input output RuleApplier ra;
      input list<tuple<String,String,String>> rules;
    protected
      String strp1, strp2, name;
    algorithm
      for strrule in rules loop
        (strp1, strp2, name) := strrule;
        ra.rules := Rule.fromString(strp1, strp2, name) :: ra.rules;
      end for;
    end addRules;
  end RuleApplier;

  uniontype StringReader
    record STRING_READER
      Integer bias;
      String string;
    end STRING_READER;

    function new
      input String str;
      output StringReader reader = STRING_READER(0, str);
    end new;

    function consume
      input output StringReader sr;
      output Integer char;
    algorithm
      // maybe fail if end-of-string is reached?
      sr.bias := sr.bias + 1;
      char := if sr.bias > stringLength(sr.string) then -1
              else stringGet(sr.string, sr.bias);
    end consume;

    function getNext
      input StringReader sr;
      output Integer char;
    protected
      Integer bias;
    algorithm
      // maybe fail if end-of-string is reached?
      bias := sr.bias + 1;
      char := if bias > stringLength(sr.string) then -1
              else stringGet(sr.string, bias);
    end getNext;

    function consumeSpaces
      input output StringReader sr;
    algorithm
      while getNext(sr) == 32 loop
        sr.bias := sr.bias + 1;
      end while;
    end consumeSpaces;
  end StringReader;

  function isAlpha
    input Integer char;
    output Boolean isAlpha;
  algorithm
    // stringCharInt("a") <= char <= stringCharInt("z")
    isAlpha := 97 <= char and char <= 122;
  end isAlpha;

  function isNumeric
    input Integer char;
    output Boolean isNumeric;
  algorithm
    // stringCharInt("0") <= char <= stringCharInt("9")
    isNumeric := 48 <= char and char <= 57;
  end isNumeric;

  function operatorType
    input String strOp;
    output Option<BinaryOp> bop;
    output Option<UnaryOp> uop;
  algorithm
    (bop, uop) := match strOp
      case "+" then (SOME(BinaryOp.ADD), NONE());
      case "*" then (SOME(BinaryOp.MUL), NONE());
      case "^" then (SOME(BinaryOp.POW), NONE());
      case "-" then (NONE(), SOME(UnaryOp.UMINUS));
      case "/" then (NONE(), SOME(UnaryOp.UDIV));
    end match;
  end operatorType;

  annotation(__OpenModelica_Interface="frontend");
end NFEGraph;
