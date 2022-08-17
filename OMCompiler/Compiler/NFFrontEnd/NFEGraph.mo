encapsulated package NFEGraph
  import UnorderedMap;
  import UnorderedSet;
  import Array;
  import NFExpression;
  import ComponentRef = NFComponentRef;
  import NFOperator.Op;
  import Operator = NFOperator;
public

  //TODO: Multary? Restrictions? Assoc
  //   + better hashes
  //   restructuring of the analysis would improve the performance


  type EClassId = Integer;
  type UnaryOp = enumeration(
    UMINUS,
    UDIV);
  type BinaryOp = enumeration(
    ADD,
    MUL,
    POW);

  function binaryOpToNFOperator
    input BinaryOp bop;
    output NFOperator op;
  algorithm
    op := match bop
      case BinaryOp.ADD then NFOperator.makeAdd(NFType.REAL());
      case BinaryOp.MUL then NFOperator.makeMul(NFType.REAL());
      case BinaryOp.POW then NFOperator.makePow(NFType.REAL());
    end match;
  end binaryOpToNFOperator;

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

  function unaryOpToString
    input UnaryOp uop;
    output String op;
  algorithm
    op := match uop
      case UnaryOp.UMINUS then "-";
      case UnaryOp.UDIV then "1/"; // doesn't really make sense since there is no unary 1/x op in NFOperator
    end match;
  end unaryOpToString;

  function unaryOpToNFOperator
    input UnaryOp uop;
    output NFOperator op;
  algorithm
    op := match uop
      case UnaryOp.UMINUS then NFOperator.makeUMinus(NFType.REAL());
      case UnaryOp.UDIV then NFOperator.makeDiv(NFType.REAL()); // doesn't really make sense since there is no unary 1/x op in NFOperator
    end match;
  end unaryOpToNFOperator;

  function hashUnaryOp
    input UnaryOp uop;
    output Integer hash;
  algorithm
    hash := match uop
      case UnaryOp.UMINUS then 1;
      case UnaryOp.UDIV then 2;
      else 3;
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
      else 4;
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
      else fail();    // later more e.g. unit matrix
    end match;
  end neutralElementBinaryOp;

  function compareUnaryOp
    input UnaryOp uop1, uop2;
    output Boolean equals;
  algorithm
    equals := (uop1 == uop2);
  end compareUnaryOp;

  function compareBinaryOp
    input BinaryOp bop1, bop2;
    output Boolean equals;
  algorithm
    equals := (bop1 == bop2);
  end compareBinaryOp;

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
      isEqual := match (node1,node2)
        local
          Real num1,num2;
          EClassId id1_1,id1_2,id2_1,id2_2;
          BinaryOp bop1, bop2;
          UnaryOp uop1, uop2;
          ComponentRef cref1,cref2;
        case (ENode.NUM(num1),ENode.NUM(num2))
          then num1 == num2;
        case (ENode.SYMBOL(cref1), ENode.SYMBOL(cref2))
          then ComponentRef.isEqual(cref1, cref2);
        case (ENode.BINARY(id1_1,id1_2,bop1),ENode.BINARY(id2_1,id2_2,bop2))
          then id1_1 == id2_1 and id1_2 == id2_2 and compareBinaryOp(bop1, bop2);
        case (ENode.UNARY(id1_1, uop1), ENode.UNARY(id2_1, uop2))
          then id1_1 == id2_1 and compareUnaryOp(uop1, uop2);
        else false;
      end match;
    end isEqual;

    function hash
      input ENode node;
      input Integer mod;
      output Integer hash;
    algorithm
      hash := match node
        local
          Real num;
          EClassId id1, id2;
          BinaryOp bop;
          UnaryOp uop;
          ComponentRef cref;
        case SYMBOL(cref) then ComponentRef.hash(cref, mod);
        case NUM(num) then intMod(realInt(num), mod);
        case BINARY(id1, id2, bop) then intMod(100 + id1 * 10 + id2 + 1000 * hashBinaryOp(bop) + 2, mod);
        case UNARY(id1, uop) then intMod(id1 * 10 + 1000 * hashUnaryOp(uop) + 1, mod);
      end match;
    end hash;

    function children
      input ENode node;
      output list<EClassId> childrenList;
    algorithm
      childrenList := match node
        local
          EClassId id1,id2;
        case (ENode.BINARY(id1,id2,_))
          then {id1,id2};
        case (ENode.UNARY(id1, _))
          then {id1};
        else
          then {};
      end match;
    end children;

    function make
      input ENode oldEnode;
      input list<EClassId> children;
      output ENode node;
    algorithm
      node := match oldEnode
        local
        BinaryOp bop;
        UnaryOp uop;
        case NUM(_) then oldEnode;
        case SYMBOL(_) then oldEnode;
        case BINARY(_, _, bop) then BINARY(listGet(children,1),listGet(children,2), bop);
        case UNARY(_, uop) then UNARY(listGet(children, 1), uop);
      end match;
    end make;

    function isNum
      input ENode node;
      output Boolean b;
    algorithm
      b := match node
        case NUM(_) then false;
        else true;
      end match;
    end isNum;
  end ENode;

  uniontype EClass
  import NFEGraph.*;
  public
    record ECLASS
      UnorderedSet<ENode> nodes;
      list<tuple<ENode,EClassId>> parents;
      Option<Real> num;
    end ECLASS;
  end EClass;

  uniontype UnionFind
  import NFEGraph.*;
  public
    record UNION_FIND
      array<Integer> nodes;
      Integer nodeCount;
    end UNION_FIND;

    function new
      output UnionFind unionfind = UNION_FIND(arrayCreate(1,-1),0);
    end new;

    function make
      input output UnionFind unionfind;
      output Integer index;
    algorithm
      unionfind.nodeCount := unionfind.nodeCount + 1;
      index := unionfind.nodeCount;
      if (arrayLength(unionfind.nodes) < unionfind.nodeCount) then
        unionfind.nodes := Array.expand(realInt(intReal(index) * 1.4), unionfind.nodes, -1);
      end if;
      unionfind.nodes[index] := index;
    end make;

    function find
      input UnionFind unionfind;
      input output Integer index;
    algorithm
      while index <> unionfind.nodes[index] loop
        index := unionfind.nodes[index];
      end while;
    end find;

    function union
      input Integer index1;
      input Integer index2;
      input output UnionFind unionfind;
      output Integer root1;
      output Integer root2;
    algorithm
      root1 := find(unionfind, index1);
      root2 := find(unionfind, index2);
      if root1 <> root2 then
        unionfind.nodes[root2] := root1;
      end if;
    end union;
  end UnionFind;

  encapsulated uniontype EGraph
  import NFEGraph.*;
  public
    record EGRAPH
      UnorderedMap<ENode,EClassId> hashcons;
      UnionFind unionfind;
      UnorderedMap<EClassId,EClass> eclasses;
      list<EClassId> worklist;
      list<EClassId> deletelist;
    end EGRAPH;

    function new
      output EGraph egraph;
    algorithm
      egraph := EGraph.EGRAPH(UnorderedMap.new<EClassId>(ENode.hash, ENode.isEqual),UnionFind.new(),UnorderedMap.new<EClass>(intMod,intEq),{},{});
    end new;

    function binaryByOperator
      input NFExpression exp1, exp2;
      input NFOperator op;
      input output EGraph graph;
      output EClassId id;
    algorithm
      (graph, id) :=  match op.op
      local
        EClassId id1, id2, id3;
        EGraph tmpGraph = graph;
          case Op.ADD algorithm
            (tmpGraph, id1) := newFromExp(exp1,tmpGraph);
            (tmpGraph, id2) := newFromExp(exp2,tmpGraph);
            then EGraph.add(ENode.BINARY(id1, id2, BinaryOp.ADD), tmpGraph);
          case Op.SUB algorithm
            (tmpGraph,id1) := newFromExp(exp1,tmpGraph);
            (tmpGraph,id2) := newFromExp(exp2,tmpGraph);
            (tmpGraph,id3) := EGraph.add(ENode.UNARY(id2, UnaryOp.UMINUS), tmpGraph);
            then EGraph.add(ENode.BINARY(id1, id3, BinaryOp.ADD), tmpGraph);
          case Op.MUL algorithm
            (tmpGraph,id1) := newFromExp(exp1,tmpGraph);
            (tmpGraph,id2) := newFromExp(exp2,tmpGraph);
            then EGraph.add(ENode.BINARY(id1, id2, BinaryOp.MUL), tmpGraph);
          case Op.DIV algorithm
            (tmpGraph,id1) := newFromExp(exp1,tmpGraph);
            (tmpGraph,id2) := newFromExp(exp2,tmpGraph);
            (tmpGraph,id3) := EGraph.add(ENode.UNARY(id2, UnaryOp.UDIV), tmpGraph);
            then EGraph.add(ENode.BINARY(id1, id3, BinaryOp.MUL), tmpGraph);
          case Op.POW algorithm
            (tmpGraph,id1) := newFromExp(exp1,tmpGraph);
            (tmpGraph,id2) := newFromExp(exp2,tmpGraph);
            then EGraph.add(ENode.BINARY(id1, id2, BinaryOp.POW), tmpGraph);
          else algorithm
            Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " Operator error!"});
          then fail();
      end match;
    end binaryByOperator;

    function unaryByOperator
      input NFExpression exp;
      input NFOperator op;
      input output EGraph graph;
      output EClassId id;
    algorithm
      (graph, id) :=  match op.op
      local
        EClassId tmpId;
        EGraph tmpGraph = graph;
        case Op.UMINUS algorithm
          (tmpGraph, tmpId) := newFromExp(exp, graph);
          then EGraph.add(ENode.UNARY(tmpId, UnaryOp.UMINUS), tmpGraph);
        else fail();
      end match;
    end unaryByOperator;

    function multaryByOperator
      input list<NFExpression> arguments, inv_arguments;
      input NFOperator op;
      input output EGraph graph;
      output EClassId id;
    protected
      NFExpression arg, inv_arg;
      EClassId idNew, idNewTemp;
      BinaryOp chainOp;
      UnaryOp invOp;
    algorithm
      (chainOp, invOp) := match op.op
        case Op.ADD then (BinaryOp.ADD, UnaryOp.UMINUS);
        case Op.MUL then (BinaryOp.MUL, UnaryOp.UDIV);
        else fail();
      end match;
      if listLength(arguments) == 0 and listLength(inv_arguments) == 0 then
        (graph, id) := EGraph.add(neutralElementBinaryOp(chainOp), graph);
      elseif listLength(arguments) == 1 and listLength(inv_arguments) == 0 then
        (graph, id) := newFromExp(listGet(arguments, 1), graph);
      elseif listLength(arguments) == 0 and listLength(inv_arguments) == 1 then
        (graph, id) := newFromExp(listGet(inv_arguments, 1), graph);
      else
        id := -1;
        for arg in arguments loop
          (graph, idNew) :=  newFromExp(arg, graph);
          if id == -1 then
            id := idNew;
          else
            (graph, id) := EGraph.add(ENode.BINARY(id, idNew, chainOp), graph);
          end if;
        end for;
        for inv_arg in inv_arguments loop
          (graph, idNewTemp) := newFromExp(inv_arg, graph);
          (graph, idNew) := EGraph.add(ENode.UNARY(idNewTemp, invOp), graph);
          if id == -1 then
            id := idNew;
          else
            (graph, id) := EGraph.add(ENode.BINARY(id, idNew, chainOp), graph);
          end if;
        end for;
      end if;
    end multaryByOperator;


    function newFromExp
      input NFExpression exp;
      input output EGraph graph = EGraph.new();
      output EClassId id;
    algorithm
      (graph, id) := match exp
        local
          NFExpression exp1, exp2;
          Operator op;
          EClassId id1, id2, id3;
          Real num;
          Integer i;
          ComponentRef cref;
          EGraph tmp_graph = graph;
          list<NFExpression> arguments, inv_arguments;
        case NFExpression.MULTARY(arguments, inv_arguments, op)
          then multaryByOperator(arguments, inv_arguments, op, graph);
        case NFExpression.BINARY(exp1, op, exp2)
          then binaryByOperator(exp1, exp2, op, graph);
        case NFExpression.UNARY(op, exp1)
          then unaryByOperator(exp1, op, graph);
        case NFExpression.REAL(num)
          then EGraph.add(ENode.NUM(num), graph);
        case NFExpression.INTEGER(i)
          then EGraph.add(ENode.NUM(intReal(i)), graph);
        case NFExpression.CREF(cref = cref)
          then EGraph.add(ENode.SYMBOL(cref), graph);
        else algorithm Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed for expression: " + NFExpression.toString(exp)});
          then fail();
      end match;
    end newFromExp;

    function add
      "Adds an Enode to the EGraph. If the node is already in the EGraph, returns the Enodes id,
      otherwise adds the id to both maps and extends the unionfind."
      input ENode node;
      input output EGraph graph;
      output EClassId id;
    protected
      UnionFind temp;
      UnorderedSet<ENode> nodeSet;
      EClass child_class;
      EClassId child_id, numid;
      Option<Real> optnum;
      Real num;
    algorithm
      try
        SOME(id) := UnorderedMap.get(node, graph.hashcons);
      else
        (temp, id) := UnionFind.make(graph.unionfind);
        graph.unionfind := temp;
        UnorderedMap.add(node, id, graph.hashcons);
        optnum := EGraph.getNum(graph, node);
        nodeSet := UnorderedSet.new<ENode>(ENode.hash, ENode.isEqual);
        UnorderedSet.add(node, nodeSet);
        UnorderedMap.add(id, ECLASS(nodeSet,{}, optnum), graph.eclasses);
        for child_id in ENode.children(node) loop
          child_id := EGraph.find(graph,child_id);
          child_class := UnorderedMap.getSafe(child_id,graph.eclasses);
          child_class.parents := (node,id) :: child_class.parents;
          UnorderedMap.add(child_id,child_class,graph.eclasses);
        end for;
        // analysis part
        if isSome(optnum) then
          SOME(num) := optnum;
          (graph, numid) := EGraph.add(ENode.NUM(num), graph);
          graph := EGraph.union(id, EGraph.find(graph,numid), graph);
        end if;
      end try;
    end add;

    function find
      "Returns the root element of an EClassId."
      input EGraph graph;
      input output EClassId id;
    algorithm
      id := UnionFind.find(graph.unionfind, id);
    end find;

    function union
      input EClassId id1;
      input EClassId id2;
      input output EGraph graph;
      output Boolean changed;
    protected
      EClassId new_id1,new_id2, classId;
      EClass class1,class2;
      UnionFind temp;
      Option<Real> num_new;
    algorithm
      (temp, new_id1, new_id2) := UnionFind.union(id1, id2, graph.unionfind);
      changed := new_id1 <> new_id2;
      if  changed then
        class1 :=  UnorderedMap.getSafe(new_id1, graph.eclasses);
        class2 :=  UnorderedMap.getSafe(new_id2, graph.eclasses);
        // short part for the analysis
        num_new := match (class1.num, class2.num)
          local
            Real num1, num2;
          case (NONE(), SOME(num2)) then SOME(num2);
          case (SOME(num1), NONE()) then SOME(num1);
          case (SOME(num1), SOME(num2)) algorithm
            if num1 <> num2 then // error case
              print("constants not equal error \n");
              fail();
            end if;
            then SOME(num1);
          else NONE();
        end match;
        // end of analysis part
        class1.parents := listAppend(class1.parents, class2.parents);
        for classId in UnorderedSet.toList(class2.nodes) loop
          UnorderedSet.add(classId, class1.nodes);    // ??
        end for;
        class1.num := num_new;
        UnorderedMap.add(new_id1, class1, graph.eclasses);
        graph.unionfind := temp;
        graph.worklist :=  new_id1 :: graph.worklist;
        graph.deletelist := id2 :: new_id2 :: graph.deletelist;
      end if;
    end union;

    function canonicalize
      "new children of an enode will become the root elements of the old children"
      input EGraph graph;
      input output ENode node;
    protected
      list<EClassId> new_ch;
    algorithm
      new_ch := list(EGraph.find(graph, id) for id in ENode.children(node));
      node := ENode.make(node, new_ch);
    end canonicalize;

    function rebuild
      input output EGraph graph;
    protected
      UnorderedSet<EClassId> todo;
      EClassId eclassid;
    algorithm
      todo := UnorderedSet.new<EClassId>(intMod,intEq);
      for eclassid in graph.worklist loop
        UnorderedSet.add(EGraph.find(graph, eclassid), todo);
      end for;
      graph := UnorderedSet.fold(todo, EGraph.repair, graph);
      graph.worklist := {};

      for eclassid in graph.deletelist loop
        UnorderedMap.remove(eclassid, graph.eclasses);
      end for;
      graph.deletelist := {};
    end rebuild;

    function repair
      input EClassId eclassid;
      input output EGraph graph;
    protected
      EClass elem,node_elem;
      ENode node;
      EClassId id;
      UnorderedMap<ENode,EClassId> new_parents;
    algorithm
      //elem := UnorderedMap.getSafe(EGraph.find(graph, eclassid), graph.eclasses);
      elem := UnorderedMap.getSafe(eclassid, graph.eclasses);
      for tup in elem.parents loop
        (node, id) := tup;
        node_elem := UnorderedMap.getSafe(EGraph.find(graph, id), graph.eclasses);
        UnorderedSet.remove(node, node_elem.nodes);
        UnorderedMap.remove(node, graph.hashcons);
        node := EGraph.canonicalize(graph, node);
        UnorderedMap.add(node, EGraph.find(graph, id), graph.hashcons);
        UnorderedSet.add(node, node_elem.nodes);
      end for;
      new_parents := UnorderedMap.new<EClassId>(ENode.hash, ENode.isEqual);
      //elem := UnorderedMap.getSafe(EGraph.find(graph, eclassid), graph.eclasses);
      elem := UnorderedMap.getSafe(eclassid, graph.eclasses);
      for tup in elem.parents loop
        (node, id) := tup;
        node := EGraph.canonicalize(graph, node);
        if UnorderedMap.contains(node, new_parents) then
          EGraph.union(id, UnorderedMap.getOrFail(node, new_parents), graph);
        end if;
        UnorderedMap.add(node, EGraph.find(graph, id), new_parents);
      end for;
      elem.parents := UnorderedMap.toList(new_parents);
      UnorderedMap.add(eclassid,elem,graph.eclasses);
    end repair;

    function getNum
      "Checks if a enode is actually a constant expression and returns Option of that value
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
        case (ENode.BINARY(id1, id2, bop)) algorithm
          id1 := EGraph.find(egraph,id1);
          id2 := EGraph.find(egraph,id2);
          eclass1 := UnorderedMap.getSafe(id1, egraph.eclasses);
          eclass2 := UnorderedMap.getSafe(id2, egraph.eclasses);
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
        case (ENode.UNARY(id1, uop)) algorithm
          id1 := EGraph.find(egraph,id1);
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
      EClassId temp_id;
      String out;
      list<String> tempList;
      Boolean b;
    algorithm
      allstrings := {};
      temp_id := EGraph.find(egraph, id);
      eclass := UnorderedMap.getOrFail(temp_id, egraph.eclasses);
      for node in UnorderedSet.toList(eclass.nodes) loop
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


    function sameRoot
      input EGraph egraph;
      input EClassId id1, id2;
      output Boolean equal;
    algorithm
      equal := EGraph.find(egraph, id1) == EGraph.find(egraph, id2);
    end sameRoot;

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
    print(intString(EGraph.find(egraph, baseId)) + "\n");
    bias := UnorderedMap.new<EClassId>(intMod,intEq);
    for cl in UnorderedMap.toList(egraph.eclasses) loop
      (classId, clazz) := cl;
      classId := EGraph.find(egraph, classId);
      biasValue := UnorderedMap.get(classId, bias);
      nodeId := match biasValue
        local
          Integer b;
        case SOME(b) then b;
        else 0;
      end match;
      for node in UnorderedSet.toList(clazz.nodes) loop
        nodeId := nodeId + 1;
        nodeStr := EGraph.nodeGraphDump(node, egraph);
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
          EClassId id1, id2;
          String opStr;
          ComponentRef cref;
          UnaryOp uop;
          BinaryOp bop;
        case ENode.NUM(x) then (realString(x) + ",,");
        case ENode.SYMBOL(cref) then (NFComponentRef.toString(cref) + ",,");
        case ENode.UNARY(id1, uop) then (unaryOpToString(uop) + "," + intString(id1) + ",");
        case ENode.BINARY(id1, id2, bop) then (binaryOpToString(bop) + "," + intString( id1) + ";" + intString(id2)  + ",");
        else fail();    // multary not implemented yet.
      end match;
    end nodeGraphDump;
  end EGraph;

  uniontype Extractor
  public
  import NFEGraph.*;
    record EXTRACTOR
      EGraph egraph;
      UnorderedMap<EClassId, ENode> best_nodes;
      UnorderedMap<EClassId, Integer> dist;
    end EXTRACTOR;

    function new
      input EGraph egraph;
      output Extractor extractor;
    algorithm
      extractor := Extractor.EXTRACTOR(egraph, UnorderedMap.new<ENode>(intMod,intEq), UnorderedMap.new<Integer>(intMod,intEq));
    end new;

    function extract
      input EClassId id;
      input output Extractor extractor;
      output Integer distance;
    protected
      EClass eclass;
      ENode node;
      EClassId temp_id;
    algorithm
      temp_id := EGraph.find(extractor.egraph,id);
      (distance, extractor) := match (UnorderedMap.get(temp_id, extractor.dist))
        local
          ENode  best_node;
          Integer current, best = 0, temp;
          Boolean first = true;
        case (SOME(current))
          then (current, extractor);
        else algorithm
          UnorderedMap.add(temp_id, UnorderedMap.size(extractor.egraph.hashcons), extractor.dist);
          temp_id := EGraph.find(extractor.egraph,temp_id);
          eclass := UnorderedMap.getOrFail(temp_id ,extractor.egraph.eclasses);
          for node in UnorderedSet.toList(eclass.nodes) loop
            current := 1;
            for class_child in ENode.children(node) loop
              (extractor, temp) := extract(class_child,extractor);
              current := temp + current;
            end for;
            if current < best or first then
              best := current;
              best_node := node;
              first := false;
            end if;
          end for;
          UnorderedMap.add(temp_id, best, extractor.dist);
          UnorderedMap.add(temp_id, best_node, extractor.best_nodes);

          then (best,extractor);
        end match;
    end extract;

    function build
      input EClassId start;
      input Extractor extractor;
      output NFExpression exp;
    protected
      EClassId temp_start;
      ENode node;
    algorithm
      temp_start := EGraph.find(extractor.egraph,start);
      node := UnorderedMap.getOrFail(temp_start,extractor.best_nodes);
      exp := match node
        local
          Real num;
          EClassId id1,id2;
          UnaryOp uop;
          BinaryOp bop;
          ComponentRef cref;
        case ENode.NUM(num)
          then NFExpression.REAL(num);
        case ENode.SYMBOL(cref)
          then NFExpression.CREF(NFType.REAL(), cref);
        case ENode.UNARY(id1, uop) guard(not compareUnaryOp(uop, UnaryOp.UDIV))
          then NFExpression.UNARY(
            unaryOpToNFOperator(uop),
            Extractor.build(id1,extractor));
        case ENode.UNARY(id1, uop) guard(compareUnaryOp(uop, UnaryOp.UDIV))
          then NFExpression.BINARY(
            NFExpression.REAL(1),
            NFOperator.makeDiv(NFType.REAL()),
            Extractor.build(id1,extractor));
        case ENode.BINARY(id1,id2,bop)
          then NFExpression.BINARY(
            Extractor.build(id1,extractor),
            binaryOpToNFOperator(bop),
            Extractor.build(id2,extractor));
        else algorithm
          print("Else Error \n");
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
      BinaryOp bop;
    end BINARY;

    record UNARY
      Pattern child;
      UnaryOp uop;
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
            then Pattern.BINARY(p1, p2, bop);
          case (_, SOME(uop)) algorithm
            sr := StringReader.consumeSpaces(sr);
            (sr, vars, p1) := fromStringHelper(sr, vars);
            sr := StringReader.consumeSpaces(sr);
            (sr, char) := StringReader.consume(sr);
            if char <> stringCharInt(")") then
              print("missing ')' \n");
              fail();
            end if;
            then Pattern.UNARY(p1, uop);
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
        pattern := Pattern.NUM(num);
      elseif char == stringCharInt("-") then
        num := 0;
        while isNumeric(StringReader.getNext(sr)) loop
          (sr, char) := StringReader.consume(sr);
          num := 10*num  + char - stringCharInt("0");
        end while;
        pattern := Pattern.NUM(-num);
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
        case Pattern.VAR(varId)
          then 17*varId + 1000;
        case Pattern.NUM(num)
          then 13*(realInt(num) + 7);
        case Pattern.SYMBOL(str)
          then stringHashDjb2Mod(str, mod);
        case Pattern.BINARY(temp_pattern1, temp_pattern2, bop)
          then hash(temp_pattern1, mod) + hash(temp_pattern2, mod) + NFEGraph.hashBinaryOp(bop);
        case Pattern.UNARY(temp_pattern1, uop)
          then hash(temp_pattern1, mod) + NFEGraph.hashUnaryOp(uop);
      end match;
    end hash;

    function matchPattern
      input EClassId id;
      input EGraph egraph;
      input Pattern pattern;
      input list<UnorderedMap<Integer, EClassId>> subs_in = {UnorderedMap.new<EClassId>(intMod,intEq)};
      output list<UnorderedMap<Integer, EClassId>> subs_out;
    protected
      EClass eclass;
      EClassId root_id;
      UnorderedMap<Integer, EClassId> temp_map;
      list<UnorderedMap<Integer, EClassId>> temp_list,node_list;
    algorithm
      root_id := EGraph.find(egraph,id);
      eclass := UnorderedMap.getOrFail(root_id,egraph.eclasses);
      subs_out := {};
      for node in UnorderedSet.toList(eclass.nodes) loop
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
          case (Pattern.NUM(num1), ENode.NUM(num2)) algorithm
            if num1 == num2 then temp_list := node_list; else temp_list := {}; end if;
            then temp_list;
          /*case (Pattern.SYMBOL(str1), ENode.SYMBOL(str2)) algorithm
            // case to insure that a hard coded symbol in the pattern corresponds to a enode symbol
            // special case of VAR
            if str1 == str2 then temp_list := node_list; else temp_list := {}; end if;
            then temp_list;*/ // TODO MAYBE
          // simple recursion
          case (Pattern.BINARY(temp_pattern1,temp_pattern2,bop1),ENode.BINARY(temp_id1,temp_id2,bop2))
            guard(bop1 == bop2)
            then matchPattern(temp_id2,egraph,temp_pattern2, matchPattern(temp_id1,egraph,temp_pattern1,node_list));
          case (Pattern.UNARY(temp_pattern1,uop1),ENode.UNARY(temp_id1,uop2))
            guard(uop1 == uop2) then matchPattern(temp_id1,egraph,temp_pattern1,node_list);
          else {};
        end match;
        subs_out := listAppend(node_list,subs_out);
      end for;
    end matchPattern;

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
          Real num;
          EClassId id1, id2;
          BinaryOp bop;
          UnaryOp uop;
          Pattern temp_pattern1,temp_pattern2;
          String str;
        case Pattern.NUM(num) then EGraph.add(ENode.NUM(num), egraph);
        //case Pattern.SYMBOL(str) then EGraph.add(ENode.SYMBOL(str), egraph); TODO MAYBE
        case Pattern.BINARY(temp_pattern1, temp_pattern2, bop)
          algorithm
          (egraph, id1) := apply(temp_pattern1, sub, egraph);
          (egraph, id2) := apply(temp_pattern2, sub, egraph);
          then EGraph.add(ENode.BINARY(EGraph.find(egraph,id1), EGraph.find(egraph,id2), bop), egraph);
        case Pattern.UNARY(temp_pattern1, uop)
          algorithm
          (egraph, id1) := apply(temp_pattern1, sub, egraph);
          then EGraph.add(ENode.UNARY(EGraph.find(egraph,id1), uop), egraph);
        case Pattern.VAR(varId) then
          (egraph, UnorderedMap.getOrFail(varId, sub));
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

    record RULEAPPLIER
      list<Rule> rules;
    end RULEAPPLIER;

    function matchApplyRules
      input RuleApplier ruleapplier;
      input output EGraph egraph;
      output Boolean saturated;
    protected
      list<tuple<Rule, EClassId, list<UnorderedMap<Integer, EClassId>>>> subs;
      tuple<Rule, EClassId, list<UnorderedMap<Integer, EClassId>>> tup;
      list<UnorderedMap<Integer, EClassId>> subs_part;
      UnorderedMap<Integer, EClassId> map;
      EClassId exId, newId;
      Rule rule;
      Boolean changed;
      UnorderedSet<EClassId> visited;
    algorithm
      // 1st phase: matching of all rules with all eclasses
      subs := {};
      //print("--matching rules--\n");
      for rule in ruleapplier.rules loop
        // print("match rule name: " + rule.name + "\n");
        visited := UnorderedSet.new<EClassId>(intMod,intEq);
        for exId in UnorderedMap.keyList(egraph.eclasses) loop
          exId := EGraph.find(egraph, exId);
          if not UnorderedSet.contains(exId,visited) then
            UnorderedSet.add(exId,visited);
            subs_part := Pattern.matchPattern(exId, egraph, rule.pattern_in);
            subs := match subs_part
              case {} then subs;
              else (rule, exId, subs_part) :: subs;
            end match;
          end if;
        end for;
      end for;
      // 2nd phase: applying of the found patterns
      saturated := true;
      changed := false;
      //print("--applying rules--\n");
      for tup in subs loop
        (rule, exId, subs_part) := tup;
        for map in subs_part loop
          (egraph, newId) := Pattern.apply(rule.pattern_out, map, egraph);
          (egraph, changed) := EGraph.union(exId, newId, egraph);
          if changed then
            //print("apply rule name: " + rule.name + "\n");
          end if;
          saturated := saturated and (not changed);
        end for;
      end for;
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
      "Adds multiple rules to an applier: {{(+ ?a 0), ?a, neutral-add},{(+ ?a ?b), (+ ?b ?a), comm-add}}"
      input output RuleApplier ra;
      input list<list<String>> rules;
    protected
      list<String> strrule;
      String strp1, strp2, name;
    algorithm
      for strrule in rules loop
        {strp1, strp2, name} := strrule;
        ra.rules := Rule.fromString(strp1, strp2, name) :: ra.rules;
      end for;
    end addRules;
  end RuleApplier;

  uniontype StringReader
    record STRINGSTATE
      Integer bias;
      String string;
    end STRINGSTATE;

    function new
      input String str;
      output StringReader reader = STRINGSTATE(0, str);
    end new;

    function consume
      input output StringReader sr;
      output Integer char;
    algorithm
      sr.bias := sr.bias + 1;
      if sr.bias > stringLength(sr.string) then
        char := -1;
      else
        char := stringGet(sr.string, sr.bias);
      end if;
    end consume;

    function getNext
      input StringReader sr;
      output Integer char;
    protected
      Integer bias;
    algorithm
      bias := sr.bias + 1;
      if bias > stringLength(sr.string) then
        char := -1;
      else
        char := stringGet(sr.string, bias);
      end if;
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
    output Boolean bool;
  algorithm
    // stringCharInt("a") <= char <= stringCharInt("z")
    if 97 <= char and char <= 122 then bool := true; else bool := false;
    end if;
  end isAlpha;

  function isNumeric
    input Integer char;
    output Boolean bool;
  algorithm
    // stringCharInt("0") <= char <= stringCharInt("9")
    if 48 <= char and char <= 57 then bool := true; else bool := false;
    end if;
  end isNumeric;

  function operatorType
    input String strOp;
    output Option<BinaryOp> bop;
    output Option<UnaryOp> uop;
  algorithm
    bop := NONE();
    uop := NONE();
    if stringEqual("+", strOp) then bop := SOME(BinaryOp.ADD);
    elseif stringEqual("*", strOp) then bop := SOME(BinaryOp.MUL);
    elseif stringEqual("^", strOp) then bop := SOME(BinaryOp.POW);
    elseif stringEqual("-", strOp) then uop := SOME(UnaryOp.UMINUS);
    elseif stringEqual("/", strOp) then uop := SOME(UnaryOp.UDIV);
    end if;
  end operatorType;
  annotation(__OpenModelica_Interface="frontend");
end NFEGraph;
