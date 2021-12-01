encapsulated package NFEGraph
    import DisjointSets;
    import UnorderedMap;
    import UnorderedSet;
public
    type EClassId = Integer;


    encapsulated uniontype ENode
    import NFEGraph.*;
    public
        record NUM
            Integer num;
        end NUM;

        record ADD
            EClassId id1;
            EClassId id2;
        end ADD;

        function isEqual
            input ENode node1;
            input ENode node2;
            output Boolean isEqual;
        algorithm
            isEqual := match (node1,node2)
                local
                    Integer num1,num2;
                    EClassId id1_1,id1_2,id2_1,id2_2;
                case (ENode.NUM(num1),ENode.NUM(num2))
                    then num1 == num2;
                case (ENode.ADD(id1_1,id1_2),ENode.ADD(id2_1,id2_2))
                    then id1_1 == id2_1 and id1_2 == id2_2;
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
                    Integer num;
                    EClassId id1, id2;
                case NUM(num) then intMod(num, mod);
                case ADD(id1, id2) then intMod(100 + id1 * 10 + id2, mod);
            end match;
        end hash;

        function children
            input ENode node;
            output list<EClassId> childrenList;
        algorithm
            childrenList := match node
                local
                    EClassId id1,id2;
                case (ENode.ADD(id1,id2))
                    then {id1,id2};
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
                case NUM(_) then oldEnode;
                case ADD(_, _) then ADD(listGet(children,1),listGet(children,2));
            end match;
        end make;
    end ENode;

    uniontype EClass
    import NFEGraph.*;
    public
        record ECLASS
            array<ENode> nodes;
            list<tuple<ENode,EClassId>> parents;
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
            while not (index == unionfind.nodes[index]) loop
                index := unionfind.nodes[index];
            end while;
        end find;

        function union
            input Integer index1;
            input Integer index2;
            input output UnionFind unionfind;
            output Integer root1;
        protected
            Integer root2;
        algorithm
            root1 := find(unionfind, index1);
            root2 := find(unionfind, index2);
            if not (root1 == root2) then
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
        end EGRAPH;

        function new
            output EGraph egraph;
        algorithm
            egraph := EGraph.EGRAPH(UnorderedMap.new<EClassId>(ENode.hash, ENode.isEqual),UnionFind.new(),UnorderedMap.new<EClass>(intMod,intEq),{});
        end new;

        function add
            "Adds an Enode to the EGraph. If the node is already in the EGraph returns the Enodes id,
            otherwise adds the id to both maps and extends the unionfind."
            input ENode node;
            input output EGraph graph;
            output EClassId id;
        protected
            UnionFind temp;
            EClass child_class;
            EClassId child_id;
        algorithm
            try
                SOME(id) := UnorderedMap.get(node, graph.hashcons);
            else
                (temp, id) := UnionFind.make(graph.unionfind);
                graph.unionfind := temp;
                UnorderedMap.add(node, id, graph.hashcons);
                UnorderedMap.add(id, ECLASS(arrayCreate(1, node),{}), graph.eclasses);

                for child_id in ENode.children(node) loop
                    child_class := UnorderedMap.getSafe(child_id,graph.eclasses);
                    child_class.parents := (node,id) :: child_class.parents;
                    UnorderedMap.add(child_id,child_class,graph.eclasses);
                end for;
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
        protected
            EClassId new_id;
            UnionFind temp;
        algorithm
            (temp,new_id) := UnionFind.union(id1, id2, graph.unionfind);
            graph.unionfind := temp;
            graph.worklist :=  new_id :: graph.worklist;
        end union;

        function canonicalize
        // new children of an enode will become the root elements of the old children
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
        end rebuild;

        function repair
            input EClassId eclassid;
            input output EGraph graph;
        protected
            EClass elem;
            ENode node;
            EClassId id;
            UnorderedMap<ENode,EClassId> new_parents;
        algorithm
            elem := UnorderedMap.getOrFail(eclassid, graph.eclasses);
            for tup in elem.parents loop
                (node, id) := tup;
                UnorderedMap.remove(node, graph.hashcons);
                node := EGraph.canonicalize(graph, node);
                UnorderedMap.add(node, EGraph.find(graph, id), graph.hashcons);
            end for;
            new_parents := UnorderedMap.new<EClassId>(ENode.hash, ENode.isEqual);

            elem := UnorderedMap.getOrFail(eclassid, graph.eclasses);
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
    end EGraph;

    annotation(__OpenModelica_Interface="frontend");
end NFEGraph;