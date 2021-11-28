encapsulated package NFEGraph
    import DisjointSets;
    import UnorderedMap;
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
    end ENode;

    uniontype EClass
    import NFEGraph.*;
    public
        record ECLASS
            array<ENode> nodes;
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
        protected
            Integer root1, root2;
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
        end EGRAPH;

        function new
            output EGraph egraph;
        algorithm
            egraph := EGraph.EGRAPH(UnorderedMap.new<EClassId>(ENode.hash,ENode.isEqual),UnionFind.new(),UnorderedMap.new<EClass>(intMod,intEq));
        end new;

        function add
            "Adds an Enode to the EGraph. If the node is already in the EGraph returns the Enodes id,
            otherwise adds the id to both maps and extends the unionfind."
            input ENode node;
            input output EGraph graph;
            output EClassId id;
        protected
            UnionFind temp;
        algorithm
            try
                SOME(id) := UnorderedMap.get(node, graph.hashcons);
            else
                (temp, id) := UnionFind.make(graph.unionfind);
                graph.unionfind := temp;
                UnorderedMap.add(node, id, graph.hashcons);
                UnorderedMap.add(id, ECLASS(arrayCreate(1, node)), graph.eclasses);
            end try;
        end add;

        function find
            "Returns the root element of an EClassId."
            input EGraph graph;
            input output  EClassId id;
        algorithm
            id := UnionFind.find(graph.unionfind, id);
        end find;

        function union
            input EClassId id1;
            input EClassId id2;
            input output EGraph graph;
        algorithm
            UnionFind.union(id1, id2, graph.unionfind);
        end union;
    end EGraph;



    annotation(__OpenModelica_Interface="frontend");
end NFEGraph;