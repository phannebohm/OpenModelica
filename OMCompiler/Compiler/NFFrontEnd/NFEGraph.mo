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
                case NUM(num) then intMod(num,mod);
                case ADD(id1,id2) then intMod(100 + id1 * 10 + id2,mod);
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
        protected
            array<Integer> nodes;
            Integer nodeCount;
        algorithm
            UNION_FIND(nodes,nodeCount) := unionfind;

            nodeCount := nodeCount + 1;
            index := nodeCount;

            if (arrayLength(nodes) < nodeCount) then
                nodes := Array.expand(realInt(intReal(index) * 1.4), nodes, -1);
            end if;

            nodes[index] := index;

            unionfind := UNION_FIND(nodes,nodeCount);
        end make;
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
            input ENode node;
            input output EGraph graph;
            output EClassId id;
        protected
            UnorderedMap<ENode,EClassId> hashcons;
            UnionFind unionfind;
            UnorderedMap<EClassId,EClass> eclasses;
            EClass eclass;
        algorithm
            EGRAPH(hashcons,unionfind,eclasses) := graph;

            try
                SOME(id) := UnorderedMap.get(node,hashcons);
            else
                eclass := ECLASS(arrayCreate(1,node));

                (unionfind,id) := UnionFind.make(unionfind);


                graph := EGRAPH(hashcons,unionfind,eclasses);
            end try;
        end add;
    end EGraph;



    annotation(__OpenModelica_Interface="frontend");
end NFEGraph;