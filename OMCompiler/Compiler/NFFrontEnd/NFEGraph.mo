encapsulated package NFEGraph
    import UnorderedMap;
    import UnorderedSet;
    import Array;
    import NFExpression;
public
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
        end match;
    end binaryOpToNFOperator;

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
            Integer num;
        end NUM;

        record SYMBOL
            String str;
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
                    Integer num1,num2;
                    EClassId id1_1,id1_2,id2_1,id2_2;
                    BinaryOp bop1, bop2;
                    UnaryOp uop1, uop2;
                case (ENode.NUM(num1),ENode.NUM(num2))
                    then num1 == num2;
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
                    Integer num;
                    EClassId id1, id2;
                    BinaryOp bop;
                    UnaryOp uop;
                    String symbol;
                case SYMBOL(symbol) then stringHashDjb2Mod(symbol, mod);
                case NUM(num) then intMod(num, mod);
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
                case BINARY(_, _, bop) then BINARY(listGet(children,1),listGet(children,2), bop);
                case UNARY(_, uop) then UNARY(listGet(children, 1), uop);
            end match;
        end make;
    end ENode;

    uniontype EClass
    import NFEGraph.*;
    public
        record ECLASS
            list<ENode> nodes;
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
            output Integer root2;
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
                UnorderedMap.add(id, ECLASS({node},{}), graph.eclasses);

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
            output Boolean changed;
        protected
            EClassId new_id1,new_id2;
            EClass class1,class2;
            UnionFind temp;
        algorithm
            (temp,new_id1,new_id2) := UnionFind.union(id1, id2, graph.unionfind);

            changed := not (new_id1 == new_id2);

            if  changed then

                class1 :=  UnorderedMap.getOrFail(new_id1, graph.eclasses);
                class2 :=  UnorderedMap.getOrFail(new_id2, graph.eclasses);

                class1.parents := listAppend(class1.parents, class2.parents);
                class1.nodes := listAppend(class1.nodes, class2.nodes);

                UnorderedMap.add(new_id1, class1, graph.eclasses);

                graph.unionfind := temp;
                graph.worklist :=  new_id1 :: graph.worklist;
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
                    eclass := UnorderedMap.getOrFail(temp_id ,extractor.egraph.eclasses);
                    for node in eclass.nodes loop
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
                    Integer num;
                    EClassId id1,id2;
                    BinaryOp bop;

                case ENode.NUM(num)
                    then NFExpression.INTEGER(num);

                case ENode.BINARY(id1,id2,bop)
                    then NFExpression.BINARY(
                        Extractor.build(id1,extractor),
                        binaryOpToNFOperator(bop),
                        Extractor.build(id2,extractor));
            end match;
        end build;



    end Extractor;

    encapsulated uniontype Pattern
    import NFEGraph.*;
    public

        record NUM
            Integer value;
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

        function matchPattern
            input EClassId id;
            input EGraph egraph;
            input Pattern pattern;
            input list<UnorderedMap<Integer, EClassId>> subs_in = {UnorderedMap.new<EClassId>(intMod,intEq)};
            output list<UnorderedMap<Integer, EClassId>> subs_out;
        protected
            EClass eclass;
            UnorderedMap<Integer, EClassId> temp_map;
            list<UnorderedMap<Integer, EClassId>> temp_list,node_list;
        algorithm
            eclass := UnorderedMap.getOrFail(EGraph.find(egraph,id),egraph.eclasses);
            subs_out := {};
            for node in eclass.nodes loop
                node_list := {};

                for map in subs_in loop
                    node_list := UnorderedMap.copy(map) :: node_list;
                end for;

                node_list :=  match (pattern, node)
                    local
                        Integer varId, num1, num2;
                        BinaryOp bop1,bop2;
                        UnaryOp uop1,uop2;
                        EClassId temp_id1,temp_id2;
                        Pattern temp_pattern1,temp_pattern2;
                        String str1, str2;
                        Boolean ok;

                    case (Pattern.VAR(varId), _)
                        // case for some common subexpression: e.g. (3*x + 1) + (3*x + 1) -> 2 * (3*x + 1)
                        algorithm
                            temp_list := {};
                            for temp_map in node_list loop
                                ok := match UnorderedMap.get(varId,temp_map)
                                    case SOME(temp_id1) then temp_id1 == id;
                                    else algorithm
                                        UnorderedMap.add(varId,id,temp_map);
                                    then true;
                                end match;

                                if ok then
                                    temp_list := temp_map :: temp_list;
                                end if;
                            end for;

                        then temp_list;

                    case (Pattern.NUM(num1), ENode.NUM(num2))
                        // case to insure that a number in the pattern corresponds to a enode number
                        algorithm
                        if num1 == num2 then temp_list := node_list; else temp_list := {}; end if;
                        then temp_list;

                    case (Pattern.SYMBOL(str1), ENode.SYMBOL(str2))
                        // case to insure that a hard coded symbol in the pattern corresponds to a enode symbol
                        // special case of VAR
                        algorithm
                        if str1 == str2 then temp_list := node_list; else temp_list := {}; end if;
                        then temp_list;

                    // simple recursion
                    case (Pattern.BINARY(temp_pattern1,temp_pattern2,bop1),ENode.BINARY(temp_id1,temp_id2,bop2))
                        guard(bop1 == bop2)
                        algorithm
                        then matchPattern(temp_id2,egraph,temp_pattern2, matchPattern(temp_id1,egraph,temp_pattern1,node_list));

                    case (Pattern.UNARY(temp_pattern1,uop1),ENode.UNARY(temp_id1,uop2))
                        guard(uop1 == uop2) then matchPattern(temp_id1,egraph,temp_pattern1,node_list);
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
                Integer varId, num;
                EClassId id1, id2;
                BinaryOp bop;
                UnaryOp uop;
                Pattern temp_pattern1,temp_pattern2;
                String str;
            case Pattern.NUM(num) then EGraph.add(ENode.NUM(num), egraph);
            case Pattern.SYMBOL(str) then EGraph.add(ENode.SYMBOL(str), egraph);
            case Pattern.BINARY(temp_pattern1, temp_pattern2, bop)
                algorithm
                (egraph, id1) := apply(temp_pattern1, sub, egraph);
                (egraph, id2) := apply(temp_pattern2, sub, egraph);
                then EGraph.add(ENode.BINARY(id1, id2, bop), egraph);
            case Pattern.UNARY(temp_pattern1, uop)
                algorithm
                (egraph, id1) := apply(temp_pattern1, sub, egraph);
                then EGraph.add(ENode.UNARY(id1, uop), egraph);
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
        end RULE;

        function matchPattern
            input Rule rule;
            input EClassId id;
            input EGraph egraph;
            output list<UnorderedMap<Integer, EClassId>> subs_out;
        algorithm
        subs_out := Pattern.matchPattern(id, egraph, rule.pattern_in);
        end matchPattern;

    end Rule;
    annotation(__OpenModelica_Interface="frontend");
end NFEGraph;