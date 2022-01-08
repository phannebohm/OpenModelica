encapsulated package NFEGraph
    import UnorderedMap;
    import UnorderedSet;
    import Array;
    import NFExpression;
public

    //TODO: Parsing of NFExpression to ENode
    //     + better hashes
    //     + printing of enodes/eclasses

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
            Real num;
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
                    Real num1,num2;
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
                    Real num;
                    EClassId id1, id2;
                    BinaryOp bop;
                    UnaryOp uop;
                    String symbol;
                case SYMBOL(symbol) then stringHashDjb2Mod(symbol, mod);
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
            list<ENode> nodes;
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
            "Adds an Enode to the EGraph. If the node is already in the EGraph, returns the Enodes id,
            otherwise adds the id to both maps and extends the unionfind."
            input ENode node;
            input output EGraph graph;
            output EClassId id;
        protected
            UnionFind temp;
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
                UnorderedMap.add(id, ECLASS({node},{}, optnum), graph.eclasses);
                for child_id in ENode.children(node) loop
                    child_class := UnorderedMap.getSafe(child_id,graph.eclasses);
                    child_class.parents := (node,id) :: child_class.parents;
                    UnorderedMap.add(child_id,child_class,graph.eclasses);
                end for;
                // analysis part
                if isSome(optnum) then
                    SOME(num) := optnum;
                    (graph, numid) := EGraph.add(ENode.NUM(num), graph);
                    graph := EGraph.union(id, numid, graph);
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
            EClassId new_id1,new_id2;
            EClass class1,class2;
            UnionFind temp;
            Option<Real> num_new;
        algorithm
            (temp, new_id1, new_id2) := UnionFind.union(id1, id2, graph.unionfind);
            changed := not (new_id1 == new_id2);
            if  changed then
                class1 :=  UnorderedMap.getOrFail(new_id1, graph.eclasses);
                class2 :=  UnorderedMap.getOrFail(new_id2, graph.eclasses);
                // short part for the analysis
                num_new := match (class1.num, class2.num)
                    local
                        Real num1, num2;
                    case (NONE(), SOME(num2)) then SOME(num2);
                    case (SOME(num1), NONE()) then SOME(num1);
                    case (SOME(num1), SOME(num2)) algorithm
                        if not(num1 == num2) then // error case
                            print("constants not equal error");
                            fail();
                        end if;
                        then SOME(num1);
                    else NONE();
                end match;
                // end of analysis part
                class1.parents := listAppend(class1.parents, class2.parents);
                class1.nodes := listAppend(class1.nodes, class2.nodes);
                class1.num := num_new;
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
                    eclass1 := UnorderedMap.getOrFail(id1, egraph.eclasses);
                    eclass2 := UnorderedMap.getOrFail(id2, egraph.eclasses);
                    if not(isNone(eclass1.num)) and not (isNone(eclass2.num)) then
                        SOME(num1) := eclass1.num;
                        SOME(num2) := eclass2.num;
                        numtemp := match bop
                            case BinaryOp.ADD then
                                SOME(num1 + num2);
                            case BinaryOp.MUL then
                                SOME(num1 * num2);
                            case BinaryOp.POW then
                                SOME(num1 ^ num2);
                            else NONE();
                        end match;
                    else numtemp := NONE();
                    end if;
                    then numtemp;
                case (ENode.UNARY(id1, uop)) algorithm
                    eclass1 := UnorderedMap.getOrFail(id1, egraph.eclasses);
                    if not(isNone(eclass1.num)) then
                        SOME(num1) := eclass1.num;
                        numtemp := match uop
                            case UnaryOp.UDIV guard (not (num1 == 0)) then
                                SOME(1/num1);
                            case UnaryOp.UMINUS then
                                SOME(-num1);
                            else NONE();
                        end match;
                    else numtemp :=  NONE();
                    end if;
                    then numtemp;
                case ENode.SYMBOL(_) then NONE();
                case ENode.NUM(num1) then SOME(num1);
                else NONE();
            end match;
        end getNum;
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
                    Real num;
                    EClassId id1,id2;
                    BinaryOp bop;
                    String sym;
                case ENode.NUM(num)
                    then NFExpression.REAL(num);
                case ENode.SYMBOL(sym)
                    then NFExpression.STRING(sym);

                case ENode.BINARY(id1,id2,bop)
                    then NFExpression.BINARY(
                        Extractor.build(id1,extractor),
                        binaryOpToNFOperator(bop),
                        Extractor.build(id2,extractor));
                else algorithm
                    print("Else Error");
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
                while not (StringReader.getNext(sr) == 32) loop // whitespace
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
                        if not (char == stringCharInt(")"))
                            then fail();
                        end if;
                        then Pattern.BINARY(p1, p2, bop);
                    case (_, SOME(uop)) algorithm
                        sr := StringReader.consumeSpaces(sr);
                        (sr, vars, p1) := fromStringHelper(sr, vars);
                        sr := StringReader.consumeSpaces(sr);
                        if not (char == stringCharInt(")"))  then
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
            for node in eclass.nodes loop
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
                        // case to insure that a number in the pattern corresponds to a enode number
                        if num1 == num2 then temp_list := node_list; else temp_list := {}; end if;
                        then temp_list;
                    case (Pattern.SYMBOL(str1), ENode.SYMBOL(str2)) algorithm
                        // case to insure that a hard coded symbol in the pattern corresponds to a enode symbol
                        // special case of VAR
                        if str1 == str2 then temp_list := node_list; else temp_list := {}; end if;
                        then temp_list;
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
                case Pattern.SYMBOL(str) then EGraph.add(ENode.SYMBOL(str), egraph);
                case Pattern.BINARY(temp_pattern1, temp_pattern2, bop)
                    algorithm
                    // find of ids?
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
            String name;
        end RULE;

        function hash
            input Rule rule;
            input Integer mod;
            output Integer out;
        algorithm
            out :=  intMod(Pattern.hash(rule.pattern_in, mod) + 10*Pattern.hash(rule.pattern_out, mod) + 1, mod);
        end hash;

        function isEqual
            input Rule rule1, rule2;
            output Boolean equal;
        algorithm
            equal := (Rule.hash(rule1, 1000) == Rule.hash(rule2, 1000));
        end isEqual;

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
        algorithm
            // 1st phase: matching of all rules with all eclasses
            subs := {};
            print("--matching rules--\n");
            for rule in ruleapplier.rules loop
                print("match rule name: " + rule.name + "\n");
                for exId in UnorderedMap.keyList(egraph.eclasses) loop
                    subs_part := Pattern.matchPattern(exId, egraph, rule.pattern_in);
                    subs := match subs_part
                        case {} then subs;
                        else (rule, exId, subs_part) :: subs;
                    end match;
                end for;
            end for;
            // 2nd phase: applying of the found patterns
            saturated := true;
            changed := false;
            print("--applying rules--\n");
            for tup in subs loop
                (rule, exId, subs_part) := tup;
                for map in subs_part loop
                    (egraph, newId) := Pattern.apply(rule.pattern_out, map, egraph);
                    (egraph, changed) := EGraph.union(exId, newId, egraph);
                    if changed then
                      print("apply rule name: " + rule.name + "\n");
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
