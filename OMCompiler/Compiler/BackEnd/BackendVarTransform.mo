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

encapsulated package BackendVarTransform
" file:        BackendVarTransform.mo
  package:     BackendVarTransform
  description: BackendVarTransform contains a Binary Tree representation of variable replacements.


  This module contain a Binary tree representation of variable replacements
  along with some functions for performing replacements of variables in equations"

public import BackendDAE;
public import DAE;
public import UnorderedMap;
public import UnorderedSet;

protected import Absyn;
protected import BackendDAETransform;
protected import BaseHashSet;
protected import BackendEquation;
protected import BackendVariable;
protected import ClassInf;
protected import ComponentReference;
protected import DAEUtil;
protected import Debug;
protected import DoubleEnded;
protected import ElementSource;
protected import Expression;
protected import ExpressionDump;
protected import ExpressionSimplify;
protected import Flags;
protected import HashSet;
protected import List;
protected import Util;
protected import MetaModelica.Dangerous.listReverseInPlace;

public
type ExpOpt = Option<DAE.Exp>;
type CrefExpTable = UnorderedMap<DAE.ComponentRef, ExpOpt>;
type CrefList = list<DAE.ComponentRef>;
type CrefListOpt = Option<CrefList>;
type CrefCrefListTable = UnorderedMap<DAE.ComponentRef, CrefListOpt>;
type CrefSet = UnorderedSet<DAE.ComponentRef>;

uniontype VariableReplacements
"VariableReplacements consists of a mapping between variables and expressions, the first binary tree of this type.
 To eliminate a variable from an equation system a replacement rule varname->expression is added to this
 datatype.
 To be able to update these replacement rules incrementally a backward lookup mechanism is also required.
 For instance, having a rule a->b and adding a rule b->c requires to find the first rule a->b and update it to
 a->c. This is what the second binary tree is used for."
  record REPLACEMENTS
    CrefExpTable hashTable "src -> dst, used for replacing. src is variable, dst is expression.";
    CrefCrefListTable invHashTable "dst -> list of sources. dst is a variable, sources are variables.";
    CrefSet extendhashTable "src -> nothing, used for extend arrays and records.";
    list<DAE.Ident> iterationVars "this are the implicit declerate iteration variables for for and range expressions";
    Option<CrefExpTable> derConst "this is used if states are constant to replace der(state) with 0.0";
  end REPLACEMENTS;

end VariableReplacements;

partial function FuncTypeExp_ExpToBoolean
  input DAE.Exp inExp;
  output Boolean outBoolean;
end FuncTypeExp_ExpToBoolean;

function newCrefExpTable
  output CrefExpTable table = UnorderedMap.new<ExpOpt>(ComponentReference.hashComponentRef, ComponentReference.crefEqual);
end newCrefExpTable;

function newCrefExpTableSized
  input Integer size;
  output CrefExpTable table = UnorderedMap.new<ExpOpt>(ComponentReference.hashComponentRef, ComponentReference.crefEqual, size);
end newCrefExpTableSized;

function newCrefCrefListTable
  output CrefCrefListTable table = UnorderedMap.new<CrefListOpt>(ComponentReference.hashComponentRef, ComponentReference.crefEqual);
end newCrefCrefListTable;

function newCrefCrefListTableSized
  input Integer size;
  output CrefCrefListTable table = UnorderedMap.new<CrefListOpt>(ComponentReference.hashComponentRef, ComponentReference.crefEqual, size);
end newCrefCrefListTableSized;

function newCrefSet
  output CrefSet set = UnorderedSet.new(ComponentReference.hashComponentRef, ComponentReference.crefEqual);
end newCrefSet;

function newCrefSetSized
  input Integer size;
  output CrefSet set = UnorderedSet.new(ComponentReference.hashComponentRef, ComponentReference.crefEqual, size);
end newCrefSetSized;

public function emptyReplacements "
  Returns an empty set of replacement rules
"
  output VariableReplacements outVariableReplacements =
    REPLACEMENTS(newCrefExpTable(), newCrefCrefListTable(), newCrefSet(), {}, NONE());
end emptyReplacements;

public function emptyReplacementsSized "Returns an empty set of replacement rules, giving a size of hashtables to allocate"
  input Integer size;
  output VariableReplacements outVariableReplacements =
    REPLACEMENTS(newCrefExpTableSized(size), newCrefCrefListTableSized(size), newCrefSetSized(size), {}, NONE());
end emptyReplacementsSized;

public function removeReplacement
  "Removes the replacement for a given key. The extendhashtable is not updated."
  input VariableReplacements repl;
  input DAE.ComponentRef inSrc;
protected
  Option<DAE.Exp> dst_opt;
  DAE.Exp dst;
algorithm
  dst_opt := UnorderedMap.getOrDefault(inSrc, repl.hashTable, NONE());

  if isNone(dst_opt) then
    return;
  end if;

  try
    // Replace the value with NONE() to mark it as deleted.
    UnorderedMap.add(inSrc, NONE(), repl.hashTable);
    removeReplacementInv(repl.invHashTable, Util.getOption(dst_opt));
  else
    Error.addInternalError("-BackendVarTransform.removeReplacement failed for " + ComponentReference.printComponentRefStr(inSrc) +"\n", sourceInfo());
  end try;
end removeReplacement;

public function removeReplacements
  input VariableReplacements iRepl;
  input list<DAE.ComponentRef> inSrcs;
algorithm
  for cr in inSrcs loop
    removeReplacement(iRepl,cr);
  end for;
end removeReplacements;

public function addReplacements
  input VariableReplacements iRepl;
  input list<DAE.ComponentRef> inSrcs;
  input list<DAE.Exp> inDsts;
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  output VariableReplacements outRepl;
algorithm
   outRepl := match(iRepl,inSrcs,inDsts,inFuncTypeExpExpToBooleanOption)
     local
       DAE.ComponentRef cr;
       list<DAE.ComponentRef> crlst;
       DAE.Exp exp;
       VariableReplacements repl;
       list<DAE.Exp> explst;
     case (_,{},{},_) then iRepl;
     case (_,cr::crlst,exp::explst,_)
       equation
         repl = addReplacement(iRepl,cr,exp,inFuncTypeExpExpToBooleanOption);
       then
         addReplacements(repl,crlst,explst,inFuncTypeExpExpToBooleanOption);
   end match;
end addReplacements;

public function addReplacement "
  Adds a replacement rule to the set of replacement rules given as argument.
  If a replacement rule a->b already exists and we add a new rule b->c then
  the rule a->b is updated to a->c. This is done using the make_transitive
  function.
"
  input VariableReplacements repl;
  input DAE.ComponentRef inSrc;
  input DAE.Exp inDst;
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  output VariableReplacements outRepl;
algorithm
  outRepl:=
  matchcontinue (repl,inSrc,inDst,inFuncTypeExpExpToBooleanOption)
    local
      DAE.ComponentRef src;
      DAE.Exp dst;
      CrefExpTable ht;
      CrefSet eht;
      CrefCrefListTable invHt;
      list<DAE.Ident> iv;
      String s;
      Option<CrefExpTable> derConst;
    // PA: Commented out this, since it will only slow things down without adding any functionality.
    // Once match is available as a complement to matchcontinue, this case could be useful again.
    //case ((repl as REPLACEMENTS(ht,invHt)),src,dst) /* source dest */
     // equation
     //   olddst = BaseHashTable.get(src, ht) "if rule a->b exists, fail";
     // then
     //   fail();

    case (_,src,dst,_)
      algorithm
        (REPLACEMENTS(ht,invHt,eht,iv,derConst),src,dst) := makeTransitive(repl, src, dst, inFuncTypeExpExpToBooleanOption);
        /*s1 = ComponentReference.printComponentRefStr(src);
        s2 = ExpressionDump.printExpStr(dst);
        s3 = ComponentReference.printComponentRefStr(src_1);
        s4 = ExpressionDump.printExpStr(dst_1);
        s = stringAppendList(
          {"add_replacement(",s1,", ",s2,") -> add_replacement(",s3,
          ", ",s4,")\n"});
          print(s);
        fprint(Flags.ADD_REPL, s);*/

        UnorderedMap.add(src, SOME(dst), ht);
        invHt := addReplacementInv(invHt, src, dst);
        eht := addExtendReplacement(eht,src,NONE());
      then
        REPLACEMENTS(ht,invHt,eht,iv,derConst);
    case (_,_,_,_)
      algorithm
        s := ComponentReference.printComponentRefStr(inSrc);
        print("-BackendVarTransform.addReplacement failed for " + s);
      then
        fail();
  end matchcontinue;
end addReplacement;

public function performReplacementsEqSystem
  input BackendDAE.EqSystem inEqs;
  input VariableReplacements inRepl;
  output BackendDAE.EqSystem outEqs = inEqs;
protected
  BackendDAE.EquationArray eqArr;
algorithm
  eqArr := inEqs.orderedEqs;
  (_, _) := BackendVariable.traverseBackendDAEVarsWithUpdate(inEqs.orderedVars, replaceVarTraverser, inRepl);
  ((eqArr, _)) := replaceEquationsArr(eqArr, inRepl, NONE());
  outEqs.orderedEqs := eqArr;
end performReplacementsEqSystem;

protected function addReplacementNoTransitive "Similar to addReplacement but
does not make transitive replacement rules.
"
  input VariableReplacements repl;
  input DAE.ComponentRef inSrc;
  input DAE.Exp inDst;
  output VariableReplacements outRepl;
algorithm
  outRepl:=
  matchcontinue (repl,inSrc,inDst)
    local
      DAE.ComponentRef src;
      DAE.Exp dst,olddst;
      CrefExpTable ht;
      CrefSet eht;
      CrefCrefListTable invHt;
      list<DAE.Ident> iv;
      Option<CrefExpTable> derConst;
    case (REPLACEMENTS(hashTable=ht),src,_) /* source dest */
      guard
        isSome(UnorderedMap.getOrDefault(src, ht, NONE())) "if rule a->b exists, fail"
      then
        fail();
    case (REPLACEMENTS(ht,invHt,eht,iv,derConst),src,dst)
      algorithm
        UnorderedMap.add(src, SOME(dst), ht);
        invHt := addReplacementInv(invHt, src, dst);
        eht := addExtendReplacement(eht,src,NONE());
      then
        REPLACEMENTS(ht,invHt,eht,iv,derConst);
    else
      algorithm
        print("-add_replacement failed for " + ComponentReference.printComponentRefStr(inSrc) + " = " + ExpressionDump.printExpStr(inDst) + "\n");
      then
        fail();
  end matchcontinue;
end addReplacementNoTransitive;

protected function removeReplacementInv "
  Helper function to removeReplacement
  removes the inverse rule of a replacement in the second binary tree
  of VariableReplacements.
"
  input CrefCrefListTable invHt;
  input DAE.Exp dst;
algorithm
  for d in Expression.extractCrefsFromExp(dst) loop
    UnorderedMap.tryUpdate(d, NONE(), invHt);
  end for;
end removeReplacementInv;

protected function addReplacementInv "
  Helper function to addReplacement
  Adds the inverse rule of a replacement to the second binary tree
  of VariableReplacements.
"
  input output CrefCrefListTable invHt;
  input DAE.ComponentRef src;
  input DAE.Exp dst;
algorithm
  for d in Expression.extractCrefsFromExp(dst) loop
    invHt := addReplacementInv2(invHt, d, src);
  end for;
end addReplacementInv;

protected function addReplacementInv2 "
  Helper function to addReplacementInv
  Adds the inverse rule for one of the variables of a replacement to the second binary tree
  of VariableReplacements.
  Since a replacement is on the form var -> expression of vars(v1,v2,...,vn) the inverse binary tree
  contains rules for v1 -> var, v2 -> var, ...., vn -> var so that any of the variables of the expression
  will update the rule.
"
  input output CrefCrefListTable invHt;
  input DAE.ComponentRef dst;
  input DAE.ComponentRef src;
protected
  Option<list<DAE.ComponentRef>> srcs_opt;
  list<DAE.ComponentRef> srcs;
algorithm
  srcs_opt := UnorderedMap.getOrDefault(dst, invHt, NONE());

  if isSome(srcs_opt) then
    // previous elt for dst -> src, append..
    SOME(srcs) := srcs_opt;
    srcs := src::srcs;
    UnorderedMap.add(dst, SOME(srcs), invHt);
  else
    // No previous elt for dst -> src
    UnorderedMap.add(dst, SOME({src}), invHt);
  end if;
end addReplacementInv2;

protected function makeTransitive "
  This function takes a set of replacement rules and a new replacement rule
  in the form of two ComponentRef:s and makes sure the new replacement rule
  is replaced with the transitive value.
  For example, if we have the rule a->b and a new rule c->a it is changed to c->b.
  Also, if we have a rule a->b and a new rule b->c then the -old- rule a->b is changed
  to a->c.
  For arbitrary expressions: if we have a rule ax-> expr(b1,..,bn) and a new rule c->expr(a1,ax,..,an)
  it is changed to c-> expr(a1,expr(b1,...,bn),..,an).
  And similary for a rule ax -> expr(b1,bx,..,bn) and a new rule bx->expr(c1,..,cn) then old rule is changed to
  ax -> expr(b1,expr(c1,..,cn),..,bn).
"
  input VariableReplacements repl;
  input DAE.ComponentRef src;
  input DAE.Exp dst;
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  output VariableReplacements outRepl;
  output DAE.ComponentRef outSrc;
  output DAE.Exp outDst;
algorithm
  (outRepl,outSrc,outDst):=
  match (repl,src,dst,inFuncTypeExpExpToBooleanOption)
    local
      VariableReplacements repl_1,repl_2;
      DAE.ComponentRef src_1,src_2;
      DAE.Exp dst_1,dst_2,dst_3;

    case (_,_,_,_)
      equation
        (repl_1,src_1,dst_1) = makeTransitive1(repl, src, dst,inFuncTypeExpExpToBooleanOption);
        (repl_2,src_2,dst_2) = makeTransitive2(repl_1, src_1, dst_1,inFuncTypeExpExpToBooleanOption);
        (dst_3,_) = ExpressionSimplify.simplify1(dst_2) "to remove e.g. --a";
      then
        (repl_2,src_2,dst_3);
  end match;
end makeTransitive;

protected function makeTransitive1 "
  helper function to makeTransitive
"
  input VariableReplacements repl;
  input DAE.ComponentRef src;
  input DAE.Exp dst;
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  output VariableReplacements outRepl;
  output DAE.ComponentRef outSrc;
  output DAE.Exp outDst;
algorithm
  (outRepl,outSrc,outDst):=
  matchcontinue (repl,src,dst,inFuncTypeExpExpToBooleanOption)
    local
      list<DAE.ComponentRef> lst;
      VariableReplacements repl_1,singleRepl;
      CrefCrefListTable invHt;
      // old rule a->expr(b1,..,bn) must be updated to a->expr(c_exp,...,bn) when new rule b1->c_exp
      // is introduced
    case ((REPLACEMENTS(invHashTable=invHt)),_,_,_)
      algorithm
        SOME(lst) := UnorderedMap.getOrFail(src, invHt);
        singleRepl := addReplacementNoTransitive(emptyReplacementsSized(53),src,dst);
        repl_1 := makeTransitive12(lst,repl,singleRepl,inFuncTypeExpExpToBooleanOption,HashSet.emptyHashSet());
      then
        (repl_1,src,dst);
    else (repl,src,dst);
  end matchcontinue;
end makeTransitive1;

protected function makeTransitive12 "Helper function to makeTransitive1
For each old rule a->expr(b1,..,bn) update dest by applying the new rule passed as argument
in singleRepl."
  input list<DAE.ComponentRef> lst;
  input VariableReplacements repl;
  input VariableReplacements singleRepl "contain one replacement rule: the rule to be added";
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  input HashSet.HashSet inSet "to avoid double work";
  output VariableReplacements outRepl;
algorithm
  outRepl := matchcontinue lst
    local
      DAE.Exp crDst;
      DAE.ComponentRef cr;
      list<DAE.ComponentRef> crs;
      VariableReplacements repl1;
      CrefExpTable ht;
      HashSet.HashSet set;
    case {} then repl;
    case cr::crs
      algorithm
        false := BaseHashSet.has(cr,inSet);
        set := BaseHashSet.add(cr,inSet);
        SOME(crDst) := UnorderedMap.getOrFail(cr,repl.hashTable);
        (crDst,_) := replaceExp(crDst,singleRepl,inFuncTypeExpExpToBooleanOption);
        repl1 := addReplacementNoTransitive(repl,cr,crDst) "add updated old rule";
      then
        makeTransitive12(crs,repl1,singleRepl,inFuncTypeExpExpToBooleanOption,set);
    case _::crs
      then
        makeTransitive12(crs,repl,singleRepl,inFuncTypeExpExpToBooleanOption,inSet);
  end matchcontinue;
end makeTransitive12;

protected function makeTransitive2 "
  Helper function to makeTransitive
"
  input VariableReplacements repl;
  input DAE.ComponentRef src;
  input DAE.Exp dst;
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  output VariableReplacements outRepl;
  output DAE.ComponentRef outSrc;
  output DAE.Exp outDst;
algorithm
  (outRepl,outSrc,outDst):=
  matchcontinue (repl,src,dst,inFuncTypeExpExpToBooleanOption)
    local
      DAE.Exp dst_1;
      // for rule a->b1+..+bn, replace all b1 to bn's in the expression;
    case (_,_,_,_)
      equation
        (dst_1,_) = replaceExp(dst,repl,inFuncTypeExpExpToBooleanOption);
      then
        (repl,src,dst_1);
        // replace Exp failed, keep old rule.
    case (_,_,_,_) then (repl,src,dst);  /* dst has no own replacement, return */
  end matchcontinue;
end makeTransitive2;

protected function addExtendReplacement
"author: Frenkel TUD 2011-04
  checks if the parents of cref from type array or record
  and add a rule to extend them."
  input CrefSet extendrepl;
  input DAE.ComponentRef cr;
  input Option<DAE.ComponentRef> preCr;
  output CrefSet outExtendrepl;
algorithm
  outExtendrepl:=
  matchcontinue (extendrepl,cr,preCr)
    local
      CrefSet erepl,erepl1;
      DAE.ComponentRef subcr,precr,precr1,pcr,precrn,precrn1;
      DAE.Ident ident;
      DAE.Type ty;
      list<DAE.Subscript> subscriptLst;
      list<DAE.Var> varLst;
      list<DAE.ComponentRef> crefs;
      String s;
    case (_,DAE.CREF_IDENT(ident=ident,identType=ty as DAE.T_ARRAY()),NONE())
      equation
        precr = ComponentReference.makeCrefIdent(ident,ty,{});
        // update Replacements
        UnorderedSet.addUnique(precr, extendrepl);
      then extendrepl;
    case (_,DAE.CREF_IDENT(ident=ident,identType=ty as DAE.T_ARRAY()),SOME(pcr))
      equation
        precr = ComponentReference.makeCrefIdent(ident,ty,{});
        precr1 = ComponentReference.joinCrefs(pcr,precr);
        // update Replacements
        UnorderedSet.addUnique(precr1, extendrepl);
      then extendrepl;
    case (_,DAE.CREF_IDENT(ident=ident,identType=ty as DAE.T_COMPLEX(complexClassType=ClassInf.RECORD(_),varLst=varLst)),NONE())
      equation
        precr = ComponentReference.makeCrefIdent(ident,ty,{});
        // update Replacements
        UnorderedSet.addUnique(precr, extendrepl);
        // Create a list of crefs from names
        crefs =  List.map(varLst,ComponentReference.creffromVar);
        erepl = List.fold1r(crefs,addExtendReplacement,SOME(precr), extendrepl);
      then erepl;
    case (_,DAE.CREF_IDENT(ident=ident,identType=ty as DAE.T_COMPLEX(complexClassType=ClassInf.RECORD(_),varLst=varLst)),SOME(pcr))
      equation
        _ = ComponentReference.makeCrefIdent(ident,ty,{});
        precr1 = ComponentReference.joinCrefs(pcr,cr);
        // update Replacements
        UnorderedSet.addUnique(precr1, extendrepl);
        // Create a list of crefs from names
        crefs =  List.map(varLst,ComponentReference.creffromVar);
        erepl = List.fold1r(crefs,addExtendReplacement,SOME(precr1), extendrepl);
      then erepl;
    case (_,DAE.CREF_IDENT(ident=ident,identType=ty,subscriptLst=_::_),NONE())
      equation
        precr = ComponentReference.makeCrefIdent(ident,ty,{});
        // update Replacements
        UnorderedSet.addUnique(precr, extendrepl);
      then extendrepl;
    case (_,DAE.CREF_IDENT(ident=ident,identType=ty,subscriptLst=_::_),SOME(pcr))
      equation
        precr = ComponentReference.makeCrefIdent(ident,ty,{});
        precr1 = ComponentReference.joinCrefs(pcr,precr);
        // update Replacements
        UnorderedSet.addUnique(precr1, extendrepl);
      then extendrepl;
    case (_,DAE.CREF_IDENT(),_)
      then
        extendrepl;
    case (_,DAE.CREF_QUAL(ident=ident,identType=ty,subscriptLst=subscriptLst,componentRef=subcr),NONE())
      equation
        precr = ComponentReference.makeCrefIdent(ident,ty,{});
        // update Replacements
        UnorderedSet.addUnique(precr, extendrepl);
        precrn = ComponentReference.makeCrefIdent(ident,ty,subscriptLst);
        erepl = addExtendReplacement(extendrepl,subcr,SOME(precrn));
      then erepl;
    case (_,DAE.CREF_QUAL(ident=ident,identType=ty,subscriptLst=subscriptLst,componentRef=subcr),SOME(pcr))
      equation
        precr = ComponentReference.makeCrefIdent(ident,ty,{});
        precr1 = ComponentReference.joinCrefs(pcr,precr);
        // update Replacements
        UnorderedSet.addUnique(precr1, extendrepl);
        precrn = ComponentReference.makeCrefIdent(ident,ty,subscriptLst);
        precrn1 = ComponentReference.joinCrefs(pcr,precrn);
        erepl = addExtendReplacement(extendrepl,subcr,SOME(precrn1));
      then erepl;
    // all other
    case (_,DAE.CREF_QUAL(ident=ident,identType=ty,subscriptLst=subscriptLst,componentRef=subcr),NONE())
      equation
        precrn = ComponentReference.makeCrefIdent(ident,ty,subscriptLst);
        erepl = addExtendReplacement(extendrepl,subcr,SOME(precrn));
      then erepl;
    case (_,DAE.CREF_QUAL(ident=ident,identType=ty,subscriptLst=subscriptLst,componentRef=subcr),SOME(pcr))
      equation
        precrn = ComponentReference.makeCrefIdent(ident,ty,subscriptLst);
        precrn1 = ComponentReference.joinCrefs(pcr,precrn);
        erepl = addExtendReplacement(extendrepl,subcr,SOME(precrn1));
      then erepl;
    case (_,_,_)
      equation
        true = Flags.isSet(Flags.FAILTRACE);
        s = ComponentReference.printComponentRefStr(cr);
        Debug.trace("- BackendVarTransform.addExtendReplacement failed for " + s);
      then extendrepl;
  end matchcontinue;
end addExtendReplacement;

protected function addIterationVar
"add a var to the iterationVars"
  input output VariableReplacements repl;
  input DAE.Ident inVar;
algorithm
  repl.iterationVars := inVar :: repl.iterationVars;
end addIterationVar;

protected function removeIterationVar
"remove the first equal var from the iterationVars"
  input output VariableReplacements repl;
  input DAE.Ident inVar;
algorithm
  repl.iterationVars := List.deleteMemberOnTrue(inVar, repl.iterationVars, stringEq);
end removeIterationVar;

protected function isIterationVar
"remove true if it is an iteration var"
  input VariableReplacements repl;
  input DAE.Ident inVar;
  output Boolean is;
algorithm
  is:=
  match (repl,inVar)
    local
      list<DAE.Ident> iv;
    case (REPLACEMENTS(iterationVars=iv),_)
      then
        listMember(inVar, iv);
  end match;
end isIterationVar;

public function addDerConstRepl
"add a var to the derConst replacements, replace der(const) with 0.0"
  input DAE.ComponentRef inComponentRef;
  input DAE.Exp inExp;
  input output VariableReplacements repl;
protected
  CrefExpTable derConst;
algorithm
  if isSome(repl.derConst) then
    UnorderedMap.add(inComponentRef, SOME(inExp), Util.getOption(repl.derConst));
  else
    derConst := newCrefExpTable();
    UnorderedMap.add(inComponentRef, SOME(inExp), derConst);
    repl.derConst := SOME(derConst);
  end if;
end addDerConstRepl;

public function getReplacement "
  Retrives a replacement variable given a set of replacement rules and a
  source variable.
"
  input VariableReplacements inVariableReplacements;
  input DAE.ComponentRef inComponentRef;
  output DAE.Exp outExp;
algorithm
  SOME(outExp) := UnorderedMap.getOrFail(inComponentRef, inVariableReplacements.hashTable);
end getReplacement;

public function hasReplacement "
  Outputs true if the replacements contain a rule for the cref
"
  input VariableReplacements repl;
  input DAE.ComponentRef inComponentRef;
  output Boolean bOut;
algorithm
  bOut := isSome(UnorderedMap.getOrDefault(inComponentRef, repl.hashTable, NONE()));
end hasReplacement;

public function hasNoReplacement "
  Outputs false if the replacements contain a rule for the cref
"
  input DAE.ComponentRef inComponentRef;
  input VariableReplacements repl;
  output Boolean bOut;
algorithm
  bOut := isNone(UnorderedMap.getOrDefault(inComponentRef, repl.hashTable, NONE()));
end hasNoReplacement;

public function getAllReplacements
  input VariableReplacements repl;
  output list<DAE.ComponentRef> crefs;
  output list<DAE.Exp> dsts;
algorithm
  (crefs, dsts) := getCrefExpTableEntries(repl.hashTable);
end getAllReplacements;

protected function getCrefExpTableEntries
  input CrefExpTable table;
  output list<DAE.ComponentRef> crefs;
  output list<DAE.Exp> dsts;
protected
  list<Option<DAE.Exp>> opt_dsts;
algorithm
  crefs := UnorderedMap.keyList(table);
  opt_dsts := UnorderedMap.valueList(table);
  // Remove deleted replacements, i.e. replacements set to NONE().
  (opt_dsts, crefs) := List.filterOnTrueSync(opt_dsts, isSome, crefs);
  dsts := list(Util.getOption(d) for d in opt_dsts);
end getCrefExpTableEntries;

public function hasExtendReplacement "
  Returns whether an extend replacement exists or not.
"
  input VariableReplacements repl;
  input DAE.ComponentRef src;
  output Boolean exists;
algorithm
  exists := UnorderedSet.contains(ComponentReference.crefStripLastSubs(src), repl.extendhashTable);
end hasExtendReplacement;

protected function avoidDoubleHashLookup "
Author BZ 200X-XX modified 2008-06
When adding replacement rules, we might not have the correct type availible at the moment.
Then DAE.T_UNKNOWN_DEFAULT is used, so when replacing exp and finding DAE.T_UNKNOWN_DEFAULT, we use the
type of the expression to be replaced instead.
TODO: find out why array residual functions containing arrays as xloc[] does not work,
      doing that will allow us to use this function for all crefs."
  input DAE.Exp inExp;
  input DAE.Type inType;
  output DAE.Exp outExp;
algorithm  outExp := matchcontinue(inExp,inType)
  local DAE.ComponentRef cr;
  case(DAE.CREF(cr,DAE.T_UNKNOWN()),_) then Expression.makeCrefExp(cr,inType);
  else inExp;
  end matchcontinue;
end avoidDoubleHashLookup;


public function isReplacementEmpty
  input VariableReplacements repl;
  output Boolean empty = UnorderedMap.none(repl.hashTable, isSome) and isNone(repl.derConst);
end isReplacementEmpty;

/*********************************************************/
/* replace Expression with condition function */
/*********************************************************/

public function replaceExp "Takes a set of replacement rules and an expression and a function
  giving a boolean value for an expression.
  The function replaces all variables in the expression using
  the replacement rules, if the boolean value is true children of the
  expression is visited (including the expression itself). If it is false,
  no replacemet is performed."
  input DAE.Exp inExp;
  input VariableReplacements inVariableReplacements;
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  output DAE.Exp outExp;
  output Boolean replacementPerformed;
algorithm
  (outExp,replacementPerformed) :=
  matchcontinue (inExp,inVariableReplacements,inFuncTypeExpExpToBooleanOption)
    local
      DAE.ComponentRef cr;
      DAE.Exp e,e1_1,e2_1,e1,e2,e3_1,e3, solverMethod, resolution, startInterval;
      DAE.Type t,tp;
      VariableReplacements repl;
      Option<FuncTypeExp_ExpToBoolean> cond;
      DAE.Operator op;
      list<DAE.Exp> expl_1,expl;
      Absyn.Path path;
      Boolean c,c1,c2,c3;
      Integer b,i;
      Absyn.CodeNode a;
      list<list<DAE.Exp>> bexpl_1,bexpl;
      Integer index_;
      Option<tuple<DAE.Exp,Integer,Integer>> isExpisASUB;
      DAE.ReductionInfo reductionInfo;
      DAE.ReductionIterators iters;
      DAE.CallAttributes attr;
      DAE.Ident ident;
      CrefExpTable derConst;
      list<String> fields;
      list<DAE.Dimension> dims;

      // Note: Most of these functions check if a subexpression did a replacement.
      // If it did not, we do not create a new copy of the expression (to save some memory).
    case (e as DAE.CREF(componentRef = DAE.CREF_IDENT(ident=ident)),repl,_)
      guard
        isIterationVar(repl, ident)
      then
        (e,false);
    case ((e as DAE.CREF(componentRef = cr,ty = t)),repl,cond)
        guard replaceExpCond(cond, e)
      equation
        (cr,_) = replaceCrefSubs(cr,repl,cond);
        e1 = getReplacement(repl, cr);
        e2 = avoidDoubleHashLookup(e1,t);
      then
        (e2,true);
    case ((e as DAE.CREF(componentRef = cr, ty = t)),repl,cond)
        guard replaceExpCond(cond, e)
      equation
        // only expand cref if dimensions are fixed
        (_, dims) = Types.flattenArrayType(t);
        true = List.none(list(Types.dimNotFixed(dim) for dim in dims), Util.id);

        (cr,_) = replaceCrefSubs(cr,repl,cond);
        true = hasExtendReplacement(repl, cr);
        (e2,true) = Expression.extendArrExp(e,false);
        (e3,_) = replaceExp(e2,repl,cond);
      then
        (e3,true);
    case ((e as DAE.CREF(componentRef = cr,ty = t)),repl,cond)
        guard replaceExpCond(cond, e)
      equation
        (cr,true) = replaceCrefSubs(cr,repl,cond);
      then (DAE.CREF(cr,t),true);
    case ((e as DAE.BINARY(exp1 = e1,operator = op,exp2 = e2)),repl,cond)
        guard replaceExpCond(cond, e)
      equation
        (e1_1,c1) = replaceExp(e1, repl, cond);
        (e2_1,c2) = replaceExp(e2, repl, cond);
        true = c1 or c2;
      then
        (DAE.BINARY(e1_1,op,e2_1),true);
    case ((e as DAE.LBINARY(exp1 = e1,operator = op,exp2 = e2)),repl,cond)
        guard replaceExpCond(cond, e)
      equation
        (e1_1,c1) = replaceExp(e1, repl, cond);
        (e2_1,c2) = replaceExp(e2, repl, cond);
        true = c1 or c2;
      then
        (DAE.LBINARY(e1_1,op,e2_1),true);
    case ((e as DAE.UNARY(operator = op,exp = e1)),repl,cond)
        guard replaceExpCond(cond, e)
      equation
        (e1_1,true) = replaceExp(e1, repl, cond);
      then
        (DAE.UNARY(op,e1_1),true);
    case ((e as DAE.LUNARY(operator = op,exp = e1)),repl,cond)
        guard replaceExpCond(cond, e)
      equation
        (e1_1,true) = replaceExp(e1, repl, cond);
      then
        (DAE.LUNARY(op,e1_1),true);
    case (DAE.RELATION(exp1 = e1,operator = op,exp2 = e2, index=index_, optionExpisASUB= isExpisASUB),repl,cond)
      equation
        (e1_1,c1) = replaceExp(e1, repl, cond);
        (e2_1,c2) = replaceExp(e2, repl, cond);
        true = c1 or c2;
      then
        (DAE.RELATION(e1_1,op,e2_1,index_,isExpisASUB),true);
    case ((e as DAE.IFEXP(expCond = e1,expThen = e2,expElse = e3)),repl,cond)
        guard replaceExpCond(cond, e)
      equation
        (e1_1,c1) = replaceExp(e1, repl, cond);
        (e2_1,c2) = replaceExp(e2, repl, cond);
        (e3_1,c3) = replaceExp(e3, repl, cond);
        true = c1 or c2 or c3;
      then
        (DAE.IFEXP(e1_1,e2_1,e3_1),true);
    case (DAE.CALL(path = Absyn.IDENT(name = "der"),expLst={DAE.CREF(componentRef = cr)}),REPLACEMENTS(derConst=SOME(derConst)),cond)
      equation
        SOME(e) = UnorderedMap.getOrFail(cr, derConst);
        (e,_) = replaceExp(e, inVariableReplacements, cond);
      then
        (e,true);
    case ((e as DAE.CALL(path = path,expLst = expl,attr = attr)),repl,cond)
        guard replaceExpCond(cond, e)
      equation
        cr = ComponentReference.toExpCref(AbsynUtil.pathToCref(path));
        if hasReplacement(repl,cr) then
          e1_1 = getReplacement(repl,cr);
          DAE.PARTEVALFUNCTION(path=path,expList = expl_1) = e1_1;
          expl = listAppend(expl_1,expl);
        end if;
        (expl_1,true) = replaceExpList(expl, repl, cond);
      then
        (DAE.CALL(path,expl_1,attr),true);
    case (DAE.RECORD(path, expl, fields, t), repl, cond)
      algorithm
        // add all constant attribute bindings to the replacements
        // partially fixes ticket #9036
        repl := addConstantRecordReplacements(t, expl, repl, inFuncTypeExpExpToBooleanOption);
        (expl, true) := replaceExpList(expl, repl, cond);
      then
        (DAE.RECORD(path, expl, fields, t), true);
    // RATIONAL_CLOCK
    case (DAE.CLKCONST(DAE.RATIONAL_CLOCK(intervalCounter=e, resolution=resolution)), repl, cond)
      equation
        (e, c1) = replaceExp(e, repl, cond);
        (resolution, c2) = replaceExp(resolution, repl, cond);
        c3 = c1 or c2;
      then
        (if c3 then DAE.CLKCONST(DAE.RATIONAL_CLOCK(e, resolution)) else inExp, c3);
    // REAL_CLOCK
    case (DAE.CLKCONST(DAE.REAL_CLOCK(interval=e)), repl, cond)
      equation
        (e, c1) = replaceExp(e, repl, cond);
      then
        (if c1 then DAE.CLKCONST(DAE.REAL_CLOCK(e)) else inExp, c1);
    // EVENT_CLOCK
    case (DAE.CLKCONST(DAE.EVENT_CLOCK(condition=e, startInterval=startInterval)), repl, cond)
      equation
        (e, c1) = replaceExp(e, repl, cond);
        (startInterval, c2) = replaceExp(startInterval, repl, cond);
        c3 = c1 or c2;
      then
        (if c3 then DAE.CLKCONST(DAE.EVENT_CLOCK(e, startInterval)) else inExp, c3);
    // SOLVER_CLOCK
    case (DAE.CLKCONST(DAE.SOLVER_CLOCK(c=e, solverMethod=solverMethod)), repl, cond)
      equation
        (e, c1) = replaceExp(e, repl, cond);
        (solverMethod, c2) = replaceExp(solverMethod, repl, cond);
        c3 = c1 or c2;
      then
        (if c3 then DAE.CLKCONST(DAE.SOLVER_CLOCK(e, solverMethod)) else inExp, c3);

    case ((e as DAE.PARTEVALFUNCTION(path,expl,tp,t)),repl,cond)
        guard replaceExpCond(cond, e)
      equation
        (expl_1,true) = replaceExpList(expl, repl, cond);
      then
        (DAE.PARTEVALFUNCTION(path,expl_1,tp,t),true);
    case ((e as DAE.ARRAY(ty = tp,scalar = c,array = expl)),repl,cond)
        guard replaceExpCond(cond, e)
      equation
        (expl_1,true) = replaceExpList(expl, repl, cond);
      then
        (DAE.ARRAY(tp,c,expl_1),true);
    case ((e as DAE.MATRIX(ty = t,integer = b,matrix = bexpl)),repl,cond)
        guard replaceExpCond(cond, e)
      equation
        (bexpl_1,true) = replaceExpMatrix(bexpl, repl, cond);
      then
        (DAE.MATRIX(t,b,bexpl_1),true);
    case ((e as DAE.RANGE(ty = tp,start = e1,step = NONE(),stop = e2)),repl,cond)
        guard replaceExpCond(cond, e)
      equation
        (e1_1,c1) = replaceExp(e1, repl, cond);
        (e2_1,c2) = replaceExp(e2, repl, cond);
        true = c1 or c2;
      then
        (DAE.RANGE(tp,e1_1,NONE(),e2_1),true);
    case ((e as DAE.RANGE(ty = tp,start = e1,step = SOME(e3),stop = e2)),repl,cond)
        guard replaceExpCond(cond, e)
      equation
        (e1_1,c1) = replaceExp(e1, repl, cond);
        (e2_1,c2) = replaceExp(e2, repl, cond);
        (e3_1,c3) = replaceExp(e3, repl, cond);
        true = c1 or c2 or c3;
      then
        (DAE.RANGE(tp,e1_1,SOME(e3_1),e2_1),true);
    case ((e as DAE.TUPLE(PR = expl)),repl,cond)
        guard replaceExpCond(cond, e)
      equation
        (expl_1,true) = replaceExpList(expl, repl, cond);
      then
        (DAE.TUPLE(expl_1),true);
    case ((e as DAE.CAST(ty = tp,exp = e1)),repl,cond)
        guard replaceExpCond(cond, e)
      equation
        (e1_1,true) = replaceExp(e1, repl, cond);
      then
        (DAE.CAST(tp,e1_1),true);
    case ((e as DAE.ASUB(exp = e1,sub = expl)),repl,cond)
        guard replaceExpCond(cond, e)
      equation
        (e1_1,c1) = replaceExp(e1, repl, cond);
        (expl,c2) = replaceExpList(expl, repl, cond);
        true = c1 or c2;
      then
        (Expression.makeASUB(e1_1,expl),true);
    case ((DAE.TSUB(exp = e1,ix = i, ty = tp)),repl,cond)
      equation
        true = replaceExpCond(cond, e1);
        (e1_1,true) = replaceExp(e1, repl, cond);
      then
        (DAE.TSUB(e1_1,i,tp),true);
    case ((e as DAE.SIZE(exp = e1,sz = SOME(e2))),repl,cond)
        guard replaceExpCond(cond, e)
      equation
        (e1_1,c1) = replaceExp(e1, repl, cond);
        (e2_1,c2) = replaceExp(e2, repl, cond);
        true = c1 or c2;
      then
        (DAE.SIZE(e1_1,SOME(e2_1)),true);
    case (DAE.CODE(code = a,ty = tp),_,_)
      equation
        print("replace_exp on CODE not impl.\n");
      then
        (DAE.CODE(a,tp),false);
    case ((e as DAE.REDUCTION(reductionInfo = reductionInfo,expr = e1,iterators = iters)),repl,cond)
        guard replaceExpCond(cond, e)
      equation
        (e1_1,_) = replaceExp(e1, repl, cond);
        (iters,true) = replaceExpIters(iters, repl, cond);
      then (DAE.REDUCTION(reductionInfo,e1_1,iters),true);
    case ((e as DAE.BOX(exp = e1)),repl,cond)
        guard replaceExpCond(cond, e)
      equation
        (e1_1,true) = replaceExp(e1, repl, cond);
      then
        (DAE.BOX(e1_1),true);
    case ((e as DAE.UNBOX(ty=tp, exp = e1)),repl,cond)
        guard replaceExpCond(cond, e)
      equation
        (e1_1,true) = replaceExp(e1, repl, cond);
      then
        (DAE.UNBOX(e1_1,tp),true);
    else
      then (inExp,false);
  end matchcontinue;
end replaceExp;

function addConstantRecordReplacements
  "adds replacements regarding constant elements of records.
  needs to always be done when other elements of records are replaced."
  input DAE.Type ty;
  input list<DAE.Exp> expl;
  input output VariableReplacements repl;
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
protected
  DAE.ComponentRef cref;
algorithm
  repl := match ty
    local
      DAE.Exp bind;

    case DAE.T_COMPLEX() algorithm
      for var in ty.varLst loop
        // only do something if there is a binding
        if DAEUtil.isBound(var.binding) then
          SOME(bind) := DAEUtil.bindingExp(var.binding);
          cref := getRecordElement(var.name, expl);
          // only replace if the expression is const and the name was found
          // if replacement already happened the name might not be found -> no error!
          if Expression.isConst(bind) and not ComponentReference.isWild(cref) then
            repl := addReplacement(repl, cref, bind, inFuncTypeExpExpToBooleanOption);
          end if;
        end if;
      end for;
    then repl;
    else repl;
  end match;
end addConstantRecordReplacements;

function getRecordElement
  "takes an attribute name and the list of full attribute names.
  returns the cref of which the last ident matches the required name."
  input DAE.Ident name;
  input list<DAE.Exp> expl;
  output DAE.ComponentRef cref = DAE.WILD();
protected
  DAE.Ident cref_name;
algorithm
  for e in expl loop
    _ := match e
      case DAE.CREF() guard(ComponentReference.crefLastIdent(e.componentRef) == name)
        algorithm
          cref := e.componentRef;
          return;
      then ();
      else ();
    end match;
  end for;
end getRecordElement;

public function replaceCref"replaces a cref.
author: Waurich TUD 2014-06"
  input DAE.ComponentRef crefIn;
  input VariableReplacements replIn;
  output DAE.Exp expOut;
  output Boolean changedOut;
algorithm
  (expOut,changedOut) := match(crefIn,replIn)
    local
      DAE.Exp exp;
    case(_,_) guard hasReplacement(replIn,crefIn)
      equation
        expOut = getReplacement(replIn,crefIn);
      then (expOut,true);
    else
    equation
      expOut = DAE.CREF(crefIn,ComponentReference.crefType(crefIn));
      then (expOut,false);
 end match;
end replaceCref;

protected function replaceCrefSubs
  input DAE.ComponentRef inCref;
  input VariableReplacements repl;
  input Option<FuncTypeExp_ExpToBoolean> cond;
  output DAE.ComponentRef outCr;
  output Boolean replacementPerformed;
algorithm
  (outCr,replacementPerformed) := match (inCref,repl,cond)
    local
      String name;
      DAE.ComponentRef cr,cr_1;
      DAE.Type ty;
      list<DAE.Subscript> subs,subs_1;
      Boolean c1,c2;

    case (DAE.CREF_QUAL(ident = name, identType = ty, subscriptLst = subs, componentRef = cr), _, _)
      equation
        (subs_1, c1) = replaceCrefSubs2(subs, repl, cond);
        (cr_1, c2) = replaceCrefSubs(cr, repl, cond);
        subs = if c1 then subs_1 else subs;
        cr = if c2 then cr_1 else cr;
        cr = if c1 or c2 then DAE.CREF_QUAL(name, ty, subs, cr) else inCref;
      then
        (cr, c1 or c2);

    case (DAE.CREF_IDENT(ident = name, identType = ty, subscriptLst = subs), _, _)
      equation
        (subs, c1) = replaceCrefSubs2(subs, repl, cond);
        cr = if c1 then DAE.CREF_IDENT(name, ty, subs) else inCref;
      then
        (cr, c1);

    else (inCref,false);
  end match;
end replaceCrefSubs;

protected function replaceCrefSubs2
  input list<DAE.Subscript> isubs;
  input VariableReplacements repl;
  input Option<FuncTypeExp_ExpToBoolean> cond;
  output list<DAE.Subscript> outSubs;
  output Boolean replacementPerformed = false;
algorithm
  outSubs := list(match sub
      local
        DAE.Exp exp;
        Boolean c1;
      case DAE.WHOLEDIM()
        then sub;
      case DAE.SLICE(exp = exp)
        equation
          (exp,c1) = replaceExp(exp, repl, cond);
          replacementPerformed = replacementPerformed or c1;
        then if c1 then DAE.SLICE(exp) else sub;
      case DAE.INDEX(exp = exp)
        equation
          (exp,c1) = replaceExp(exp, repl, cond);
          replacementPerformed = replacementPerformed or c1;
        then if c1 then DAE.INDEX(exp) else sub;
      case DAE.WHOLE_NONEXP(exp = exp)
        equation
          (exp,c1) = replaceExp(exp, repl, cond);
          replacementPerformed = replacementPerformed or c1;
        then if c1 then DAE.WHOLE_NONEXP(exp) else sub;
    end match for sub in isubs);
end replaceCrefSubs2;

public function replaceExpList
  input list<DAE.Exp> iexpl;
  input VariableReplacements repl;
  input Option<FuncTypeExp_ExpToBoolean> cond;
  output list<DAE.Exp> outExpl;
  output Boolean replacementPerformed = false;
protected
  DAE.Exp exp_;
  Boolean c;
algorithm
  outExpl := list(match exp
      case _ algorithm
        (exp_,c) := replaceExp(exp,repl,cond);
        if c then
          replacementPerformed := true;
        else
          exp_ := exp;
        end if;
        then exp_;
    end match for exp in iexpl);
end replaceExpList;

public function replaceExpList1
  input list<DAE.Exp> iexpl;
  input VariableReplacements repl;
  input Option<FuncTypeExp_ExpToBoolean> cond;
  output list<DAE.Exp> outExpl;
  output list<Boolean> replacementPerformed;
protected
  list<DAE.Exp> acc1 = {};
  list<Boolean> acc2 = {};
  Boolean c;
algorithm
  for exp in iexpl loop
    (exp,c) := replaceExp(exp,repl,cond);
    acc2 := c::acc2;
    acc1 := exp::acc1;
  end for;
  outExpl := listReverseInPlace(acc1);
  replacementPerformed := listReverseInPlace(acc2);
end replaceExpList1;


protected function replaceExpIters
  input list<DAE.ReductionIterator> inIters;
  input VariableReplacements repl;
  input Option<FuncTypeExp_ExpToBoolean> cond;
  output list<DAE.ReductionIterator> outIter;
  output Boolean replacementPerformed = false;
protected
  DAE.ReductionIterator it;
algorithm
  outIter := list(match (iter)
      local
        String id;
        DAE.Exp exp,gexp;
        DAE.Type ty;
        Boolean b1,b2;
      case (DAE.REDUCTIONITER(id,exp,NONE(),ty))
        equation
          (exp,b1) = replaceExp(exp, repl, cond);
          if b1 then
            it = DAE.REDUCTIONITER(id,exp,NONE(),ty);
            replacementPerformed = true;
          else
            it = iter;
          end if;
        then it;
      case (DAE.REDUCTIONITER(id,exp,SOME(gexp),ty))
        equation
          (exp,b1) = replaceExp(exp, repl, cond);
          (gexp,b2) = replaceExp(gexp, repl, cond);
          if b1 or b2 then
            it = DAE.REDUCTIONITER(id,exp,SOME(gexp),ty);
            replacementPerformed = true;
          else
            it = iter;
          end if;
        then it;
      else iter;
    end match for iter in inIters);
end replaceExpIters;

protected function replaceExpCond "function replaceExpCond(cond,e) => true &
  Helper function to replace_Expression. Evaluates a condition function if
  SOME otherwise returns true."
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  input DAE.Exp inExp;
  output Boolean outBoolean;
algorithm
  outBoolean:=
  match (inFuncTypeExpExpToBooleanOption,inExp)
    local
      Boolean res;
      FuncTypeExp_ExpToBoolean cond;
      DAE.Exp e;
    case (SOME(cond),e) /* cond e */
      equation
        res = cond(e);
      then
        res;
    else true;
  end match;
end replaceExpCond;

protected function replaceExpMatrix "author: PA
  Helper function to replaceExp, traverses Matrix expression list."
  input list<list<DAE.Exp>> inTplExpExpBooleanLstLst;
  input VariableReplacements inVariableReplacements;
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  output list<list<DAE.Exp>> outTplExpExpBooleanLstLst;
  output Boolean replacementPerformed = false;

protected
  list<DAE.Exp> exp_;
  Boolean c;
algorithm
  outTplExpExpBooleanLstLst := list(match exp
      case _ algorithm
        (exp_,c) := replaceExpList(exp, inVariableReplacements, inFuncTypeExpExpToBooleanOption);
        if c then
          replacementPerformed := true;
        else
          exp_ := exp;
        end if;
      then exp_;
    end match for exp in inTplExpExpBooleanLstLst);
end replaceExpMatrix;

/*********************************************************/
/* condition function for replace Expression  */
/*********************************************************/

public function skipPreOperator "The variable/exp in the pre operator should not be replaced.
  This function is passed to replace_exp to ensure this."
  input DAE.Exp inExp;
  output Boolean outBoolean;
algorithm
  outBoolean := match (inExp)
    local String idn;
    case (DAE.CALL(path = Absyn.IDENT(name = idn)))
      guard idn=="pre" or idn=="previous" then false;
    else true;
  end match;
end skipPreOperator;

public function skipPreChangeEdgeOperator "The variable/exp in the pre/change/edge operator should not be replaced.
  This function is passed to replace_exp to ensure this."
  input DAE.Exp inExp;
  output Boolean outBoolean;
algorithm
  outBoolean := match (inExp)
    local
      DAE.ComponentRef cr;
      String idn;
    case DAE.CALL(path = Absyn.IDENT(name = idn),expLst = {DAE.CREF(componentRef=cr)})
      guard idn=="pre" or idn=="previous" or idn=="change" or idn=="edge" then selfGeneratedVar(cr);
    case DAE.CALL(path = Absyn.IDENT(name = idn))
      guard idn=="pre" or idn=="previous" or idn=="change" or idn=="edge" then false;
    else true;
  end match;
end skipPreChangeEdgeOperator;

protected function selfGeneratedVar
  input DAE.ComponentRef inCref;
  output Boolean b;
algorithm
  b := match(inCref)
    local String idn;
    case DAE.CREF_QUAL(ident = idn) guard idn=="$ZERO" or idn=="$_DER" or idn=="$pDER" then true;
    // keep same a while untill we know which are needed
    //case DAE.CREF_QUAL(ident = "$DER") then true;
    else false;
  end match;
end selfGeneratedVar;

/*********************************************************/
/* replace Equations  */
/*********************************************************/

public function replaceEquationsArr
"This function takes a list of equations ana a set of variable
  replacements and applies the replacements on all equations.
  The function returns the updated list of equations"
  input BackendDAE.EquationArray inEqns;
  input VariableReplacements repl;
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  output BackendDAE.EquationArray outEqns;
  output Boolean replacementPerformed;
algorithm
  (outEqns,replacementPerformed) := matchcontinue(inEqns,repl,inFuncTypeExpExpToBooleanOption)
    local
      list<BackendDAE.Equation> eqns;
    case(_,_,_)
      equation
        // Do not do empty replacements; it just takes time ;)
        false = isReplacementEmpty(repl);
        ((_,_,eqns,replacementPerformed)) = BackendEquation.traverseEquationArray(inEqns,replaceEquationTraverser,(repl,inFuncTypeExpExpToBooleanOption,{},false));
        outEqns = if replacementPerformed then BackendEquation.listEquation(eqns) else inEqns;
      then
        (outEqns,replacementPerformed);
    else
      then
        (inEqns,false);
  end matchcontinue;
end replaceEquationsArr;

protected function replaceEquationTraverser
  "Help function to e.g. removeSimpleEquations"
  input BackendDAE.Equation inEq;
  input tuple<VariableReplacements,Option<FuncTypeExp_ExpToBoolean>,list<BackendDAE.Equation>,Boolean> inTpl;
  output BackendDAE.Equation e;
  output tuple<VariableReplacements,Option<FuncTypeExp_ExpToBoolean>,list<BackendDAE.Equation>,Boolean> outTpl;
protected
  VariableReplacements repl;
  Option<FuncTypeExp_ExpToBoolean> optfunc;
  list<BackendDAE.Equation> eqns;
  Boolean b;
algorithm
  e := inEq;
  (repl,optfunc,eqns,b) := inTpl;
  (eqns,b) := replaceEquation(e,repl,optfunc,eqns,b);
  outTpl := (repl,optfunc,eqns,b);
end replaceEquationTraverser;

public function replaceEquations
"This function takes a list of equations ana a set of variable
  replacements and applies the replacements on all equations.
  The function returns the updated list of equations"
  input list<BackendDAE.Equation> inEqns;
  input VariableReplacements repl;
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  output list<BackendDAE.Equation> outEqns;
  output Boolean replacementPerformed;
algorithm
  if isReplacementEmpty(repl) then
    outEqns := inEqns;
    replacementPerformed := false;
  else
    (outEqns,replacementPerformed) := replaceEquations2(inEqns,repl,inFuncTypeExpExpToBooleanOption,{},false);
    if replacementPerformed and false /* Seems to break some modules */ then
      (outEqns,_) := BackendDAETransform.traverseBackendDAEExpsEqnLstWithSymbolicOperation(outEqns,BackendDAETransform.collapseArrayCrefExp,0/*dummy*/);
    end if;
  end if;
end replaceEquations;

protected function replaceEquations2
  input list<BackendDAE.Equation> inBackendDAEEquationLst;
  input VariableReplacements inVariableReplacements;
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  input list<BackendDAE.Equation> inAcc;
  input Boolean iReplacementPerformed;
  output list<BackendDAE.Equation> outBackendDAEEquationLst;
  output Boolean replacementPerformed;
algorithm
  (outBackendDAEEquationLst,replacementPerformed) :=
  match (inBackendDAEEquationLst,inVariableReplacements,inFuncTypeExpExpToBooleanOption,inAcc,iReplacementPerformed)
    local
      BackendDAE.Equation a;
      list<BackendDAE.Equation> es,acc;
      Boolean b;
    case ({},_,_,_,_) then (listReverse(inAcc),iReplacementPerformed);
    case (a::es,_,_,_,_)
      equation
        (acc,b) = replaceEquation(a,inVariableReplacements,inFuncTypeExpExpToBooleanOption,inAcc,iReplacementPerformed);
        (es,b) = replaceEquations2(es, inVariableReplacements,inFuncTypeExpExpToBooleanOption,acc,b);
      then
        (es,b);
  end match;
end replaceEquations2;

protected function replaceEquation
  input BackendDAE.Equation inBackendDAEEquation;
  input VariableReplacements inVariableReplacements;
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  input list<BackendDAE.Equation> inAcc;
  input Boolean iReplacementPerformed;
  output list<BackendDAE.Equation> outBackendDAEEquationLst;
  output Boolean replacementPerformed;
algorithm
  (outBackendDAEEquationLst,replacementPerformed) :=
  matchcontinue (inBackendDAEEquation,inVariableReplacements,inFuncTypeExpExpToBooleanOption,inAcc,iReplacementPerformed)
    local
      DAE.Exp e1_1,e2_1,e1_2,e2_2,e1,e2,e_1,e_2,e;
      VariableReplacements repl;
      BackendDAE.Equation a;
      DAE.ComponentRef cr;
      Integer size;
      Option<Integer> recordSize;
      list<DAE.Exp> expl,expl1,expl2;
      BackendDAE.WhenEquation whenEqn,whenEqn1;
      DAE.ElementSource source;
      Boolean b1,b2,b3, hasArrayCref;
      list<Integer> dimSize;
      DAE.Algorithm alg;
      list<DAE.ComponentRef> crefs;
      list<DAE.Statement> stmts,stmts1;
      list<Boolean> blst;
      list<BackendDAE.Equation> eqns;
      list<list<BackendDAE.Equation>> eqnslst;
      DAE.Expand crefExpand;
      BackendDAE.EquationAttributes eqAttr;

    case (BackendDAE.ARRAY_EQUATION(dimSize=dimSize, left=e1, right=e2, source=source, attr=eqAttr, recordSize=recordSize),repl,_,_,_)
      equation
        (e1_1,b1) = replaceExp(e1, repl,inFuncTypeExpExpToBooleanOption);
        (e2_1,b2) = replaceExp(e2, repl,inFuncTypeExpExpToBooleanOption);
        true = b1 or b2;
        source = ElementSource.addSymbolicTransformationSubstitution(b1,source,e1,e1_1);
        source = ElementSource.addSymbolicTransformationSubstitution(b2,source,e2,e2_1);
        (DAE.EQUALITY_EXPS(e1_2,e2_2),source) = ExpressionSimplify.simplifyAddSymbolicOperation(DAE.EQUALITY_EXPS(e1_1,e2_1),source);
      then
        (BackendDAE.ARRAY_EQUATION(dimSize,e1_2,e2_2,source,eqAttr,recordSize)::inAcc,true);

    case (BackendDAE.COMPLEX_EQUATION(size=size, left=e1, right=e2, source=source, attr=eqAttr),repl,_,_,_)
      equation
        (e1_1,b1) = replaceExp(e1, repl,inFuncTypeExpExpToBooleanOption);
        (e2_1,b2) = replaceExp(e2, repl,inFuncTypeExpExpToBooleanOption);
        true = b1 or b2;
        source = ElementSource.addSymbolicTransformationSubstitution(b1,source,e1,e1_1);
        source = ElementSource.addSymbolicTransformationSubstitution(b2,source,e2,e2_1);
        (DAE.EQUALITY_EXPS(e1_2,e2_2),source) = ExpressionSimplify.simplifyAddSymbolicOperation(DAE.EQUALITY_EXPS(e1_1,e2_1),source);
      then
        (BackendDAE.COMPLEX_EQUATION(size,e1_2,e2_2,source,eqAttr)::inAcc,true);

    case (BackendDAE.EQUATION(exp=e1, scalar=e2, source=source, attr=eqAttr),repl,_,_,_)
      equation
        (e1_1,b1) = replaceExp(e1, repl,inFuncTypeExpExpToBooleanOption);
        (e2_1,b2) = replaceExp(e2, repl,inFuncTypeExpExpToBooleanOption);
        true = b1 or b2;
        source = ElementSource.addSymbolicTransformationSubstitution(b1,source,e1,e1_1);
        source = ElementSource.addSymbolicTransformationSubstitution(b2,source,e2,e2_1);
        (DAE.EQUALITY_EXPS(e1_2,e2_2),source) = ExpressionSimplify.simplifyAddSymbolicOperation(DAE.EQUALITY_EXPS(e1_1,e2_1),source);
      then
        (BackendDAE.EQUATION(e1_2,e2_2,source,eqAttr)::inAcc,true);

    case (BackendDAE.ALGORITHM(size=size, alg=DAE.ALGORITHM_STMTS(statementLst=stmts), source=source, expand=crefExpand, attr=eqAttr), repl, _, _, _)
      equation
        crefs = Expression.getLhsCrefsFromStatements(stmts);
        // if there is no need for expanding the original equation, the replaced one shouldn't either
        hasArrayCref = List.exist(crefs,ComponentReference.isArrayElement);
        crefExpand = if hasArrayCref then crefExpand else DAE.NOT_EXPAND();

        (stmts1,true) = replaceStatementLst(stmts,repl,inFuncTypeExpExpToBooleanOption,{},false);
        alg = DAE.ALGORITHM_STMTS(stmts1);
        // if all statements are removed, remove the whole algorithm
        eqns = if not listEmpty(stmts1) then BackendDAE.ALGORITHM(size,alg,source,crefExpand,eqAttr)::inAcc else inAcc;
      then
        (eqns,true);

    case (BackendDAE.SOLVED_EQUATION(componentRef=cr, exp=e, source=source, attr=eqAttr),repl,_,_,_)
      equation
        (e_1,true) = replaceExp(e, repl,inFuncTypeExpExpToBooleanOption);
        (e_2,_) = ExpressionSimplify.simplify(e_1);
        source = ElementSource.addSymbolicTransformationSubstitution(true,source,e,e_2);
      then
        (BackendDAE.SOLVED_EQUATION(cr,e_2,source,eqAttr)::inAcc,true);

    case (BackendDAE.RESIDUAL_EQUATION(exp=e, source=source, attr=eqAttr),repl,_,_,_)
      equation
        (e_1,true) = replaceExp(e, repl,inFuncTypeExpExpToBooleanOption);
        (e_2,_) = ExpressionSimplify.simplify(e_1);
        source = ElementSource.addSymbolicTransformationSubstitution(true,source,e,e_2);
      then
        (BackendDAE.RESIDUAL_EQUATION(e_2,source,eqAttr)::inAcc,true);

    case (BackendDAE.WHEN_EQUATION(size,whenEqn,source,eqAttr),repl,_,_,_)
      equation
        (whenEqn1,source,true) = replaceWhenEquation(whenEqn,repl,inFuncTypeExpExpToBooleanOption,source);
      then
        (BackendDAE.WHEN_EQUATION(size,whenEqn1,source,eqAttr)::inAcc,true);

    case (BackendDAE.IF_EQUATION(conditions=expl, eqnstrue=eqnslst, eqnsfalse=eqns, source=source, attr=eqAttr),repl,_,_,_)
      equation
        (expl1,blst) = replaceExpList1(expl, repl, inFuncTypeExpExpToBooleanOption);
        b1 = Util.boolOrList(blst);
        source = ElementSource.addSymbolicTransformationSubstitutionLst(blst,source,expl,expl1);
        (expl2,blst) = ExpressionSimplify.condsimplifyList1(blst,expl1);
        source = ElementSource.addSymbolicTransformationSimplifyLst(blst,source,expl1,expl2);
        (eqnslst,b2) = List.map3Fold(eqnslst,replaceEquations2,repl,inFuncTypeExpExpToBooleanOption,{},false);
        (eqns,b3) = replaceEquations2(eqns,repl,inFuncTypeExpExpToBooleanOption,{},false);
        true = b1 or b2 or b3;
        eqns = optimizeIfEquation(expl2,eqnslst,eqns,{},{},source,eqAttr,inAcc);
      then
        (eqns,true);

    case (a,_,_,_,_) then (a::inAcc,iReplacementPerformed);

  end matchcontinue;
end replaceEquation;

protected function optimizeIfEquation
  input list<DAE.Exp> conditions;
  input list<list<BackendDAE.Equation>> theneqns;
  input list<BackendDAE.Equation> elseenqs;
  input list<DAE.Exp> conditions1;
  input list<list<BackendDAE.Equation>> theneqns1;
  input DAE.ElementSource source;
  input BackendDAE.EquationAttributes inEqAttr;
  input list<BackendDAE.Equation> inEqns;
  output list<BackendDAE.Equation> outEqns;
algorithm
  outEqns := matchcontinue(conditions,theneqns,elseenqs,conditions1,theneqns1,source,inEqAttr,inEqns)
    local
      DAE.Exp e;
      list<DAE.Exp> explst;
      list<list<BackendDAE.Equation>> eqnslst;
      list<BackendDAE.Equation> eqns;

    // no true case left with condition<>false
    case ({},{},_,{},{},_,_,_)
      then
        listAppend(elseenqs,inEqns);
    // true case left with condition<>false
    case ({},{},_,_,_,_,_,_)
      equation
        explst = listReverse(conditions1);
        eqnslst = listReverse(theneqns1);
      then
        BackendDAE.IF_EQUATION(explst,eqnslst,elseenqs,source,inEqAttr)::inEqns;
    // if true use it if it is the first one
    case(DAE.BCONST(true)::_,eqns::_,_,{},{},_,_,_)
      then
        listAppend(eqns,inEqns);
    // if true use it as new else if it is not the first one
    case(DAE.BCONST(true)::_,eqns::_,_,{},{},_,_,_)
      equation
        explst = listReverse(conditions1);
        eqnslst = listReverse(theneqns1);
      then
        BackendDAE.IF_EQUATION(explst,eqnslst,eqns,source,inEqAttr)::inEqns;
    // if false skip it
    case(DAE.BCONST(false)::explst,_::eqnslst,_,_,_,_,_,_)
      then
        optimizeIfEquation(explst,eqnslst,elseenqs,conditions1,theneqns1,source,inEqAttr,inEqns);
    // all other cases
    case(e::explst,eqns::eqnslst,_,_,_,_,_,_)
      then
        optimizeIfEquation(explst,eqnslst,elseenqs,e::conditions1,eqns::theneqns1,source,inEqAttr,inEqns);
  end matchcontinue;
end optimizeIfEquation;

protected function validWhenLeftHandSide
  input DAE.Exp inLhs;
  input DAE.Exp inRhs;
  input DAE.ComponentRef oldCr;
  output DAE.ComponentRef outCr;
  output DAE.Exp oRhs;
algorithm
  (outCr,oRhs) := match(inLhs,inRhs,oldCr)
    local
      DAE.ComponentRef cr;
      DAE.Operator op;
      String msg;
    case(DAE.CREF(componentRef=cr),_,_) then (cr,inRhs);
    case(DAE.UNARY(operator=op,exp=DAE.CREF(componentRef=cr)),_,_) then (cr,DAE.UNARY(op,inRhs));
    case(DAE.LUNARY(operator=op,exp=DAE.CREF(componentRef=cr)),_,_) then (cr,DAE.LUNARY(op,inRhs));
    else
      equation
        true = Flags.isSet(Flags.FAILTRACE);
        msg = "BackendVarTransform: failed to replace left hand side of when equation " +
              ComponentReference.printComponentRefStr(oldCr) + " with " + ExpressionDump.printExpStr(inLhs) + "\n";
        // print(msg + "\n");
        Debug.trace(msg);
      then
        fail();
  end match;
end validWhenLeftHandSide;

protected function replaceWhenEquation "Replaces variables in a when equation"
  input BackendDAE.WhenEquation whenEqn;
  input VariableReplacements repl;
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  input DAE.ElementSource isource;
  output BackendDAE.WhenEquation outWhenEqn;
  output DAE.ElementSource osource;
  output Boolean replacementPerformed;

algorithm
  (outWhenEqn,osource,replacementPerformed) :=
  match(whenEqn,repl,inFuncTypeExpExpToBooleanOption,isource)
  local
    DAE.ComponentRef cr,cr1;
    DAE.Exp e,e1,e2,cre,cre1,cond,cond1,cond2;
    BackendDAE.WhenEquation weqn,elsePart,elsePart2;
    Boolean b1,b2,b3,b4;
    DAE.ElementSource source;
    list<BackendDAE.WhenOperator> whenStmtLst;
    Option<BackendDAE.WhenEquation> oelsewhenPart;
    BackendDAE.WhenEquation elsewhenPart;

    case (BackendDAE.WHEN_STMTS(condition=cond,whenStmtLst=whenStmtLst,elsewhenPart=oelsewhenPart),_,_,_)
      equation
        (cond1, b1) = replaceExp(cond, repl, inFuncTypeExpExpToBooleanOption);
        (cond2, _) = ExpressionSimplify.condsimplify(b1, cond1);
        source = ElementSource.addSymbolicTransformationSubstitution(b1, isource, cond, cond2);
        (whenStmtLst,b2) = replaceWhenOperator(whenStmtLst, repl, inFuncTypeExpExpToBooleanOption, false, {});
        if isSome(oelsewhenPart) then
          SOME(elsewhenPart) = oelsewhenPart;
          (elsewhenPart,source,b3) = replaceWhenEquation(elsewhenPart,repl,inFuncTypeExpExpToBooleanOption,source);
          oelsewhenPart = SOME(elsewhenPart);
        else
          oelsewhenPart = NONE();
          b3 = false;
        end if;
        b4 = b1 or b2 or b3;
        weqn = if b4 then BackendDAE.WHEN_STMTS(cond2,whenStmtLst,oelsewhenPart) else whenEqn;
      then (weqn,source,b4);

  end match;
end replaceWhenEquation;

protected function replaceWhenOperator
"author: Frenkel TUD 2012-09"
  input list<BackendDAE.WhenOperator> inReinitStmtLst;
  input VariableReplacements repl;
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  input Boolean replacementPerformed;
  input list<BackendDAE.WhenOperator> iAcc;
  output list<BackendDAE.WhenOperator> oReinitStmtLst;
  output Boolean oReplacementPerformed;

algorithm
  (oReinitStmtLst,oReplacementPerformed) :=
  match (inReinitStmtLst,repl,inFuncTypeExpExpToBooleanOption,replacementPerformed,iAcc)
    local
      list<BackendDAE.WhenOperator> res,res1;
      BackendDAE.WhenOperator wop,wop1;
      DAE.Exp cond,cond1,msg,level,cre,cre1,exp,exp1;
      DAE.ComponentRef cr,cr1;
      DAE.ElementSource source;
      Boolean b,b1,b2;
      Absyn.Path functionName;
      list<DAE.Exp> functionArgs,functionArgs1;
      list<Boolean> blst;

    case ({},_,_,_,_) then (listReverse(iAcc),replacementPerformed);

    case ((wop as BackendDAE.ASSIGN(left=cre as DAE.CREF(componentRef = cr),right=exp,source=source))::res,_,_,_,_)
      equation
        //cre = Expression.crefExp(cr);
        (cre1,b1) = replaceExp(cre,repl,inFuncTypeExpExpToBooleanOption);
        (_,_) = validWhenLeftHandSide(cre1,cre,cr);
        source = ElementSource.addSymbolicTransformationSubstitution(b1,source,cre,cre1);
        (exp1,b2) = replaceExp(exp,repl,inFuncTypeExpExpToBooleanOption);
        (exp1,_) = ExpressionSimplify.condsimplify(b2,exp1);
        source = ElementSource.addSymbolicTransformationSubstitution(b2,source,exp,exp1);
        b = b1 or b2;
        wop1 = if b then BackendDAE.ASSIGN(cre1,exp1,source) else wop;
        (res1,b) =  replaceWhenOperator(res,repl,inFuncTypeExpExpToBooleanOption,replacementPerformed or b,wop1::iAcc);
      then
        (res1,b);

    case ((wop as BackendDAE.ASSIGN(left=cre, right=exp, source=source))::res,_,_,_,_)
      equation
        //cre = Expression.crefExp(cr);
        (cre1,b1) = replaceExp(cre,repl,inFuncTypeExpExpToBooleanOption);
        source = ElementSource.addSymbolicTransformationSubstitution(b1,source,cre,cre1);
        (exp1,b2) = replaceExp(exp,repl,inFuncTypeExpExpToBooleanOption);
        (exp1,_) = ExpressionSimplify.condsimplify(b2,exp1);
        source = ElementSource.addSymbolicTransformationSubstitution(b2,source,exp,exp1);
        b = b1 or b2;
        wop1 = if b then BackendDAE.ASSIGN(cre1,exp1,source) else wop;
        (res1,b) =  replaceWhenOperator(res,repl,inFuncTypeExpExpToBooleanOption,replacementPerformed or b,wop1::iAcc);
      then
        (res1,b);

    case ((wop as BackendDAE.REINIT(stateVar=cr,value=cond,source=source))::res,_,_,_,_)
      equation
        cre = Expression.crefExp(cr);
        (cre1,b1) = replaceExp(cre,repl,inFuncTypeExpExpToBooleanOption);
        (cr1,_) = validWhenLeftHandSide(cre1,cre,cr);
        source = ElementSource.addSymbolicTransformationSubstitution(b1,source,cre,cre1);
        (cond1,b2) = replaceExp(cond,repl,inFuncTypeExpExpToBooleanOption);
        (cond1,_) = ExpressionSimplify.condsimplify(b2,cond1);
        source = ElementSource.addSymbolicTransformationSubstitution(b2,source,cond,cond1);
        b = b1 or b2;
        wop1 = if b then BackendDAE.REINIT(cr1,cond1,source) else wop;
        (res1,b) =  replaceWhenOperator(res,repl,inFuncTypeExpExpToBooleanOption,replacementPerformed or b,wop1::iAcc);
      then
        (res1,b);
    case ((wop as BackendDAE.ASSERT(condition=cond,message=exp,level=level,source=source))::res,_,_,_,_)
      equation
        (cond1,b1) = replaceExp(cond,repl,inFuncTypeExpExpToBooleanOption);
        (cond1,_) = ExpressionSimplify.condsimplify(b1,cond1);
        (exp1,b2) = replaceExp(exp,repl,inFuncTypeExpExpToBooleanOption);
        b = b1 or b2;
        source = ElementSource.addSymbolicTransformationSubstitution(b,source,cond,cond1);
        wop1 = if b then BackendDAE.ASSERT(cond1,exp1,level,source) else wop;
        (res1,b) =  replaceWhenOperator(res,repl,inFuncTypeExpExpToBooleanOption,replacementPerformed or b,wop1::iAcc);
      then
        (res1,b);
    case ((wop as BackendDAE.TERMINATE(message=exp,source=source))::res,_,_,_,_)
      equation
        (exp1,b) = replaceExp(exp,repl,inFuncTypeExpExpToBooleanOption);
        source = ElementSource.addSymbolicTransformationSubstitution(b,source,exp,exp1);
        wop1 = if b then BackendDAE.TERMINATE(exp1,source) else wop;
        (res1,b) =  replaceWhenOperator(res,repl,inFuncTypeExpExpToBooleanOption,replacementPerformed or b,wop1::iAcc);
      then
        (res1,b);
    case ((wop as BackendDAE.NORETCALL(exp=exp,source=source))::res,_,_,_,_)
      equation
        (exp1,b) = replaceExp(exp,repl,inFuncTypeExpExpToBooleanOption);
        (exp1,_) = ExpressionSimplify.condsimplify(b,exp1);
        source = ElementSource.addSymbolicTransformationSubstitution(b,source,exp,exp1);
        wop1 = if b then BackendDAE.NORETCALL(exp1,source) else wop;
        (res1,b) =  replaceWhenOperator(res,repl,inFuncTypeExpExpToBooleanOption,replacementPerformed or b,wop1::iAcc);
      then
        (res1,b);
  end match;
end replaceWhenOperator;

/*********************************************************/
/* replace statements  */
/*********************************************************/

public function replaceStatementLst "
function: replaceStatementLst
  perform replacements on statements.
"
  input list<DAE.Statement> inStatementLst;
  input VariableReplacements inVariableReplacements;
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  input list<DAE.Statement> inAcc;
  input Boolean inBAcc;
  output list<DAE.Statement> outStatementLst = {};
  output Boolean replacementPerformed = inBAcc;

protected
  Boolean isCon;
  VariableReplacements repl = inVariableReplacements;
  list<DAE.Statement> es,es_1,statementLst,statementLst_1;
  DAE.Statement statement,statement_1;
  DAE.Type type_;
  DAE.Exp e1_1,e2_1,e1,e2,e1_2,e2_2,e3,e3_1,e3_2;
  list<DAE.Exp> expExpLst,expExpLst_1;
  DAE.Else else_;
  DAE.ElementSource source;
  DAE.ComponentRef cr;
  Boolean iterIsArray;
  DAE.Ident ident;
  list<DAE.ComponentRef> conditions;
  Boolean initialCall;
  Boolean b,b1,b2,b3;
  list<tuple<DAE.ComponentRef,SourceInfo>> loopPrlVars "list of parallel variables used/referenced in the parfor loop";
algorithm
  for stmt in inStatementLst loop
    (outStatementLst, replacementPerformed) := matchcontinue stmt
      case DAE.STMT_ASSIGN(type_=type_,exp1=e1,exp=e2,source=source)
        equation
          (e1_1,b1) = replaceExp(e1, repl,inFuncTypeExpExpToBooleanOption);
          //isCon = Expression.isConst(e1_1);
          //e1_1 = if_(isCon,e1,e1_1);
          //cr = Expression.expCref(e1);
          //repl = Debug.bcallret3(isCon,removeReplacement,repl,cr,NONE(),repl);
          (e2_1,b2) = replaceExp(e2, repl,inFuncTypeExpExpToBooleanOption);
          true = b1 or b2;
          (e1_2,_) = ExpressionSimplify.simplify(e1_1);
          (e2_2,_) = ExpressionSimplify.simplify(e2_1);
          (e1_2,e2_2) = moveNegateRhs(e1_2,e2_2);
          source = ElementSource.addSymbolicTransformationSubstitution(b1,source,e1,e1_2);
          source = ElementSource.addSymbolicTransformationSubstitution(b2,source,e2,e2_2);
        then
          (DAE.STMT_ASSIGN(type_,e1_2,e2_2,source) :: outStatementLst, true);

      case DAE.STMT_TUPLE_ASSIGN(type_=type_,expExpLst=expExpLst,exp=e2,source=source)
        equation
          (expExpLst_1,b1) = replaceExpList(expExpLst,repl,inFuncTypeExpExpToBooleanOption);
          (e2_1,b2) = replaceExp(e2, repl,inFuncTypeExpExpToBooleanOption);
          true = b1 or b2;
          source = ElementSource.addSymbolicTransformationSubstitution(b2,source,e2,e2_1);
          (e2_2,b1) = ExpressionSimplify.simplify(e2_1);
          source = ElementSource.addSymbolicTransformationSimplify(b1,source,DAE.PARTIAL_EQUATION(e2_1),DAE.PARTIAL_EQUATION(e2_2));
        then
          (DAE.STMT_TUPLE_ASSIGN(type_,expExpLst_1,e2_2,source) :: outStatementLst, true);

      case DAE.STMT_ASSIGN_ARR(type_=type_, lhs = e1 as DAE.CREF(componentRef=cr),exp=e2,source=source)
        equation
          (e1_1,b1) = replaceExp(e1,repl,inFuncTypeExpExpToBooleanOption);
          (e2_1,b2) = replaceExp(e2, repl,inFuncTypeExpExpToBooleanOption);
          true = b1 or b2;
          source = ElementSource.addSymbolicTransformationSubstitution(b1,source,e1,e1_1);
          source = ElementSource.addSymbolicTransformationSubstitution(b2,source,e2,e2_1);
          (DAE.EQUALITY_EXPS(e1_1,e2_2),source) = ExpressionSimplify.simplifyAddSymbolicOperation(DAE.EQUALITY_EXPS(e1_1,e2_1),source);
        then
          (validLhsArrayAssignSTMT(cr,e1_1,e2_2,type_,source,outStatementLst), true);

      case DAE.STMT_IF(exp=e1,statementLst=statementLst,else_=else_,source=source)
        equation
          (e1_1,b1) = replaceExp(e1, repl,inFuncTypeExpExpToBooleanOption);
          (e1_2,_) = ExpressionSimplify.condsimplify(b1,e1_1);
          source = ElementSource.addSymbolicTransformationSubstitution(b1,source,e1,e1_2);
        then
          replaceSTMT_IF(e1_2,statementLst,else_,source,repl,inFuncTypeExpExpToBooleanOption,outStatementLst,replacementPerformed or b1);

      case DAE.STMT_FOR(type_=type_,iterIsArray=iterIsArray,iter=ident,range=e1,statementLst=statementLst,source=source)
        equation
          repl = addIterationVar(repl,ident);
          (statementLst_1,b1) = replaceStatementLst(statementLst, repl,inFuncTypeExpExpToBooleanOption,{},false);
          (e1_1,b2) = replaceExp(e1, repl,inFuncTypeExpExpToBooleanOption);
          true = b1 or b2;
          source = ElementSource.addSymbolicTransformationSubstitution(b2,source,e1,e1_1);
          (e1_2,b1) = ExpressionSimplify.condsimplify(b2,e1_1);
          source = ElementSource.addSymbolicTransformationSimplify(b1,source,DAE.PARTIAL_EQUATION(e1_1),DAE.PARTIAL_EQUATION(e1_2));
          repl = removeIterationVar(repl,ident);
        then
          (DAE.STMT_FOR(type_,iterIsArray,ident,e1_2,statementLst_1,source) :: outStatementLst, true);

      case DAE.STMT_PARFOR(type_=type_,iterIsArray=iterIsArray,iter=ident,range=e1,statementLst=statementLst,loopPrlVars=loopPrlVars,source=source)
        equation
          (statementLst_1,b1) = replaceStatementLst(statementLst, repl,inFuncTypeExpExpToBooleanOption,{},false);
          (e1_1,b2) = replaceExp(e1, repl,inFuncTypeExpExpToBooleanOption);
          true = b1 or b2;
          source = ElementSource.addSymbolicTransformationSubstitution(b2,source,e1,e1_1);
          (e1_2,b1) = ExpressionSimplify.condsimplify(b2,e1_1);
          source = ElementSource.addSymbolicTransformationSimplify(b1,source,DAE.PARTIAL_EQUATION(e1_1),DAE.PARTIAL_EQUATION(e1_2));
        then
          (DAE.STMT_PARFOR(type_,iterIsArray,ident,e1_2,statementLst_1,loopPrlVars,source) :: outStatementLst, true);

      case DAE.STMT_WHILE(exp=e1,statementLst=statementLst,source=source)
        equation
          (statementLst_1,b1) = replaceStatementLst(statementLst, repl,inFuncTypeExpExpToBooleanOption,{},false);
          (e1_1,b2) = replaceExp(e1, repl,inFuncTypeExpExpToBooleanOption);
          true = b1 or b2;
          source = ElementSource.addSymbolicTransformationSubstitution(b2,source,e1,e1_1);
          (e1_2,b1) = ExpressionSimplify.condsimplify(b2,e1_1);
          source = ElementSource.addSymbolicTransformationSimplify(b1,source,DAE.PARTIAL_EQUATION(e1_1),DAE.PARTIAL_EQUATION(e1_2));
        then
          (DAE.STMT_WHILE(e1_2,statementLst_1,source) :: outStatementLst, true);

      case DAE.STMT_WHEN(exp=e1,conditions=conditions,initialCall=initialCall,statementLst=statementLst,elseWhen=NONE(),source=source)
        equation
          (statementLst_1,b1) = replaceStatementLst(statementLst, repl,inFuncTypeExpExpToBooleanOption,{},false);
          (e1_1,b2) = replaceExp(e1, repl,inFuncTypeExpExpToBooleanOption);
          true = b1 or b2;
          source = ElementSource.addSymbolicTransformationSubstitution(b2,source,e1,e1_1);
          (e1_2,b1) = ExpressionSimplify.condsimplify(b2,e1_1);
          source = ElementSource.addSymbolicTransformationSimplify(b1,source,DAE.PARTIAL_EQUATION(e1_1),DAE.PARTIAL_EQUATION(e1_2));
        then
          (DAE.STMT_WHEN(e1_2,conditions,initialCall,statementLst_1,NONE(),source) :: outStatementLst, true);

      case DAE.STMT_WHEN(exp=e1,conditions=conditions,initialCall=initialCall,statementLst=statementLst,elseWhen=SOME(statement),source=source)
        equation
          (statementLst_1,b1) = replaceStatementLst(statementLst, repl,inFuncTypeExpExpToBooleanOption,{},false);
          (statement_1::{},b2) = replaceStatementLst({statement}, repl,inFuncTypeExpExpToBooleanOption,{},false);
          (e1_1,b3) = replaceExp(e1, repl,inFuncTypeExpExpToBooleanOption);
          true = b1 or b2 or b3;
          source = ElementSource.addSymbolicTransformationSubstitution(b3,source,e1,e1_1);
          (e1_2,b1) = ExpressionSimplify.condsimplify(b3,e1_1);
          source = ElementSource.addSymbolicTransformationSimplify(b1,source,DAE.PARTIAL_EQUATION(e1_1),DAE.PARTIAL_EQUATION(e1_2));
        then
          (DAE.STMT_WHEN(e1_2,conditions,initialCall,statementLst_1,SOME(statement_1),source) :: outStatementLst, true);

      case DAE.STMT_ASSERT(cond=e1,msg=e2,level=e3,source=source)
        equation
          (e1_1,b1) = replaceExp(e1, repl,inFuncTypeExpExpToBooleanOption);
          (e2_1,b2) = replaceExp(e2, repl,inFuncTypeExpExpToBooleanOption);
          (e3_1,b3) = replaceExp(e3, repl,inFuncTypeExpExpToBooleanOption);
          true = b1 or b2 or b3;
          (e1_2,_) = ExpressionSimplify.condsimplify(b1,e1_1);
          (e2_2,_) = ExpressionSimplify.condsimplify(b2,e2_1);
          (e3_2,_) = ExpressionSimplify.condsimplify(b3,e3_1);
          source = ElementSource.addSymbolicTransformationSubstitution(b1,source,e1,e1_2);
          source = ElementSource.addSymbolicTransformationSubstitution(b2,source,e2,e2_2);
          source = ElementSource.addSymbolicTransformationSubstitution(b3,source,e3,e3_2);
        then
          (DAE.STMT_ASSERT(e1_2,e2_2,e3_2,source) :: outStatementLst, true);

      case DAE.STMT_TERMINATE(msg=e1,source=source)
        equation
          (e1_1,true) = replaceExp(e1, repl,inFuncTypeExpExpToBooleanOption);
          source = ElementSource.addSymbolicTransformationSubstitution(true,source,e1,e1_1);
          (e1_2,b1) = ExpressionSimplify.simplify(e1_1);
          source = ElementSource.addSymbolicTransformationSimplify(b1,source,DAE.PARTIAL_EQUATION(e1_1),DAE.PARTIAL_EQUATION(e1_2));
        then
          (DAE.STMT_TERMINATE(e1_2,source) :: outStatementLst, true);

      case DAE.STMT_REINIT(var=e1,value=e2,source=source)
        equation
          (e1_1,b1) = replaceExp(e1, repl,inFuncTypeExpExpToBooleanOption);
          (e2_1,b2) = replaceExp(e2, repl,inFuncTypeExpExpToBooleanOption);
          true = b1 or b2;
          (e1_2,_) = ExpressionSimplify.condsimplify(b1,e1_1);
          (e2_2,_) = ExpressionSimplify.condsimplify(b2,e2_1);
          source = ElementSource.addSymbolicTransformationSubstitution(b1,source,e1,e1_2);
          source = ElementSource.addSymbolicTransformationSubstitution(b2,source,e2,e2_2);
        then
          (DAE.STMT_REINIT(e1_2,e2_2,source) :: outStatementLst, true);

      case DAE.STMT_NORETCALL(exp=e1,source=source)
        equation
          (e1_1,true) = replaceExp(e1, repl,inFuncTypeExpExpToBooleanOption);
          source = ElementSource.addSymbolicTransformationSubstitution(true,source,e1,e1_1);
          (e1_2,b1) = ExpressionSimplify.simplify(e1_1);
          source = ElementSource.addSymbolicTransformationSimplify(b1,source,DAE.PARTIAL_EQUATION(e1_1),DAE.PARTIAL_EQUATION(e1_2));
        then
          (DAE.STMT_NORETCALL(e1_2,source) :: outStatementLst, true);

      // MetaModelica extension. KS
      case DAE.STMT_FAILURE(body=statementLst,source=source)
        equation
          (statementLst_1,true) = replaceStatementLst(statementLst, repl,inFuncTypeExpExpToBooleanOption,{},false);
        then
          (DAE.STMT_FAILURE(statementLst_1,source) :: outStatementLst, true);

      else (stmt :: outStatementLst, replacementPerformed);
    end matchcontinue;
  end for;

  outStatementLst := listReverseInPlace(outStatementLst);
end replaceStatementLst;

public function replaceStatementLstRHS
  input list<DAE.Statement> inStatementLst;
  input VariableReplacements inVariableReplacements;
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  input list<DAE.Statement> inAcc;
  input Boolean inBAcc;
  output list<DAE.Statement> outStatementLst;
  output Boolean replacementPerformed;
partial function FuncTypeExp_ExpToBoolean
  input DAE.Exp inExp;
  output Boolean outBoolean;
  end FuncTypeExp_ExpToBoolean;
algorithm
  (outStatementLst,(_,_,replacementPerformed)) := DAEUtil.traverseDAEEquationsStmtsRhsOnly(inStatementLst,replaceExpWrapper,(inVariableReplacements,inFuncTypeExpExpToBooleanOption,false));
end replaceStatementLstRHS;

protected function replaceExpWrapper"to use replaceExp in DAEUtil.traverseDAEEquationsStmtsRhsOnly
author: Waurich TUD 2014-4"
  input DAE.Exp inExp;
  input tuple<VariableReplacements,Option<FuncTypeExp_ExpToBoolean>,Boolean> inTpl;
  output DAE.Exp exp;
  output tuple<VariableReplacements,Option<FuncTypeExp_ExpToBoolean>,Boolean> tpl;
partial function FuncTypeExp_ExpToBoolean
  input DAE.Exp inExp;
  output Boolean outBoolean;
end FuncTypeExp_ExpToBoolean;
protected
  Boolean b1,b2;
  VariableReplacements repl;
  Option<FuncTypeExp_ExpToBoolean> opt;
algorithm
  exp := inExp;
  tpl := inTpl;
  (repl,opt,b1) := tpl;
  (exp,b2) := replaceExp(exp,repl,opt);
  b2 := b1 or b2;
  tpl := (repl,opt,b2);
end replaceExpWrapper;

protected function moveNegateRhs
  input DAE.Exp inLhs;
  input DAE.Exp inRhs;
  output DAE.Exp outLhs;
  output DAE.Exp outRhs;
algorithm
  (outLhs,outRhs) := match(inLhs,inRhs)
    local
      DAE.Exp e;
      DAE.Type ty;
    case (DAE.LUNARY(DAE.NOT(ty),e),_) then (e,DAE.LUNARY(DAE.NOT(ty),inRhs));
    case (DAE.UNARY(DAE.UMINUS(ty),e),_) then (e,DAE.UNARY(DAE.UMINUS(ty),inRhs));
    case (DAE.UNARY(DAE.UMINUS_ARR(ty),e),_) then (e,DAE.UNARY(DAE.UMINUS_ARR(ty),inRhs));
    case (_,_) then (inLhs,inRhs);
  end match;
end moveNegateRhs;

protected function validLhsArrayAssignSTMT "
function: validLhsArrayAssignSTMT
  author Frenkel TUD 2012-11
  checks if the lhs is a variable or an array of variables."
  input DAE.ComponentRef oldCr;
  input DAE.Exp lhs;
  input DAE.Exp rhs;
  input DAE.Type type_;
  input DAE.ElementSource source;
  input list<DAE.Statement> inStatementLst;
  output list<DAE.Statement> outStatementLst;
algorithm
  outStatementLst :=
  matchcontinue (oldCr,lhs,rhs,type_,source,inStatementLst)
    local
      list<DAE.Statement> statementLst;
      DAE.ComponentRef cr;
      list<DAE.Exp> elst,elst1;
      DAE.Type tp;
      DAE.Exp e, crefexp;
      list<Integer> ds;
      list<list<DAE.Subscript>> subslst;
      String msg;
    case (_,crefexp,_,_,_,_) then DAE.STMT_ASSIGN_ARR(type_,crefexp,rhs,source)::inStatementLst;
    case (_,DAE.UNARY(DAE.UMINUS(tp),crefexp),_,_,_,_) then DAE.STMT_ASSIGN_ARR(type_,crefexp,DAE.UNARY(DAE.UMINUS(tp),rhs),source)::inStatementLst;
    case (_,DAE.UNARY(DAE.UMINUS_ARR(tp),crefexp),_,_,_,_) then DAE.STMT_ASSIGN_ARR(type_,crefexp,DAE.UNARY(DAE.UMINUS_ARR(tp),rhs),source)::inStatementLst;
    case (_,DAE.LUNARY(DAE.NOT(tp),crefexp),_,_,_,_) then DAE.STMT_ASSIGN_ARR(type_,crefexp,DAE.LUNARY(DAE.NOT(tp),rhs),source)::inStatementLst;
    case (_,DAE.ARRAY(array=elst),_,_,_,_)
      equation
        ds = Expression.dimensionsSizes(Expression.arrayDimension(type_));
        subslst = Expression.dimensionSizesSubscripts(ds);
        subslst = Expression.rangesToSubscripts(subslst);
        elst1 = List.map1r(subslst,Expression.applyExpSubscripts,rhs);
        e = listHead(elst1);
        tp = Expression.typeof(e);
        statementLst = List.threadFold2(elst,elst1,validLhsAssignSTMT,tp,source,inStatementLst);
      then
        statementLst;
    else
      equation
        true = Flags.isSet(Flags.FAILTRACE);
        msg = "BackendVarTransform: failed to replace left hand side of array assign statement " +
              ComponentReference.printComponentRefStr(oldCr) + " with " + ExpressionDump.printExpStr(lhs) + "\n";
        // print(msg + "\n");
        Debug.trace(msg);
      then
        fail();
  end matchcontinue;
 end validLhsArrayAssignSTMT;

protected function validLhsAssignSTMT "
function: validLhsAssignSTMT
  author Frenkel TUD 2012-11
  checks if the lhs is a variable or an array of variables."
  input DAE.Exp lhs;
  input DAE.Exp rhs;
  input DAE.Type type_;
  input DAE.ElementSource source;
  input list<DAE.Statement> inStatementLst;
  output list<DAE.Statement> outStatementLst;
algorithm
  outStatementLst :=
  match (lhs,rhs,type_,source,inStatementLst)
    local DAE.Type tp;
    case (DAE.CREF(),_,_,_,_) then DAE.STMT_ASSIGN(type_,lhs,rhs,source)::inStatementLst;
    case (DAE.UNARY(DAE.UMINUS(tp),DAE.CREF()),_,_,_,_) then DAE.STMT_ASSIGN(type_,lhs,DAE.UNARY(DAE.UMINUS(tp),rhs),source)::inStatementLst;
    case (DAE.LUNARY(DAE.NOT(tp),DAE.CREF()),_,_,_,_) then DAE.STMT_ASSIGN(type_,lhs,DAE.LUNARY(DAE.NOT(tp),rhs),source)::inStatementLst;
  end match;
 end validLhsAssignSTMT;


protected function replaceElse "
  Helper for replaceStatementLst.
"
  input DAE.Else inElse;
  input VariableReplacements inVariableReplacements;
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  output DAE.Else outElse;
  output Boolean replacementPerformed;

algorithm
  (outElse,replacementPerformed) := matchcontinue (inElse,inVariableReplacements,inFuncTypeExpExpToBooleanOption)
    local
      VariableReplacements repl;
      list<DAE.Statement> statementLst,statementLst_1;
      DAE.Exp e1,e1_1,e1_2;
      DAE.Else else_,else_1;
      Boolean b1,b2;
    case (DAE.ELSEIF(exp=e1,statementLst=statementLst,else_=else_),repl,_)
      equation
        (e1_1,b1) = replaceExp(e1, repl,inFuncTypeExpExpToBooleanOption);
        (e1_2,_) = ExpressionSimplify.condsimplify(b1,e1_1);
        (else_1,b2) = replaceElse1(e1_2,statementLst,else_,repl,inFuncTypeExpExpToBooleanOption);
        true = b1 or b2;
      then
        (else_1,true);
    case (DAE.ELSE(statementLst=statementLst),repl,_)
      equation
        (statementLst_1,true) = replaceStatementLst(statementLst, repl,inFuncTypeExpExpToBooleanOption,{},false);
      then
        (DAE.ELSE(statementLst_1),true);
    else (inElse,false);
  end matchcontinue;
end replaceElse;

protected function replaceElse1 "
  Helper for replaceStatementLst.
"
  input DAE.Exp inExp;
  input list<DAE.Statement> inStatementLst;
  input DAE.Else inElse;
  input VariableReplacements inVariableReplacements;
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  output DAE.Else outElse;
  output Boolean replacementPerformed;

algorithm
  (outElse,replacementPerformed) := matchcontinue (inExp,inStatementLst,inElse,inVariableReplacements,inFuncTypeExpExpToBooleanOption)
    local
      VariableReplacements repl;
      list<DAE.Statement> statementLst,statementLst_1;
      DAE.Exp e1;
      DAE.Else else_,else_1;
      Boolean b1,b2;
    case (DAE.BCONST(true),statementLst,_,repl,_)
      equation
        (statementLst_1,_) = replaceStatementLst(statementLst, repl,inFuncTypeExpExpToBooleanOption,{},false);
      then
        (DAE.ELSE(statementLst_1),true);
    case (DAE.BCONST(false),_,else_,repl,_)
      equation
        (else_1,_) = replaceElse(else_, repl,inFuncTypeExpExpToBooleanOption);
      then
        (else_1,true);
    case (e1,statementLst,else_,repl,_)
      equation
        (statementLst_1,b1) = replaceStatementLst(statementLst, repl,inFuncTypeExpExpToBooleanOption,{},false);
        (else_1,b2) = replaceElse(else_,repl,inFuncTypeExpExpToBooleanOption);
        true = b1 or b2;
      then
        (DAE.ELSEIF(e1,statementLst_1,else_1),true);
    case (e1,statementLst,else_,_,_)
      then
        (DAE.ELSEIF(e1,statementLst,else_),false);
  end matchcontinue;
end replaceElse1;

protected function replaceSTMT_IF
  input DAE.Exp inExp;
  input list<DAE.Statement> inStatementLst;
  input DAE.Else inElse;
  input DAE.ElementSource inSource;
  input VariableReplacements inVariableReplacements;
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  input list<DAE.Statement> inAcc;
  input Boolean inBAcc;
  output list<DAE.Statement> outStatementLst;
  output Boolean replacementPerformed;

algorithm
  (outStatementLst,replacementPerformed) :=
  matchcontinue (inExp,inStatementLst,inElse,inSource,inVariableReplacements,inFuncTypeExpExpToBooleanOption,inAcc,inBAcc)
    local
      DAE.Exp exp,exp_e;
      list<DAE.Statement> statementLst,statementLst_e,statementLst_1,es,es_1;
      DAE.Else else_,else_e,else_1;
      DAE.ElementSource source;
      VariableReplacements repl;
      Boolean b,b1,b2;
      case (DAE.BCONST(true),statementLst,_,_,repl,_,_,_)
        then replaceStatementLst(statementLst, repl, inFuncTypeExpExpToBooleanOption, inAcc, true);
      case (DAE.BCONST(false),_,DAE.NOELSE(),_,repl,_,_,_)
        then (inAcc, true);
      case (DAE.BCONST(false),_,DAE.ELSEIF(exp=exp_e,statementLst=statementLst_e,else_=else_e),source,repl,_,_,_)
        then replaceSTMT_IF(exp_e,statementLst_e,else_e,source,repl,inFuncTypeExpExpToBooleanOption,inAcc,true);
      case (DAE.BCONST(false),_,DAE.ELSE(statementLst=statementLst_e),_,repl,_,_,_)
        then replaceStatementLst(statementLst_e, repl, inFuncTypeExpExpToBooleanOption, inAcc, true);
      case (exp,statementLst,else_,source,repl,_,_,_)
        equation
          (statementLst_1,b1) = replaceStatementLst(statementLst, repl,inFuncTypeExpExpToBooleanOption,{},false);
          (else_1,b2) = replaceElse(else_,repl,inFuncTypeExpExpToBooleanOption);
          true = b1 or b2;
        then
          (DAE.STMT_IF(exp,statementLst_1,else_1,source) :: inAcc, true);
      case (exp,statementLst,else_,source,repl,_,_,_)
        then (DAE.STMT_IF(exp,statementLst,else_,source) :: inAcc, inBAcc);
   end matchcontinue;
end replaceSTMT_IF;

/*********************************************************/
/* variable replacements  */
/*********************************************************/

public function replaceVarTraverser "author: Frenkel TUD 2011-03"
  input BackendDAE.Var inVar;
  input VariableReplacements inRepl;
  output BackendDAE.Var outVar;
  output VariableReplacements repl = inRepl;
algorithm
  outVar := replaceBindingExp(inVar, inRepl);
  outVar := replaceVariableAttributesInVar(outVar, inRepl);
end replaceVarTraverser;

public function replaceBindingExp
  input BackendDAE.Var varIn;
  input VariableReplacements repl;
  output BackendDAE.Var varOut;
algorithm
  varOut := match(varIn,repl)
  local
    DAE.Exp exp;
  case(BackendDAE.VAR(bindExp=SOME(exp)),_)
    equation
    exp = replaceExp(exp,repl,NONE());
    (exp,_) = ExpressionSimplify.simplify(exp);
  then BackendVariable.setBindExp(varIn,SOME(exp));
  case(BackendDAE.VAR(bindExp=NONE()),_)
    then varIn;
  end match;
end replaceBindingExp;

public function replaceVariableAttributes
  input DAE.VariableAttributes attrIn;
  input VariableReplacements repl;
  output DAE.VariableAttributes attrOut;
algorithm
  attrOut := match(attrIn,repl)
  local
    Option<DAE.Exp> quantity "quantity";
    Option<DAE.Exp> unit "unit";
    Option<DAE.Exp> displayUnit "displayUnit";
    Option<DAE.Exp> min;
    Option<DAE.Exp> max;
    Option<DAE.Exp> start "start value";
    Option<DAE.Exp> fixed "fixed - true: default for parameter/constant, false - default for other variables";
    Option<DAE.Exp> nominal "nominal";
    Option<DAE.StateSelect> stateSelectOption;
    Option<DAE.Uncertainty> uncertainOption;
    Option<DAE.Distribution> distributionOption;
    Option<DAE.Exp> equationBound;
    Option<Boolean> isProtected;
    Option<Boolean> finalPrefix;
    Option<DAE.Exp> startOrigin;
  case(DAE.VAR_ATTR_REAL(quantity,unit,displayUnit,min,max,start,fixed,nominal,stateSelectOption,uncertainOption,distributionOption,
    equationBound,isProtected,finalPrefix,startOrigin),_)
    equation
    quantity = replaceOptionExp(quantity,repl);
    unit = replaceOptionExp(unit,repl);
    displayUnit = replaceOptionExp(displayUnit,repl);
    min = replaceOptionExp(min,repl);
    max = replaceOptionExp(max,repl);
    start = replaceOptionExp(start,repl);
    fixed = replaceOptionExp(fixed,repl);
    nominal = replaceOptionExp(nominal,repl);
    equationBound = replaceOptionExp(equationBound,repl);
    startOrigin = replaceOptionExp(startOrigin,repl);
  then DAE.VAR_ATTR_REAL(quantity,unit,displayUnit,min,max,start,fixed,nominal,stateSelectOption,uncertainOption,distributionOption,
    equationBound,isProtected,finalPrefix,startOrigin);

  case(DAE.VAR_ATTR_INT(quantity,min,max,start,fixed,uncertainOption,distributionOption,
    equationBound,isProtected,finalPrefix,startOrigin),_)
    equation
    quantity = replaceOptionExp(quantity,repl);
    min = replaceOptionExp(min,repl);
    max = replaceOptionExp(max,repl);
    start = replaceOptionExp(start,repl);
    fixed = replaceOptionExp(fixed,repl);
    equationBound = replaceOptionExp(equationBound,repl);
    startOrigin = replaceOptionExp(startOrigin,repl);
  then DAE.VAR_ATTR_INT(quantity,min,max,start,fixed,uncertainOption,distributionOption,
    equationBound,isProtected,finalPrefix,startOrigin);

  case(DAE.VAR_ATTR_BOOL(quantity,start,fixed,equationBound,isProtected,finalPrefix,startOrigin),_)
    equation
    quantity = replaceOptionExp(quantity,repl);
    start = replaceOptionExp(start,repl);
    fixed = replaceOptionExp(fixed,repl);
    equationBound = replaceOptionExp(equationBound,repl);
    startOrigin = replaceOptionExp(startOrigin,repl);
  then DAE.VAR_ATTR_BOOL(quantity,start,fixed,equationBound,isProtected,finalPrefix,startOrigin);

  case(DAE.VAR_ATTR_STRING(quantity,start,fixed,equationBound,isProtected,finalPrefix,startOrigin),_)
    equation
    quantity = replaceOptionExp(quantity,repl);
    start = replaceOptionExp(start,repl);
    fixed = replaceOptionExp(fixed,repl);
    equationBound = replaceOptionExp(equationBound,repl);
    startOrigin = replaceOptionExp(startOrigin,repl);
  then DAE.VAR_ATTR_STRING(quantity,start,fixed,equationBound,isProtected,finalPrefix,startOrigin);

  case(DAE.VAR_ATTR_ENUMERATION(quantity,min,max,start,fixed,equationBound,isProtected,finalPrefix,startOrigin),_)
    equation
    quantity = replaceOptionExp(quantity,repl);
    min = replaceOptionExp(min,repl);
    max = replaceOptionExp(max,repl);
    start = replaceOptionExp(start,repl);
    fixed = replaceOptionExp(fixed,repl);
    equationBound = replaceOptionExp(equationBound,repl);
    startOrigin = replaceOptionExp(startOrigin,repl);
  then DAE.VAR_ATTR_ENUMERATION(quantity,min,max,start,fixed,equationBound,isProtected,finalPrefix,startOrigin);

  else
    then attrIn;
  end match;
end replaceVariableAttributes;

public function replaceOptionExp"replaces the exp inside an option"
  input Option<DAE.Exp> optIn;
  input VariableReplacements repl;
  output Option<DAE.Exp> optOut;
protected
  DAE.Exp exp;
algorithm
  if isSome(optIn) then
    exp := Util.getOption(optIn);
    exp := replaceExp(exp,repl,NONE());
    optOut := SOME(exp);
  else
    optOut := NONE();
  end if;
end replaceOptionExp;

public function replaceVariableAttributesInVar
  input BackendDAE.Var varIn;
  input VariableReplacements repl;
  output BackendDAE.Var varOut;
algorithm
  varOut := match(varIn,repl)
  local
    DAE.VariableAttributes values;
  case(BackendDAE.VAR(values=SOME(values)),_)
    equation
    values = replaceVariableAttributes(values,repl);
    then BackendVariable.setVarAttributes(varIn,SOME(values));
  else
    then varIn;
  end match;
end replaceVariableAttributesInVar;

protected function negateOperator
  "makes an add out of a sub and a sub out of an add."
  input DAE.Operator inOp;
  output DAE.Operator outOp;
algorithm
  outOp:= match(inOp)
    local
      DAE.Type ty;
    case(DAE.UMINUS(ty=ty)) then DAE.ADD(ty);
    case(DAE.SUB(ty=ty)) then DAE.ADD(ty);
    case(DAE.ADD(ty=ty)) then DAE.SUB(ty);
    else inOp;
  end match;
end negateOperator;

public function replaceEventInfo
  input BackendDAE.EventInfo eInfoIn;
  input VariableReplacements inVariableReplacements;
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  output BackendDAE.EventInfo eInfoOut;

protected
  Integer numberMathEvents;
  list<BackendDAE.TimeEvent> timeEvents;
  BackendDAE.ZeroCrossingSet zeroCrossingLst, sampleLst;
  DoubleEnded.MutableList<BackendDAE.ZeroCrossing> relationsLst;
  protected partial function Func
    input output BackendDAE.ZeroCrossing zc;
    input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  end Func;
  Func zc;
algorithm
  BackendDAE.EVENT_INFO(timeEvents, zeroCrossingLst, relationsLst, sampleLst, numberMathEvents) := eInfoIn;
  timeEvents := List.map2(timeEvents, replaceTimeEvents, inVariableReplacements, inFuncTypeExpExpToBooleanOption);
  zc := function replaceZeroCrossing(inVariableReplacements=inVariableReplacements);
  DoubleEnded.mapNoCopy_1(zeroCrossingLst.zc, zc, inFuncTypeExpExpToBooleanOption);
  DoubleEnded.mapNoCopy_1(sampleLst.zc, zc, inFuncTypeExpExpToBooleanOption);
  DoubleEnded.mapNoCopy_1(relationsLst, zc, inFuncTypeExpExpToBooleanOption);
  eInfoOut := BackendDAE.EVENT_INFO(timeEvents,zeroCrossingLst,relationsLst,sampleLst,numberMathEvents);
end replaceEventInfo;

protected function replaceTimeEvents
  input BackendDAE.TimeEvent teIn;
  input VariableReplacements inVariableReplacements;
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  output BackendDAE.TimeEvent teOut;

algorithm
  teOut := matchcontinue(teIn,inVariableReplacements,inFuncTypeExpExpToBooleanOption)
    local
      Integer index;
      DAE.Exp startExp, intervalExp;
  case(BackendDAE.SAMPLE_TIME_EVENT(index=index, startExp=startExp, intervalExp=intervalExp),_,_)
    equation
      (startExp,_) = replaceExp(startExp,inVariableReplacements,inFuncTypeExpExpToBooleanOption);
      (intervalExp,_) = replaceExp(intervalExp,inVariableReplacements,inFuncTypeExpExpToBooleanOption);
    then BackendDAE.SAMPLE_TIME_EVENT(index, startExp, intervalExp);
  else
    then teIn;
  end matchcontinue;
end replaceTimeEvents;

protected function replaceZeroCrossing"replaces the exp in the BackendDAE.ZeroCrossing"
  input BackendDAE.ZeroCrossing zcIn;
  input VariableReplacements inVariableReplacements;
  input Option<FuncTypeExp_ExpToBoolean> inFuncTypeExpExpToBooleanOption;
  output BackendDAE.ZeroCrossing zcOut;

algorithm
  zcOut := matchcontinue(zcIn,inVariableReplacements,inFuncTypeExpExpToBooleanOption)
    local
      DAE.Exp relation_;
  case(BackendDAE.ZERO_CROSSING(relation_ = relation_),_,_)
    equation
      (relation_,_) = replaceExp(relation_,inVariableReplacements,inFuncTypeExpExpToBooleanOption);
    then BackendDAE.ZERO_CROSSING(zcIn.index, relation_, zcIn.occurEquLst, zcIn.iter);
  else
    then zcIn;
  end matchcontinue;
end replaceZeroCrossing;


/*********************************************************/
/* dump replacements  */
/*********************************************************/

public function dumpReplacements "Prints the variable replacements on form var1 -> var2"
  input VariableReplacements repl;
protected
  list<DAE.ComponentRef> srcs;
  list<DAE.Exp> dsts;
  list<tuple<DAE.ComponentRef,DAE.Exp>> tplLst;
algorithm
  (srcs, dsts) := getAllReplacements(repl);
  tplLst := List.zip(srcs, dsts);
  print("\nReplacements: (");
  print(String(listLength(tplLst)));
  print(")\n");
  print("========================================\n");
  print(stringDelimitList(List.map(tplLst,printReplacementTupleStr), "\n"));
  print("\n");
end dumpReplacements;

public function dumpExtendReplacements
"Prints the variable extendreplacements on form var1 -> var2"
  input VariableReplacements repl;
protected
  list<DAE.ComponentRef> crefs;
algorithm
  crefs := UnorderedSet.toList(repl.extendhashTable);
  print("\nExtendReplacements: (");
  print(String(listLength(crefs)));
  print(")\n");
  print("========================================\n");
  print(stringDelimitList(list(ComponentReference.printComponentRefStr(c) for c in crefs), "\n"));
  print("\n");
end dumpExtendReplacements;

public function dumpDerConstReplacements
"Prints the variable derConst replacements on form var1 -> exp"
  input VariableReplacements repl;
protected
  list<DAE.ComponentRef> srcs;
  list<DAE.Exp> dsts;
  list<tuple<DAE.ComponentRef,DAE.Exp>> tplLst;
algorithm
  if isSome(repl.derConst) then
    (srcs, dsts) := getCrefExpTableEntries(Util.getOption(repl.derConst));
    tplLst := List.zip(srcs, dsts);
    print("\nDerConstReplacements: (");
    print(String(listLength(tplLst)));
    print(")\n");
    print("========================================\n");
    print(stringDelimitList(List.map(tplLst,printReplacementTupleStr), "\n"));
    print("\n");
  end if;
end dumpDerConstReplacements;

protected function printReplacementTupleStr "help function to dumpReplacements"
  input tuple<DAE.ComponentRef,DAE.Exp> tpl;
  output String str;
algorithm
  // optional exteded type debugging
  //str := ComponentReference.debugPrintComponentRefTypeStr(Util.tuple21(tpl)) + " -> " + ExpressionDump.debugPrintComponentRefExp(Util.tuple22(tpl));
  // Normal debugging, without type&dimension information on crefs.
  str := ComponentReference.printComponentRefStr(Util.tuple21(tpl)) + " -> " + ExpressionDump.printExpStr(Util.tuple22(tpl));
end printReplacementTupleStr;

public function getConstantReplacements"gets a clean replacement set containing only constant replacement rules"
  input VariableReplacements replIn;
  output VariableReplacements replOut;
protected
  list<DAE.ComponentRef> crefs;
  list<DAE.Exp> exps;
algorithm
  (crefs,exps) := getAllReplacements(replIn);
  (exps,crefs):= List.filterOnTrueSync(exps,Expression.isEvaluatedConst,crefs);
  replOut := emptyReplacements();
  replOut := addReplacements(replOut,crefs,exps,NONE());
end getConstantReplacements;

annotation(__OpenModelica_Interface="backend");
end BackendVarTransform;
