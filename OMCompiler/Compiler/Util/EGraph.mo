/*
 * This file is part of OpenModelica.
 *
 * Copyright (c) 1998-CurrentYear, Open Source Modelica Consortium (OSMC),
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

encapsulated uniontype EGraph
  "An interface to egg, a rust implementation of e-graphs."

protected
  import Expression = NFExpression;
  import Global;

public
  function simplifyExp
    input output Expression exp;
  protected
    EGraph egraph = getEGraph();
  algorithm
    simplifyExp_impl(egraph.rules, Expression.toPrefixString(exp));
  end simplifyExp;

protected
  record E_GRAPH
    Rules rules           "";
//    Runner runner         "";
//    Extractor extractor   "";
  end E_GRAPH;

  function getEGraph
    output EGraph egraph;
  protected
    Option<EGraph> ograph = getGlobalRoot(Global.eGraph);
  algorithm
    egraph := match ograph
      case SOME(egraph) then egraph;
      else algorithm
        egraph := E_GRAPH(rules = Rules());
        setGlobalRoot(Global.eGraph, SOME(egraph));
      then egraph;
    end match;
  end getEGraph;

  class Rules
    extends ExternalObject;
    function constructor
      output Rules rules;
    external "C"
      rules = egg_make_rules() annotation(Library="omcruntime");
    end constructor;
    function destructor
      input Rules rules;
    external "C"
      egg_free_rules(rules) annotation(Library="omcruntime");
    end destructor;
  end Rules;

//  class Runner
//    extends ExternalObject;
//  end Runner;
//
//  class Extractor
//    extends ExternalObject;
//  end Extractor;

  function simplifyExp_impl
    input Rules r;
    input String e "expression in prefix notation";
    external "C" egg_simplify_expr(r, e) annotation(Library="omcruntime");
  end simplifyExp_impl;

annotation(__OpenModelica_Interface="util");
end EGraph;
