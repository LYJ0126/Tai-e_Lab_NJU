/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.LinkedList;
import java.util.Queue;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        // worklist algorithm(forward)
        Queue<Node> worklist = new LinkedList<Node>();
        worklist.addAll(cfg.getNodes());
        while(!worklist.isEmpty()){
            Node current = worklist.poll();
            Fact inFact = result.getInFact(current);
            Fact outFact = result.getOutFact(current);
            for(Node pred: cfg.getPredsOf(current)){//in[B] = meet(out[P],P is pred of B)
                analysis.meetInto(result.getOutFact(pred), inFact);
            }
            boolean flag = analysis.transferNode(current, inFact, outFact);
            if(flag){
                for(Node succ: cfg.getSuccsOf(current)){
                    worklist.add(succ);
                }
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        // worklist algorithm(backward)
        Queue<Node> worklist = new LinkedList<Node>();
        worklist.addAll(cfg.getNodes());
        while(!worklist.isEmpty()){
            Node current = worklist.poll();
            Fact inFact = result.getInFact(current);
            Fact outFact = result.getOutFact(current);
            //outFact[node] = \cup_{s a successor of node} inFact[s]
            //inFact[node] = use[node] \cup (outFact[node] - def[node])
            for(Node succ: cfg.getSuccsOf(current)){
                analysis.meetInto(result.getInFact(succ), outFact);
            }
            boolean flag = analysis.transferNode(current, inFact, outFact);
            if(flag) {
                for (Node pred : cfg.getPredsOf(current)) {
                    worklist.add(pred);
                }
            }
        }
    }
}
