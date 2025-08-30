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

class IterativeSolver<Node, Fact> extends Solver<Node, Fact> {

    public IterativeSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
//        boolean flag = false;
//        do {
//            flag = false;
//            for(Node node: cfg)
//            {
//                if(cfg.isExit(node)){
//
//                }else {
//                    result.setOutFact(node, analysis.newInitialFact());
//                    cfg.getSuccsOf(node).forEach(fact->{
//                        analysis.meetInto(result.getInFact(fact), result.getOutFact(node));
//                    });
//                    flag |= analysis.transferNode(node,
//                            result.getInFact(node), result.getOutFact(node));
//                }
//            }
//        }while(flag);
        Queue<Node> queue = new LinkedList<Node>();
        for(Node node : cfg.getNodes()) {
            if(cfg.isExit(node)) {
                continue;
            }
            queue.add(node);
        }
        while (!queue.isEmpty()) {
            Node node = queue.poll();
            result.setOutFact(node, analysis.newInitialFact());
            cfg.getSuccsOf(node).forEach(fact->{
                analysis.meetInto(result.getInFact(fact), result.getOutFact(node));
            });
            if(analysis.transferNode(node, result.getInFact(node), result.getOutFact(node) )) {
                queue.addAll(cfg.getPredsOf(node));
            }
        }
    }
}
