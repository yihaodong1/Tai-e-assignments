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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        Stmt entry = cfg.getEntry();
        Queue<Stmt> queue = new LinkedList<>();
        queue.add(entry);
        Set<Stmt> traveled = new HashSet<>();
        while (!queue.isEmpty()) {
            Stmt stmt = queue.poll();
            traveled.add(stmt);
            CPFact fact = constants.getInFact(stmt);
            cfg.getOutEdgesOf(stmt).forEach(edge -> {
                if(!traveled.contains(edge.getTarget())) {
                    switch (edge.getKind()) {
                        case GOTO, ENTRY, FALL_THROUGH, RETURN -> {

                            queue.add(edge.getTarget());
                        }
                        case IF_TRUE -> {
                            ConditionExp c = ((If) stmt).getCondition();
                            Value val = ConstantPropagation.evaluate(c, fact);
                            if(val.isConstant() && val.getConstant() == 1)
                                queue.add(edge.getTarget());
                            else if(!val.isConstant())
                                // not a constant, but maybe true
                                queue.add(edge.getTarget());
                        }
                        case IF_FALSE -> {
                            ConditionExp c = ((If) stmt).getCondition();
                            Value val = ConstantPropagation.evaluate(c, fact);
                            if(val.isConstant() && val.getConstant() == 0)
                                queue.add(edge.getTarget());
                            else if(!val.isConstant())
                                // not a constant, but maybe true
                                queue.add(edge.getTarget());
                        }
                        case SWITCH_CASE -> {
                            Var var = ((SwitchStmt) stmt).getVar();
                            Value val = ConstantPropagation.evaluate(var, fact);
                            if (val.isConstant()) {
                                int c = val.getConstant();
                                int caseval = edge.getCaseValue();
                                if (c == caseval) {
                                    queue.add(edge.getTarget());
                                }
                            }else // when var not constant, maybe match
                                queue.add(edge.getTarget());

                        }
                        case SWITCH_DEFAULT -> {
                            List<Integer> list = ((SwitchStmt)stmt).getCaseValues();
                            Var var = ((SwitchStmt) stmt).getVar();
                            Value val = ConstantPropagation.evaluate(var, fact);
                            if(!val.isConstant() || !list.contains(val.getConstant())) {
                                queue.add(edge.getTarget());
                            }
                        }
                    }
                }
            });
        }
        for (Stmt stmt : cfg.getNodes()) {
            if(!traveled.contains(stmt) && !cfg.isExit(stmt)) {
                deadCode.add(stmt);
            }
        }
        for(Stmt node : cfg.getNodes()) {
            if(node instanceof AssignStmt) {
                SetFact<Var>out = liveVars.getOutFact(node);
                if(out != null) {
                    LValue l = ((AssignStmt<?, ?>) node).getLValue();
                    RValue r = ((AssignStmt<?, ?>) node).getRValue();
                    if(l instanceof Var) {
                        if(!out.contains((Var)l) && hasNoSideEffect(r)){
                            deadCode.add(node);
                        }
                    }
                }
            }
        }
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
