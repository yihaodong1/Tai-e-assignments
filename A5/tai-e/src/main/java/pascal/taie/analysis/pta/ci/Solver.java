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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;
import polyglot.ast.Call;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if(callGraph.addReachableMethod(method)) {

            method.getIR().forEach(stmt -> {
                stmt.accept(stmtProcessor);
            });

        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(Copy stmt) {
            Pointer source = pointerFlowGraph.getVarPtr(stmt.getRValue());
            Pointer target = pointerFlowGraph.getVarPtr(stmt.getLValue());
            addPFGEdge(source, target);
            return null;
        }
        @Override
        public Void visit(LoadField loadField) {
            if(loadField.isStatic()){
                Pointer source = pointerFlowGraph.getStaticField(loadField.getRValue().getFieldRef().resolve());
                Pointer target = pointerFlowGraph.getVarPtr(loadField.getLValue());
                addPFGEdge(source, target);
            }
            return null;
        }
        @Override
        public Void visit(StoreField storeField) {
            if(storeField.isStatic()){
                Pointer source = pointerFlowGraph.getVarPtr(storeField.getRValue());
                Pointer target = pointerFlowGraph.getStaticField(storeField.getLValue().getFieldRef().resolve());
                addPFGEdge(source, target);
            }
            return null;
        }
        @Override
        public Void visit(New newInstance) {
            Pointer p = pointerFlowGraph.getVarPtr(newInstance.getLValue());
            workList.addEntry(p, new PointsToSet(heapModel.getObj(newInstance)));
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if(stmt.isStatic()){
                JMethod m = resolveCallee(null, stmt);
                CallKind k = getCallKind(stmt);
                if(callGraph.addEdge(new Edge<>(k, stmt, m))){
                    addReachable(m);
                    for(int i = 0; i < stmt.getInvokeExp().getArgs().size(); i++){
                        addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getInvokeExp().getArgs().get(i))
                                , pointerFlowGraph.getVarPtr(m.getIR().getParams().get(i)));
                    }
                    m.getIR().getReturnVars().forEach(mret->{
                        if(stmt.getLValue() != null)
                            addPFGEdge(pointerFlowGraph.getVarPtr(mret),
                                    pointerFlowGraph.getVarPtr(stmt.getLValue()));
                    });
                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if(pointerFlowGraph.addEdge(source, target)){
            if(!source.getPointsToSet().isEmpty()){
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {

            pascal.taie.analysis.pta.ci.WorkList.Entry entry = workList.pollEntry();
            PointsToSet delta = propagate(entry.pointer(), entry.pointsToSet());
            if(entry.pointer() instanceof VarPtr varPtr){
                Var var = varPtr.getVar();
                for(Obj obj: delta){
                    callGraph.reachableMethods().forEach(jMethod -> {
                        jMethod.getIR().forEach(stmt -> {
                            if(stmt instanceof LoadArray loadArray
                            && var.getLoadArrays().contains(stmt)){
                                addPFGEdge(pointerFlowGraph.getArrayIndex(obj)
                                        , pointerFlowGraph.getVarPtr(loadArray.getLValue()));
                            }
                            if(stmt instanceof LoadField loadField
                            && var.getLoadFields().contains(stmt)
                            && !loadField.isStatic()){
                                addPFGEdge(pointerFlowGraph.getInstanceField(obj
                                                , loadField.getRValue().getFieldRef().resolve())
                                        , pointerFlowGraph.getVarPtr(loadField.getLValue()));
                            }
                            if(stmt instanceof StoreArray storeArray
                                    &&  var.getStoreArrays().contains(stmt)){
                                addPFGEdge(pointerFlowGraph.getVarPtr(storeArray.getRValue())
                                        , pointerFlowGraph.getArrayIndex(obj));
                            }
                            if(stmt instanceof StoreField storeField
                            && var.getStoreFields().contains(stmt)
                            && !storeField.isStatic()){
                                addPFGEdge(pointerFlowGraph.getVarPtr(storeField.getRValue())
                                , pointerFlowGraph.getInstanceField(obj
                                                , storeField.getLValue().getFieldRef().resolve()));

                            }

                        });
                    });
                    processCall(var, obj);
                }
            }


        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        if(pointsToSet.isEmpty()){
            return pointsToSet;
        }
        PointsToSet delta = new  PointsToSet();
        pointsToSet.forEach(obj -> {
            if(!pointer.getPointsToSet().contains(obj)) {
                delta.addObject(obj);
                pointer.getPointsToSet().addObject(obj);
            }
        });
        pointerFlowGraph.getSuccsOf(pointer).forEach(pt-> {
            workList.addEntry(pt, delta);
        });
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        Set<JMethod> newAdd = new HashSet<>();
        callGraph.reachableMethods().forEach(jMethod -> {
            jMethod.getIR().forEach(stmt -> {
                if(stmt instanceof Invoke invoke
                        && var.getInvokes().contains(invoke)){
                    JMethod m = resolveCallee(recv, invoke);
//                    if(!m.isStatic())
                        workList.addEntry(pointerFlowGraph.getVarPtr(m.getIR().getThis())
                            , new PointsToSet(recv));
                    CallKind k = getCallKind(invoke);
                    if(callGraph.addEdge(new Edge<>(k, invoke, m))){
//                        addReachable(m);
                        // avoid addReachable directly, or will raise exception
                        // ConcurrentModificationException
                        newAdd.add(m);
                        for(int i = 0; i < invoke.getInvokeExp().getArgs().size(); i++){
                            addPFGEdge(pointerFlowGraph.getVarPtr(invoke.getInvokeExp().getArgs().get(i))
                                    , pointerFlowGraph.getVarPtr(m.getIR().getParams().get(i)));
                        }
                        m.getIR().getReturnVars().forEach(mret->{
                            if(invoke.getLValue() != null)
                                addPFGEdge(pointerFlowGraph.getVarPtr(mret),
                                    pointerFlowGraph.getVarPtr(invoke.getLValue()));
                        });
                    }
                }
            });
        });
        for(JMethod jMethod: newAdd){
            addReachable(jMethod);
        }
    }

    private static CallKind getCallKind(Invoke stmt) {
        CallKind k = CallKind.OTHER;
        if(stmt.isStatic())
            k = CallKind.STATIC;
        else if(stmt.isInterface())
            k = CallKind.INTERFACE;
        else if(stmt.isDynamic())
            k = CallKind.DYNAMIC;
        else if(stmt.isSpecial())
            k = CallKind.SPECIAL;
        else if(stmt.isVirtual())
            k = CallKind.VIRTUAL;
        return k;
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
