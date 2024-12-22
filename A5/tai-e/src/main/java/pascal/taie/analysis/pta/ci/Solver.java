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
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;

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
        if(callGraph.addReachableMethod(method)){
            method.getIR().getStmts().forEach(stmt -> {
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
        public Void visit(New stmt) {
            Pointer ptr = pointerFlowGraph.getVarPtr(stmt.getLValue());
            workList.addEntry(ptr, new PointsToSet(heapModel.getObj(stmt)));
            return null;
        }
        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), pointerFlowGraph.getVarPtr(stmt.getLValue()));
            return null;
        }
        @Override
        public Void visit(LoadField stmt) {
            if(stmt.isStatic()){
                addPFGEdge(pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()), pointerFlowGraph.getVarPtr(stmt.getLValue()));
            }
            return null;
        }
        @Override
        public Void visit(StoreField stmt) {
            if(stmt.isStatic()){
                addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()));
            }
            return null;
        }
        @Override
        public Void visit(Invoke stmt){
            if(stmt.isStatic()){
                JMethod callee = resolveCallee(null, stmt);
                if(callee != null){
                    //processCall(stmt, callee);
                    if(!callGraph.getCalleesOf(stmt).contains(callee)){
                        CallKind kind = null;
                        if(stmt.isVirtual()) kind = CallKind.VIRTUAL;
                        else if(stmt.isSpecial()) kind = CallKind.SPECIAL;
                        else if(stmt.isInterface()) kind = CallKind.INTERFACE;
                        else if(stmt.isStatic()) kind = CallKind.STATIC;
                        if(kind != null){
                            callGraph.addEdge(new Edge<>(kind, stmt, callee));
                            addReachable(callee);
                            //参数
                            List<Var> params = callee.getIR().getParams();
                            for(int i = 0; i < params.size(); i++){
                                addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue().getArg(i)), pointerFlowGraph.getVarPtr(params.get(i)));
                            }
                        }
                        //返回值
                        Var retvar = stmt.getLValue();
                        if(retvar != null){
                            List<Var> ret_vars = callee.getIR().getReturnVars();
                            for(Var ret : ret_vars){
                                addPFGEdge(pointerFlowGraph.getVarPtr(ret), pointerFlowGraph.getVarPtr(retvar));
                            }
                        }
                    }
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
        if(!pointerFlowGraph.getSuccsOf(source).contains(target)){
            pointerFlowGraph.addEdge(source, target);
            PointsToSet pts = source.getPointsToSet();
            if(!pts.isEmpty()) workList.addEntry(target, pts);//若source已经有指向的对象，则将source的指向对象传递给targets
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while(!workList.isEmpty()){
            WorkList.Entry cur_entry = workList.pollEntry();
            Pointer cur_ptr = cur_entry.pointer();
            PointsToSet cur_pts = cur_entry.pointsToSet();
            PointsToSet diff = propagate(cur_ptr, cur_pts);
            if(cur_ptr instanceof VarPtr varPtr){
                Var x = varPtr.getVar();
                diff.forEach(obj -> {
                    x.getStoreFields().forEach(store_stmt -> {// x.f = y
                        addPFGEdge(pointerFlowGraph.getVarPtr(store_stmt.getRValue()), pointerFlowGraph.getInstanceField(obj, store_stmt.getFieldRef().resolve()));
                    });
                    x.getLoadFields().forEach(load_stmt -> {// y = x.f
                        addPFGEdge(pointerFlowGraph.getInstanceField(obj, load_stmt.getFieldRef().resolve()), pointerFlowGraph.getVarPtr(load_stmt.getLValue()));
                    });
                    x.getStoreArrays().forEach(array_store_stmt -> {// x[i] = y
                        addPFGEdge(pointerFlowGraph.getVarPtr(array_store_stmt.getRValue()), pointerFlowGraph.getArrayIndex(obj));
                    });
                    x.getLoadArrays().forEach(array_load_stmt -> {// y = x[i]
                        addPFGEdge(pointerFlowGraph.getArrayIndex(obj), pointerFlowGraph.getVarPtr(array_load_stmt.getLValue()));
                    });
                    processCall(x, obj);
                });
            }

        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        //return null;
        //计算差集 pts - pt(n)
        PointsToSet diff = new PointsToSet();
        PointsToSet ptn = pointer.getPointsToSet();
        pointsToSet.forEach(obj -> {
            if(!ptn.contains(obj)){
                diff.addObject(obj);
            }
        });
        if(!diff.isEmpty()){
            // pt(n) = pt(n) ∪ diff
            diff.forEach(obj -> {
                ptn.addObject(obj);
            });
            //更新pointer的pointsToSet
            ptn.forEach(obj->{
                if(!pointer.getPointsToSet().contains(obj)) pointer.getPointsToSet().addObject(obj);
            });
            //更新worklist
            pointerFlowGraph.getSuccsOf(pointer).forEach(succ -> {
                workList.addEntry(succ, diff);
            });
        }
        return diff;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        var.getInvokes().forEach(callsite -> {
            JMethod callee = resolveCallee(recv, callsite); //等同dispatch
            workList.addEntry(pointerFlowGraph.getVarPtr(callee.getIR().getThis()), new PointsToSet(recv));
            if(!callGraph.getCalleesOf(callsite).contains(callee)){
                CallKind kind = null;
                if(callsite.isVirtual()) kind = CallKind.VIRTUAL;
                else if(callsite.isSpecial()) kind = CallKind.SPECIAL;
                else if(callsite.isInterface()) kind = CallKind.INTERFACE;
                else if(callsite.isStatic()) kind = CallKind.STATIC;
                if(kind != null){
                    callGraph.addEdge(new Edge<>(kind, callsite, callee));
                    addReachable(callee);
                    //参数
                    List<Var> params = callee.getIR().getParams();
                    for(int i = 0; i < params.size(); i++){
                        addPFGEdge(pointerFlowGraph.getVarPtr(callsite.getRValue().getArg(i)), pointerFlowGraph.getVarPtr(params.get(i)));
                    }
                }
                //返回值
                Var retvar = callsite.getLValue();
                if(retvar != null){
                    List<Var> ret_vars = callee.getIR().getReturnVars();
                    for(Var ret : ret_vars){
                        addPFGEdge(pointerFlowGraph.getVarPtr(ret), pointerFlowGraph.getVarPtr(retvar));
                    }
                }
            }
        });
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
