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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if(!callGraph.contains(csMethod)){
            callGraph.addReachableMethod(csMethod);
            csMethod.getMethod().getIR().forEach(stmt -> stmt.accept(new StmtProcessor(csMethod)));
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            Pointer ptr = csManager.getCSVar(context, stmt.getLValue());
            Obj obj = heapModel.getObj(stmt);
            Context ctx = contextSelector.selectHeapContext(csMethod, obj);
            PointsToSet pst = PointsToSetFactory.make(csManager.getCSObj(ctx, obj));
            workList.addEntry(ptr, pst);
            return null;
        }
        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(csManager.getCSVar(context, stmt.getRValue()),
                    csManager.getCSVar(context, stmt.getLValue()));
            return null;
        }
        @Override
        public Void visit(LoadField stmt) {
            if(stmt.isStatic()) {
                addPFGEdge(csManager.getStaticField(stmt.getFieldRef().resolve()), csManager.getCSVar(context, stmt.getLValue()));
            }
            return null;
        }
        @Override
        public Void visit(StoreField stmt) {
            if(stmt.isStatic()) {
                addPFGEdge(csManager.getCSVar(context, stmt.getRValue()), csManager.getStaticField(stmt.getFieldRef().resolve()));
            }
            return null;
        }
        @Override
        public Void visit(Invoke stmt) {
            if(stmt.isStatic()){
                JMethod callee = resolveCallee(null, stmt);//null because it is static
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
                Context calleectx = contextSelector.selectContext(csCallSite, callee);
                Invoke callSite = csCallSite.getCallSite();
                Context callerctx = csCallSite.getContext();
                CSMethod cscallee = csManager.getCSMethod(calleectx, callee);
                if(!callGraph.getCalleesOf(csCallSite).contains(cscallee)){
                    CallKind kind = null;
                    if(stmt.isVirtual()) kind = CallKind.VIRTUAL;
                    else if(stmt.isSpecial()) kind = CallKind.SPECIAL;
                    else if(stmt.isInterface()) kind = CallKind.INTERFACE;
                    else if(stmt.isStatic()) kind = CallKind.STATIC;
                    if(kind != null){
                        callGraph.addEdge(new Edge<>(kind, csCallSite, cscallee));
                        addReachable(cscallee);
                        //参数
                        List<Var> params = callee.getIR().getParams();
                        for(int i = 0; i < params.size(); i++){
                            addPFGEdge(csManager.getCSVar(callerctx, callSite.getRValue().getArg(i)), csManager.getCSVar(calleectx, params.get(i)));
                        }
                        Var retvar = callSite.getLValue();
                        if(retvar != null){
                            List<Var> ret_vars = callee.getIR().getReturnVars();
                            for(Var ret: ret_vars){
                                addPFGEdge(csManager.getCSVar(calleectx, ret), csManager.getCSVar(callerctx, retvar));
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
            if(!pts.isEmpty()){
                workList.addEntry(target, pts);
            }
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
            // delta
            PointsToSet diff = propagate(cur_ptr, cur_pts);
            if(cur_ptr instanceof CSVar ptr){
                Var x = ptr.getVar();
                Context ctx = ptr.getContext();
                diff.forEach(obj -> {
                    x.getStoreFields().forEach(store_stmt -> { //x.f = y
                        addPFGEdge(csManager.getCSVar(ctx, store_stmt.getRValue()), csManager.getInstanceField(obj, store_stmt.getFieldRef().resolve()));
                    });
                    x.getLoadFields().forEach(load_stmt -> { // y = x.f
                        addPFGEdge(csManager.getInstanceField(obj, load_stmt.getFieldRef().resolve()), csManager.getCSVar(ctx, load_stmt.getLValue()));
                    });
                    x.getStoreArrays().forEach(array_store_stmt -> { //x[i] = y
                        addPFGEdge(csManager.getCSVar(ctx, array_store_stmt.getRValue()), csManager.getArrayIndex(obj));
                    });
                    x.getLoadArrays().forEach(array_load_stmt -> { //y = x[i]
                        addPFGEdge(csManager.getArrayIndex(obj), csManager.getCSVar(ctx, array_load_stmt.getLValue()));
                    });
                    // ProcessCall
                    processCall(ptr, obj);
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
        PointsToSet diff = PointsToSetFactory.make();
        PointsToSet ptn = pointer.getPointsToSet();
        pointsToSet.forEach(obj -> {
            if(!ptn.contains(obj)){
                diff.addObject(obj);
            }
        });
        if(!diff.isEmpty()){
            // pt(n) = pt(n) U diff
            diff.forEach(obj -> {
                ptn.addObject(obj);
            });
            //更新pointer中的pointsToSet
            ptn.forEach(obj -> {
                if(pointer.getPointsToSet().contains(obj)) pointer.getPointsToSet().addObject(obj);
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
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        recv.getVar().getInvokes().forEach(callSite -> {
            JMethod callee = resolveCallee(recvObj, callSite);
            CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(), callSite);
            Context calleectx = contextSelector.selectContext(csCallSite, recvObj, callee);
            CSMethod cscallee = csManager.getCSMethod(calleectx, callee);
            workList.addEntry(csManager.getCSVar(calleectx, callee.getIR().getThis()), PointsToSetFactory.make(recvObj));
            Context callerctx = csCallSite.getContext();
            if(!callGraph.getCalleesOf(csCallSite).contains(cscallee)){
                CallKind kind = null;
                if(callSite.isVirtual()) kind = CallKind.VIRTUAL;
                else if(callSite.isSpecial()) kind = CallKind.SPECIAL;
                else if(callSite.isInterface()) kind = CallKind.INTERFACE;
                else if(callSite.isStatic()) kind = CallKind.STATIC;
                if(kind != null){
                    callGraph.addEdge(new Edge<>(kind, csCallSite, cscallee));
                    addReachable(cscallee);
                    //参数
                    List<Var> params = callee.getIR().getParams();
                    for(int i = 0; i < params.size(); i++){
                        addPFGEdge(csManager.getCSVar(callerctx, callSite.getRValue().getArg(i)), csManager.getCSVar(calleectx, params.get(i)));
                    }
                    Var retvar = callSite.getLValue();
                    if(retvar != null){
                        List<Var> ret_vars = callee.getIR().getReturnVars();
                        for(Var ret: ret_vars){
                            addPFGEdge(csManager.getCSVar(calleectx, ret), csManager.getCSVar(callerctx, retvar));
                        }
                    }
                }
            }
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
