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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;

import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Pair;
//import java.lang.reflect.Type;
import javax.annotation.Nullable;
import java.util.Map;
import java.util.*;
import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me
    public Obj getTaintSource(Invoke callsite, JMethod callee) {
        Type retype = callee.getReturnType();
        Source source = new Source(callee, retype);
        if(config.getSources().contains(source)) return manager.makeTaint(callsite, retype);
        return null;
    }

    public Set<Pair<Var, Obj>> TaintTransfer(CSCallSite csCallSite, JMethod callee, @Nullable CSVar base) {
        Invoke callsite = csCallSite.getCallSite();
        PointerAnalysisResult ptares = solver.getResult();
        Var lvar = callsite.getLValue();
        Set<Pair<Var, Obj>> res = new HashSet<>();
        TaintTransfer transfer;
        Type restype = callee.getReturnType();
        List<Var> args = callsite.getInvokeExp().getArgs();
        int len = args.size();
        if(base != null) {//非静态方法
            Type basetype = base.getType();
            // base to result
            transfer = new TaintTransfer(callee, TaintTransfer.BASE, TaintTransfer.RESULT, restype);
            if(config.getTransfers().contains(transfer) && lvar != null) {
                Set<CSObj> pts = ptares.getPointsToSet(base);
                pts.forEach(csObj -> {
                    Obj obj = csObj.getObject();
                    if(manager.isTaint(obj)) {
                        res.add(new Pair<>(lvar, manager.makeTaint(manager.getSourceCall(obj), restype)));
                    }
                });
            }
            // arg to base
            for(int i = 0; i < len; ++i) {
                Var arg = args.get(i);
                Set<CSObj> pts = ptares.getPointsToSet(csManager.getCSVar(csCallSite.getContext(), arg));
                transfer = new TaintTransfer(callee, i, TaintTransfer.BASE, basetype);
                if(config.getTransfers().contains(transfer)) {
                    pts.forEach(csObj -> {
                        Obj obj = csObj.getObject();
                        if(manager.isTaint(obj)) {
                            res.add(new Pair<>(base.getVar(), manager.makeTaint(manager.getSourceCall(obj), restype)));
                        }
                    });
                }
            }
        }
        // arg to result
        for(int i = 0; i < len; ++i) {
            Var arg = args.get(i);
            Set<CSObj> pts = ptares.getPointsToSet(csManager.getCSVar(csCallSite.getContext(), arg));
            transfer = new TaintTransfer(callee, i, TaintTransfer.RESULT, restype);
            if(config.getTransfers().contains(transfer) && lvar != null) {
                pts.forEach(csObj -> {
                    Obj obj = csObj.getObject();
                    if(manager.isTaint(obj)) {
                        res.add(new Pair<>(lvar, manager.makeTaint(manager.getSourceCall(obj), restype)));
                    }
                });
            }
        }

        return res;
    }

    public boolean isTaint(Obj obj) { //用于判断是否为污点
        return manager.isTaint(obj);
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        CallGraph<CSCallSite, CSMethod> callgraph = result.getCSCallGraph();
        callgraph.reachableMethods().forEach(method -> {
            for(CSCallSite csCallSite : callgraph.getCallersOf(method)) {
                Invoke callsite = csCallSite.getCallSite();
                JMethod callee = method.getMethod();
                List<Var> args = callsite.getInvokeExp().getArgs();
                for(int i = 0; i < args.size(); ++i) {
                    if(config.getSinks().contains(new Sink(callee, i))) {
                        Set<Obj> pts = result.getPointsToSet(args.get(i));
                        for(Obj obj : pts) {
                            if(manager.isTaint(obj)) {
                                taintFlows.add(new TaintFlow(manager.getSourceCall(obj), callsite, i));
                            }
                        }
                    }
                }
            }
        });
        return taintFlows;
    }
}
