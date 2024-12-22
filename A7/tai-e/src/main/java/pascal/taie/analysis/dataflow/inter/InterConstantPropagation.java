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

package pascal.taie.analysis.dataflow.inter;

//import jas.Pair;
import pascal.taie.util.collection.Pair;
import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.ir.proginfo.FieldRef;
//import soot.jimple.FieldRef;

import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;
    public static final Map<Obj, Set<Var>> aliasMap = new HashMap<>();
    public static final Map<Pair<?,?>, Value> valueMap = new HashMap<>();
    public static final Map<Pair<JClass, FieldRef>, Set<LoadField>> staticloadFieldMap = new HashMap<>();
    public static PointerAnalysisResult pta;


    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        //PointerAnalysisResult pta = World.get().getResult(ptaId);
        pta = World.get().getResult(ptaId);
        // You can do initialization work here
        for(Var var: pta.getVars()){
            for(Obj obj: pta.getPointsToSet(var)){
                Set<Var> temp = aliasMap.getOrDefault(obj, new HashSet<>());
                temp.add(var);
                aliasMap.put(obj, temp);
            }
        }
        icfg.getNodes().forEach(stmt -> {
            if(stmt instanceof LoadField loadstmt && loadstmt.getFieldAccess() instanceof StaticFieldAccess staticaccess){
                Pair<JClass, FieldRef> accesspair = new Pair<>(staticaccess.getFieldRef().getDeclaringClass(), staticaccess.getFieldRef());
                Set<LoadField> temp = staticloadFieldMap.getOrDefault(accesspair, new HashSet<>());
                temp.add(loadstmt);
                staticloadFieldMap.put(accesspair, temp);
            }
        });
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        //return false;
        AtomicBoolean flag = new AtomicBoolean(false);
        in.forEach((var, value) -> {
            if (out.update(var, value)) {
                flag.set(true);
            }
        });
        return flag.get();
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        //return false;
        return cp.transferNode(stmt, in, out);//same as intraprocedural constant propagation
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        //return null;
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        //return null;
        Invoke callsite = (Invoke) edge.getSource();
        Var lvar = callsite.getLValue();
        CPFact res = out.copy();
        if(lvar != null){
            res.remove(lvar);
        }
        return res;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        //return null;
        Invoke callsite = (Invoke) edge.getSource();
        CPFact res = new CPFact();
        //pass argument values
        List<Var> parameters = callsite.getRValue().getArgs();//传入的参数
        List<Var> args = edge.getCallee().getIR().getParams();//函数的参数(形参)
        for(int i = 0; i < args.size(); i++){
            res.update(args.get(i), callSiteOut.get(parameters.get(i)));
        }
        return res;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        //return null;
        Invoke callsite = (Invoke) edge.getCallSite();
        CPFact res = new CPFact();
        Var lvar = callsite.getLValue();
        if(lvar != null){
            edge.getReturnVars().forEach(var -> res.update(lvar, cp.meetValue(res.get(lvar), returnOut.get(var))));
        }
        return res;
    }
}
