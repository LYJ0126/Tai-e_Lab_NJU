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

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JClass;
import pascal.taie.util.collection.SetQueue;
import pascal.taie.ir.proginfo.FieldRef;
//import soot.jimple.FieldRef;

//import jas.Pair;
import pascal.taie.util.collection.Pair;
import java.util.*;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;
import static pascal.taie.analysis.dataflow.inter.InterConstantPropagation.*;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // TODO - finish me
        for(Node node:icfg){
            result.setOutFact(node, analysis.newInitialFact());
            result.setInFact(node, analysis.newInitialFact());
        }
        icfg.entryMethods().forEach(method -> {
            Node entry = icfg.getEntryOf(method);
            result.setOutFact(entry, analysis.newBoundaryFact(entry));
        });
    }

    private Value meet(Value v1, Value v2) {
        //对应格上的meet操作
        if(v1.isNAC() || v2.isNAC()) {
            return v1.isNAC() ? v1 : v2;
        }
        else if(v1.isUndef() || v2.isUndef()) {
            return v1.isUndef() ? v2 : v1;
        }
        else if(v1.equals(v2)) return v1;
        else return Value.getNAC();
    }

    private void doSolve() {
        // TODO - finish me
        workList = new LinkedList<>();
        workList.addAll(icfg.getNodes());
        while(!workList.isEmpty()){
            Node current = workList.poll();
            CPFact inFact = (CPFact) result.getInFact(current);
            CPFact outFact = (CPFact) result.getOutFact(current);
            for(ICFGEdge<Node> edge :icfg.getInEdgesOf(current)){
                analysis.meetInto(analysis.transferEdge(edge, result.getOutFact(edge.getSource())), (Fact)inFact);
            }
            // field
            if((Stmt)current instanceof StoreField s){
                if(ConstantPropagation.canHoldInt(s.getRValue())){
                    if(s.getFieldAccess() instanceof InstanceFieldAccess instanceacess){// 实例字段
                        Var base = instanceacess.getBase();
                        pta.getPointsToSet(base).forEach(obj -> {
                            Pair<Obj, FieldRef> acesspair = new Pair<>(obj, instanceacess.getFieldRef());
                            Value oldvalue = valueMap.getOrDefault(acesspair, Value.getUndef());
                            Value newvalue = ConstantPropagation.evaluate(s.getRValue(), inFact);
                            // meet
                            newvalue = meet(oldvalue, newvalue);
                            valueMap.put(acesspair, newvalue);
                            // 更新aliasMap
                            if(!oldvalue.equals(newvalue)) {
                                Set<Var> aliasvars = aliasMap.get(obj);
                                for(Var aliasvar : aliasvars){
                                    aliasvar.getLoadFields().forEach(loadstmt -> {
                                        if(loadstmt.getFieldAccess().getFieldRef().equals(s.getFieldRef())){
                                            workList.offer((Node)loadstmt);
                                        }
                                    });
                                }
                            }
                        });
                    }
                    else if(s.getFieldAccess() instanceof StaticFieldAccess staticacess){
                        Pair<JClass, FieldRef> acesspair = new Pair<>(staticacess.getFieldRef().getDeclaringClass(), staticacess.getFieldRef());
                        Value oldvalue = valueMap.getOrDefault(acesspair, Value.getUndef());
                        Value newvalue = ConstantPropagation.evaluate(s.getRValue(), inFact);
                        // meet
                        newvalue = meet(oldvalue, newvalue);
                        valueMap.put(acesspair, newvalue);
                        // 更新staticloadFieldMap
                        if(!oldvalue.equals(newvalue)) {
                            Set<LoadField> loadfields = staticloadFieldMap.getOrDefault(acesspair, new HashSet<>());
                            for(LoadField loadfield : loadfields){
                                workList.offer((Node)loadfield);
                            }

                        }
                    }
                }
            }
            // array
            if((Stmt)current instanceof StoreArray s){
                if(ConstantPropagation.canHoldInt(s.getRValue())){
                    ArrayAccess access = s.getArrayAccess();
                    Value index = ConstantPropagation.evaluate(access.getIndex(), inFact);
                    if(!index.isUndef()){
                        Var base = access.getBase();
                        pta.getPointsToSet(base).forEach(obj -> {
                            Pair<Obj, Value> acesspair = new Pair<>(obj, index);
                            Value oldvalue = valueMap.getOrDefault(acesspair, Value.getUndef());
                            Value newvalue = ConstantPropagation.evaluate(s.getRValue(), inFact);
                            // meet
                            newvalue = meet(oldvalue, newvalue);
                            valueMap.put(acesspair, newvalue);
                            // 更新aliasMap
                            if(!oldvalue.equals(newvalue)){
                                Set<Var> aliasvars = aliasMap.get(obj);
                                for(Var aliasvar : aliasvars){
                                    aliasvar.getLoadArrays().forEach(loadstmt -> {
                                        workList.offer((Node)loadstmt);
                                    });
                                }
                            }
                        });
                    }
                }
            }
            boolean flag = analysis.transferNode(current, (Fact)inFact, (Fact)outFact);
            if(flag){
                for(ICFGEdge<Node> edge :icfg.getOutEdgesOf(current)){
                    workList.add(edge.getTarget());
                }
            }
            result.setInFact(current, (Fact)inFact);
            result.setOutFact(current, (Fact)outFact);
        }

    }
}