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
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.collection.Pair;

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
        // bfs
        Queue<Stmt> que = new java.util.LinkedList<>();
        deadCode.addAll(cfg.getNodes());// add all nodes to deadCode, then remove live nodes
        //visit set
        Set<Stmt> visited = new HashSet<>();
        que.add(cfg.getEntry());
        //visited.add(cfg.getEntry());
        while(!que.isEmpty()) {
            Stmt stmt = que.poll();
            visited.add(stmt);
            // 赋值语句,左侧为不活跃变量且右侧无副作用
            if(stmt instanceof AssignStmt<?,?> assignStmt) {
                if(assignStmt.getLValue() instanceof Var lvalue && !liveVars.getOutFact(stmt).contains((lvalue))) {
                    if(hasNoSideEffect(assignStmt.getRValue())) {
                        // stmt为无用赋值语句
                        //que.addAll(cfg.getSuccsOf(stmt));//bfs
                        for(Stmt s : cfg.getSuccsOf(stmt)) {
                            if(!visited.contains(s)) que.add(s);
                        }
                        continue;//不用删除这个stmt了
                    }
                }
            }
            //队列里的stmt一定是可达的
            deadCode.remove(stmt);
            // 不可达代码检测
            // 首先，在队列中的Stmt一定是控制流可达的
            if(stmt instanceof If stmtif) {
                Value condition = ConstantPropagation.evaluate(stmtif.getCondition(), constants.getInFact(stmt));
                if(condition.isConstant()) {
                    //如果条件是常量,只保留分支可达的分支进入队列，另一个分支一定是分支不可达的，为dead code
                    for(Edge<Stmt> e : cfg.getOutEdgesOf(stmt)) {
                        if((condition.getConstant() == 1 && e.getKind() == Edge.Kind.IF_TRUE) || (condition.getConstant() == 0 && e.getKind() == Edge.Kind.IF_FALSE)) {
                            //que.add(e.getTarget());
                            if(!visited.contains(e.getTarget())) que.add(e.getTarget());
                        }
                    }
                }
                //else que.addAll(cfg.getSuccsOf(stmt));//如果条件不是常量，那么两个分支都是可达的
                else{
                    for(Stmt s : cfg.getSuccsOf(stmt)) {
                        if(!visited.contains(s)) que.add(s);
                    }
                }
            }
            else if(stmt instanceof SwitchStmt switchStmt) {
                Value casevalue = ConstantPropagation.evaluate(switchStmt.getVar(), constants.getInFact(stmt));
                if(casevalue.isConstant()) {
                    // 如果case的值是常量，看哪个case的值与之对应，若有则该case的target可达，加入队列。若无，则default target可达，加入队列
                    boolean flag = false;
                    List<Pair<Integer, Stmt>> cases = switchStmt.getCaseTargets();
                    for (int i =0; i < cases.size(); i++) {
                        if(cases.get(i).first() == casevalue.getConstant()) {
                            //que.add(cases.get(i).second());
                            if(!visited.contains(cases.get(i).second())) que.add(cases.get(i).second());
                            flag = true;
                            break;
                        }
                    }
                    //if(!flag) que.add(switchStmt.getDefaultTarget());
                    if(!flag && !visited.contains(switchStmt.getDefaultTarget())) que.add(switchStmt.getDefaultTarget());
                }
                //else que.addAll(cfg.getSuccsOf(stmt));//如果case的值不是常量，那么所有case都是可达的
                else{
                    for(Stmt s : cfg.getSuccsOf(stmt)) {
                        if(!visited.contains(s)) que.add(s);
                    }
                }
            }
            //else que.addAll(cfg.getSuccsOf(stmt));//bfs
            else {
                for(Stmt s : cfg.getSuccsOf(stmt)) {
                    if(!visited.contains(s)) que.add(s);
                }
            }
        }
        deadCode.remove(cfg.getExit());
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
