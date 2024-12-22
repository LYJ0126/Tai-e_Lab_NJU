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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        //return null;
        CPFact temp = new CPFact();
        for (Var var: cfg.getIR().getParams()) {
            if(canHoldInt(var)) {
                temp.update(var, Value.getNAC());
            }
        }
        return temp;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        //return null;
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        //将fact中的变量值与target中的变量值进行meet操作
        for (Var var: fact.keySet()) {
            target.update(var, meetValue(fact.get(var), target.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        //return null;
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

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        //return false;
        //对应节点的transfer操作
        //保存outFact原值, 将inFact赋值给outFact
        //判断Node(Stmt)是否为DefinitionStmt
        //判断是否拥有合法左值, 包括def的类型Var和Var中的ValueType是否为Int, 如果不是, 本次实验中可以认为是nop空操作. 不需要为这个Stmt做任何分析, 直接将inFact copy给 outFact即可.
        //计算Stmt的右值(通过evaluate()获得), 并更新outFact中的相应Var def(笔者在此并未使用update方法的返回值, 或许可从此处入手优化效率, 但笔者不能保证其正确性)
        //比较outFact是否更新返回布尔值.
        CPFact oldOut = out.copy();
        out.copyFrom(in);
        if(stmt instanceof DefinitionStmt def_stmt) {
            LValue def = def_stmt.getLValue();
            if(def instanceof Var var && canHoldInt(var)) {
                Value value = evaluate(def_stmt.getRValue(), in);
                out.update(var, value);
            }
        }
        return !oldOut.equals(out);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        //return null;
        if(exp instanceof Var var) {
            return in.get(var);
        }
        if(exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }
        if(exp instanceof BinaryExp binaryExp) {
            Var var1 = binaryExp.getOperand1();
            Var var2 = binaryExp.getOperand2();
            Value left = in.get(var1);
            Value right = in.get(var2);
            if(canHoldInt(var1) && canHoldInt(var2)) {
                if(left.isConstant() && right.isConstant()) {
                    if(binaryExp instanceof ArithmeticExp arithmeticExp) {
                        Value result = Value.getUndef();
                        switch(arithmeticExp.getOperator()) {
                            case ADD:
                                result = Value.makeConstant(left.getConstant() + right.getConstant());
                                break;
                            case SUB:
                                result = Value.makeConstant(left.getConstant() - right.getConstant());
                                break;
                            case MUL:
                                result = Value.makeConstant(left.getConstant() * right.getConstant());
                                break;
                            case DIV:
                                if(right.getConstant() != 0) {
                                    result = Value.makeConstant(left.getConstant() / right.getConstant());
                                }
                                break;
                            case REM:
                                if(right.getConstant() != 0) {
                                    result = Value.makeConstant(left.getConstant() % right.getConstant());
                                }
                                break;
                        }
                        return result;
                    }
                    else if(binaryExp instanceof BitwiseExp bitwiseExp) {
                        Value result = Value.getNAC();
                        switch(bitwiseExp.getOperator()) {
                            case OR:
                                result = Value.makeConstant(left.getConstant() | right.getConstant());
                                break;
                            case AND:
                                result = Value.makeConstant(left.getConstant() & right.getConstant());
                                break;
                            case XOR:
                                result = Value.makeConstant(left.getConstant() ^ right.getConstant());
                                break;
                        }
                        return result;
                    }
                    else if (binaryExp instanceof ShiftExp shiftExp){
                        Value result = Value.getNAC();
                        switch(shiftExp.getOperator()){
                            case SHL:
                                result = Value.makeConstant(left.getConstant() << right.getConstant());
                                break;
                            case SHR:
                                result = Value.makeConstant(left.getConstant() >> right.getConstant());
                                break;
                            case USHR:
                                result = Value.makeConstant(left.getConstant() >>> right.getConstant());
                                break;
                        }
                        return result;
                    }
                    else if(binaryExp instanceof ConditionExp conditionExp){
                        Value result = Value.getNAC();
                        switch (conditionExp.getOperator()){
                            case EQ:
                                result = left.getConstant() == right.getConstant() ? Value.makeConstant(1) : Value.makeConstant(0);
                                break;
                            case NE:
                                result = left.getConstant() != right.getConstant() ? Value.makeConstant(1) : Value.makeConstant(0);
                                break;
                            case LT:
                                result = left.getConstant() < right.getConstant() ? Value.makeConstant(1) : Value.makeConstant(0);
                                break;
                            case GT:
                                result = left.getConstant() > right.getConstant() ? Value.makeConstant(1) : Value.makeConstant(0);
                                break;
                            case LE:
                                result = left.getConstant() <= right.getConstant() ? Value.makeConstant(1) : Value.makeConstant(0);
                                break;
                            case GE:
                                result = left.getConstant() >= right.getConstant() ? Value.makeConstant(1) : Value.makeConstant(0);
                                break;
                        }
                        return result;
                    }
                }
                else if(left.isNAC() || right.isNAC()) {
                    //return Value.getNAC();
                    //特殊情况,如果是/或%，除数为0，无论被除数是什么,都是Undefined
                    if(binaryExp instanceof ArithmeticExp arithmeticExp) {
                        if(arithmeticExp.getOperator() == ArithmeticExp.Op.DIV || arithmeticExp.getOperator() == ArithmeticExp.Op.REM) {
                            if(right.isConstant()){
                                if(right.getConstant() == 0) return Value.getUndef();
                            }
                        }
                    }
                    return Value.getNAC();
                }
                else return Value.getUndef();
            }
            return Value.getNAC();
        }
        return Value.getNAC();
    }
}
