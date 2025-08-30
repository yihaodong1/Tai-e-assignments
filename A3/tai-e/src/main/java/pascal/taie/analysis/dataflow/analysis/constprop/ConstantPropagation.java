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

import java.util.function.BiConsumer;

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
        CPFact fact = new CPFact();
        for(Var v: cfg.getIR().getParams()){
            if(canHoldInt(v))
                fact.update(v, Value.getNAC());
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        BiConsumer<Var, Value> action = (var, val) -> {
            Value val_target = target.get(var);
            target.update(var, meetValue(val_target, val));
        };
        fact.forEach(action);
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if(v1.isNAC()||v2.isNAC())
            return Value.getNAC();
        if(v1.isUndef())
            return v2;
        if(v2.isUndef())
            return v1;
        if(v1.isConstant() && v2.isConstant()){
            if(v1.getConstant() == v2.getConstant()){
                return Value.makeConstant(v1.getConstant());
            }else
                return Value.getNAC();
        }
//        throw new UnsupportedOperationException("meetValue: Not supported yet.");
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact copy = in.copy();   // 复制in给copy，避免影响in。
        if (stmt instanceof DefinitionStmt) { // 只处理赋值语句
            if (stmt.getDef().isPresent()) {  // 如果左值存在
                LValue lValue = stmt.getDef().get();  // 获取左值
                if ((lValue instanceof Var) && canHoldInt((Var) lValue)) {  // 对于符合条件的左值
                    copy.update((Var) lValue, evaluate(((DefinitionStmt<?, ?>)  stmt).getRValue(), copy));  // 计算右值表达式的值用来更新左值变量在格上的值
                }
            }
        }
        return out.copyFrom(copy);  // copy复制给out。copy和in相比，有更新，返回true；反之返回false
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
        if (exp instanceof Var) {   // 变量
            return in.get((Var) exp);
        } else if (exp instanceof IntLiteral) {  // 常量
            return Value.makeConstant(((IntLiteral) exp).getValue());
        } else if (exp instanceof BinaryExp) {   // 二元运算
            Value v1 = in.get(((BinaryExp) exp).getOperand1()); // 获取运算分量在格上的值
            Value v2 = in.get(((BinaryExp) exp).getOperand2());
            if (v1.isNAC() || v2.isNAC()) {      // 易错点1：NAC / 0 = Undef
                if (v1.isNAC() && v2.isConstant() && exp instanceof ArithmeticExp) {
                    ArithmeticExp.Op operator = ((ArithmeticExp) exp).getOperator();
                    if (operator == ArithmeticExp.Op.DIV || operator == ArithmeticExp.Op.REM) {
                        if (v2.getConstant() == 0) return Value.getUndef();
                    }
                }
                return Value.getNAC();
            }
            if (v1.isUndef() || v2.isUndef()) {
                return Value.getUndef();
            }
            if (exp instanceof ArithmeticExp) {
                ArithmeticExp.Op operator = ((ArithmeticExp) exp).getOperator();
                switch (operator) {
                    case ADD -> {
                        return Value.makeConstant(v1.getConstant() + v2.getConstant());
                    }
                    case DIV -> {
                        if (v2.getConstant() == 0) return Value.getUndef();
                        return Value.makeConstant(v1.getConstant() / v2.getConstant());
                    }
                    case MUL -> {
                        return Value.makeConstant(v1.getConstant() * v2.getConstant());
                    }
                    case SUB -> {
                        return Value.makeConstant(v1.getConstant() - v2.getConstant());
                    }
                    case REM -> {
                        if (v2.getConstant() == 0) return Value.getUndef();
                        return Value.makeConstant(v1.getConstant() % v2.getConstant());
                    }
                }
            } else if (exp instanceof ConditionExp) {
                ConditionExp.Op operator = ((ConditionExp) exp).getOperator();
                switch (operator) {
                    case EQ -> {
                        if (v1.getConstant() == v2.getConstant()) return Value.makeConstant(1);
                        else return Value.makeConstant(0);
                    }
                    case GE -> {
                        if (v1.getConstant() >= v2.getConstant()) return Value.makeConstant(1);
                        else return Value.makeConstant(0);
                    }
                    case GT -> {
                        if (v1.getConstant() > v2.getConstant()) return Value.makeConstant(1);
                        else return Value.makeConstant(0);
                    }
                    case LE -> {
                        if (v1.getConstant() <= v2.getConstant()) return Value.makeConstant(1);
                        else return Value.makeConstant(0);
                    }
                    case LT -> {
                        if (v1.getConstant() < v2.getConstant()) return Value.makeConstant(1);
                        else return Value.makeConstant(0);
                    }
                    case NE -> {
                        if (v1.getConstant() != v2.getConstant()) return Value.makeConstant(1);
                        else return Value.makeConstant(0);
                    }
                }
            } else if (exp instanceof BitwiseExp) {
                BitwiseExp.Op operator = ((BitwiseExp) exp).getOperator();
                switch (operator) {
                    case OR -> {
                        return Value.makeConstant(v1.getConstant() | v2.getConstant());
                    }
                    case AND -> {
                        return Value.makeConstant(v1.getConstant() & v2.getConstant());
                    }
                    case XOR -> {
                        return Value.makeConstant(v1.getConstant() ^ v2.getConstant());
                    }
                }
            } else if (exp instanceof ShiftExp) {
                ShiftExp.Op operator = ((ShiftExp) exp).getOperator();
                switch (operator) {
                    case SHL -> {
                        return Value.makeConstant(v1.getConstant() << v2.getConstant());
                    }
                    case SHR -> {
                        return Value.makeConstant(v1.getConstant() >> v2.getConstant());
                    }
                    case USHR -> {
                        return Value.makeConstant(v1.getConstant() >>> v2.getConstant());
                    }
                }
            }
            else {  // 易错点2：二元表达式中的其他类型表达式
                return Value.getNAC();
            }
        }
        return Value.getNAC();
    }
}
