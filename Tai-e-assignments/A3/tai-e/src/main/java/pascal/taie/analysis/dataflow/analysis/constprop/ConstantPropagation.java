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

import java.util.List;

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
        CPFact cpFact = new CPFact();
        List<Var> uses = cfg.getIR().getParams();
        for (Var use : uses) {
            cpFact.update(use, Value.getNAC());
        }
        return cpFact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var key : fact.keySet()) {
            if (canHoldInt(key)) target.update(key, meetValue(fact.get(key), target.get(key)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isConstant()) {
            if (v2.isConstant() && v2.getConstant() == v1.getConstant()) {
                return Value.makeConstant(v1.getConstant());
            } else if (v2.isUndef()) {
                return Value.makeConstant(v1.getConstant());
            } else if (v2.isConstant() && v2.getConstant() != v1.getConstant()) {
                return Value.getNAC();
            } else {
                return Value.getUndef();
            }
        } else if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else {
            return Value.getUndef();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {

        if(stmt instanceof DefinitionStmt<?,?>){
            //out[b] = genb uninon (in[b] - killb)
            CPFact tmp = new CPFact();
            if (stmt.getDef().isPresent()) {//这里我不太理解，已经做了definitionstmt的判断了，但是如果不判断present依然会报错
                //tmp = in[b] -killb
                LValue def = stmt.getDef().get();
                tmp.copyFrom(in);
                in.remove((Var) def);
                //tmp = genb union tmp
                Value gens = evaluate(stmt.getUses().get(stmt.getUses().size() - 1), in);
                tmp.update((Var) def, gens);
            }
            if (tmp.equals(out)) {
                return false;
            } else {
                out.copyFrom(tmp);
                return true;
            }
        }else {
            out.copyFrom(in);
            return false;
        }
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
        //如果lh是个常量，则直接返回
        if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        //如果lh是个变量，则去找in中lh的值，并根据值返回
        else if (exp instanceof Var) {
            if (in.get((Var) exp).isConstant()) {
                return Value.makeConstant(in.get((Var) exp).getConstant());
            } else if (in.get((Var) exp).isNAC()) {
                return Value.getNAC();
            } else {
                return Value.getUndef();
            }
        }
        //如果lh是二元表达式，则根据二院表达式种类分别处理
        else if (exp instanceof BinaryExp) {
            BinaryExp.Op operator = ((BinaryExp) exp).getOperator();
            Var operand1 = ((BinaryExp) exp).getOperand1();
            Var operand2 = ((BinaryExp) exp).getOperand2();
            if (in.get(operand1).isConstant() && in.get(operand2).isConstant()) {
                //如果这两个变量不能holdint，那就直接返回null
                if (exp instanceof ArithmeticExp) {//数学运算

                    switch ((ArithmeticExp.Op) operator) {
                        case ADD:
                            return Value.makeConstant(in.get(operand1).getConstant() + in.get(operand2).getConstant());
                        case SUB:
                            return Value.makeConstant(in.get(operand1).getConstant() - in.get(operand2).getConstant());
                        case MUL:
                            return Value.makeConstant(in.get(operand1).getConstant() * in.get(operand2).getConstant());
                        case DIV:
                            return (in.get(operand2).getConstant() == 0 ? Value.getNAC() : Value.makeConstant(in.get(operand1).getConstant() / in.get(operand2).getConstant()));
                        case REM:
                            return (in.get(operand2).getConstant() == 0 ? Value.getNAC() : Value.makeConstant(in.get(operand1).getConstant() % in.get(operand2).getConstant()));
                    }
                } else if (exp instanceof ConditionExp) {//条件表达式
                    switch ((ConditionExp.Op) operator) {
                        case EQ:
                            return in.get(operand1).getConstant() == in.get(operand2).getConstant() ? Value.makeConstant(1) : Value.makeConstant(0);
                        case NE:
                            return in.get(operand1).getConstant() != in.get(operand2).getConstant() ? Value.makeConstant(1) : Value.makeConstant(0);
                        case LT:
                            return in.get(operand1).getConstant() < in.get(operand2).getConstant() ? Value.makeConstant(1) : Value.makeConstant(0);
                        case GT:
                            return in.get(operand1).getConstant() > in.get(operand2).getConstant() ? Value.makeConstant(1) : Value.makeConstant(0);
                        case LE:
                            return in.get(operand1).getConstant() <= in.get(operand2).getConstant() ? Value.makeConstant(1) : Value.makeConstant(0);
                        case GE:
                            return in.get(operand1).getConstant() >= in.get(operand2).getConstant() ? Value.makeConstant(1) : Value.makeConstant(0);
                    }
                } else if (exp instanceof ShiftExp) {
                    switch ((ShiftExp.Op) operator) {
                        case SHL:
                            return Value.makeConstant(in.get(operand1).getConstant() << in.get(operand2).getConstant());
                        case SHR:
                            return Value.makeConstant(in.get(operand1).getConstant() >> in.get(operand2).getConstant());
                        case USHR:
                            return Value.makeConstant(in.get(operand1).getConstant() >>> in.get(operand2).getConstant());
                    }
                } else if (exp instanceof BitwiseExp) {
                    switch ((BitwiseExp.Op) operator) {
                        case AND:
                            return Value.makeConstant(in.get(operand1).getConstant() & in.get(operand2).getConstant());
                        case OR:
                            return Value.makeConstant(in.get(operand1).getConstant() | in.get(operand2).getConstant());
                        case XOR:
                            return Value.makeConstant(in.get(operand1).getConstant() ^ in.get(operand2).getConstant());
                    }
                }
            } else if (in.get(operand1).equals(Value.getNAC()) || in.get(operand2).equals(Value.getNAC())) {//有nuc
                return Value.getNAC();
            } else {
                return Value.getUndef();
            }
        }
        //如果是methodcall
        else {return Value.getNAC();}
        return null;

    }
}
