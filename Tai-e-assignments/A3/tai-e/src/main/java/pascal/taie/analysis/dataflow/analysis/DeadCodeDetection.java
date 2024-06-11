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

import org.yaml.snakeyaml.nodes.Node;
import pascal.taie.Assignment;
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
import pascal.taie.ir.exp.*;
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


        Stmt entry = cfg.getEntry();
        LinkedList<Stmt> worklist = new LinkedList<>();
        worklist.add(entry);
        //首先循环遍历cfg，找出来其中的控制流不可达
        Set<Stmt> controlFlowReachable = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        TreeSet<Stmt> deadAssignment = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        while (!worklist.isEmpty()) {
            Stmt stmt = worklist.removeFirst();
            Set<Stmt> succsOf = cfg.getSuccsOf(stmt);
            controlFlowReachable.add(stmt);
            for (Stmt succ : succsOf) {
                //已经遍历过的控制流的点不再加入worklist，防止loop循环。
                if (!controlFlowReachable.contains(succ)) {
                    worklist.add(succ);
                }
            }
            //如果是if语句，则判断lh是不是常量，如果是常量则把它的出了常量分支之外的设置为分支不可达。
            if (stmt instanceof If ifStmt) {
                Value evaluate = ConstantPropagation.evaluate(ifStmt.getCondition(), constants.getInFact(ifStmt));
                //如果一个边是常量，先判断这个常量是0还是1，然后找到另一个对应的边，加入deadcode
                if (evaluate.isConstant()) {
                    int constant = evaluate.getConstant();
                    Set<Edge<Stmt>> outEdgesOf = cfg.getOutEdgesOf(ifStmt);
                    if (constant == 0) {
                        for (Edge<Stmt> edge : outEdgesOf) {
                            if (edge.getKind() == Edge.Kind.IF_TRUE) {
                                deadCode.add(edge.getTarget());

                            }
                        }
                    } else if (constant == 1) {
                        for (Edge<Stmt> edge : outEdgesOf) {
                            if (edge.getKind() == Edge.Kind.IF_FALSE) {
                                deadCode.add(edge.getTarget());

                            }
                        }
                    }
                }
            }
            else if (stmt instanceof SwitchStmt switchStmt) {
                //先拿到表达式，然后判断是否是常量，再做相应的判断
                Value switchCondition = ConstantPropagation.evaluate(switchStmt.getVar(), constants.getInFact(switchStmt));
                if (switchCondition.isConstant()) {
                    int condition = switchCondition.getConstant();
                    Set<Edge<Stmt>> outEdgesOf = cfg.getOutEdgesOf(switchStmt);
                    List<Pair<Integer, Stmt>> caseTargets = switchStmt.getCaseTargets();
                    for (Pair<Integer, Stmt> caseTarget : caseTargets) {
                        if (caseTarget.first() != condition) {
                            deadCode.add(caseTarget.second());
                        }
                    }
                    deadCode.add(switchStmt.getDefaultTarget());
                }
            }
            else if (stmt instanceof AssignStmt
                    && hasNoSideEffect(stmt.getUses().get(stmt.getUses().size()-1))
                    &&stmt.getDef().isPresent()
            ) {
                Var def = (Var)stmt.getDef().get();
                SetFact<Var> liverSet = liveVars.getResult(stmt);
                if(!liverSet.contains(def)){
                    deadAssignment.add(stmt);
                }
            }
            //上面只是设置了if内为分支不可达，需要遍历一遍，让它之后入度为1的点全部为deadcode
            //如果入度为1，并且之前的点在deadcode里面，则把这个点也加入deadcode
            if (!cfg.getPredsOf(stmt).isEmpty() && !cfg.isExit(stmt) &&
                    cfg.getInDegreeOf(stmt) == 1 &&
                    deadCode.contains(cfg.getPredsOf(stmt).toArray()[0])) {
                deadCode.add(stmt);
            }
            //如果是if语句，则判断lh是不是常量，如果是常量则把它的出了常量分支之外的设置为分支不可达。
        }
        for (Stmt stmt : cfg.getNodes()) {
            if (!controlFlowReachable.contains(stmt)) {
                deadCode.add(stmt);
            }
        }
        deadCode.addAll(deadAssignment);


// TODO - finish me
// Your task is to recognize dead code in ir and add it to deadCode
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
