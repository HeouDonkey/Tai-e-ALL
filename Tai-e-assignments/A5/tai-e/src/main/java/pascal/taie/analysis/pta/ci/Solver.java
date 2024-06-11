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
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

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
        if (!callGraph.contains(method)) {  // 当前调用图中该方法是否可达
            callGraph.addReachableMethod(method);  // 添加可达方法到调用图
            for (Stmt stmt : method.getIR().getStmts()) {  // 遍历方法中所有语句，调用accept
                stmt.accept(stmtProcessor);
            }
        }
    }


    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {  // 对于NEW语句，例如 x = new X()
            Obj obj = heapModel.getObj(stmt);  // 从模拟堆中获取当前语句的allocation site
            VarPtr varPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());  // 获取左值变量指针
            workList.addEntry(varPtr, new PointsToSet(obj));  // 添加(x,o)到worklist
            return null;
        }

        @Override
        public Void visit(Copy stmt) {  // 对于COPY语句，例如 x = y，左右值都是变量
            VarPtr lVar = pointerFlowGraph.getVarPtr(stmt.getLValue());  // 获取左值变量指针
            VarPtr rVar = pointerFlowGraph.getVarPtr(stmt.getRValue());  // 获取右值变量指针
            addPFGEdge(rVar, lVar);  // 添加边到pfg
            return null;
        }

        @Override
        public Void visit(LoadArray stmt) {  // 对于LOAD ARRAY语句，不处理
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreArray stmt) { // 对于STORY ARRAY语句，不处理
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(LoadField stmt) {  // 对于LOAD FIELD语句
            JField loadField = stmt.getFieldRef().resolve();  // 获取要被load的字段
            if (loadField.isStatic()) {  // 只处理STATIC LOAD FIELD语句
                VarPtr lVar = pointerFlowGraph.getVarPtr(stmt.getLValue()); // 获取左值变量指针
                StaticField rStaticField = pointerFlowGraph.getStaticField(loadField);  // 获取静态字段指针
                addPFGEdge(rStaticField, lVar);  // 添加边到pfg
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {  // 对于STORE FIELD语句
            JField loadField = stmt.getFieldRef().resolve();  // 获取要被store的字段
            if (loadField.isStatic()) {  // 只处理STATIC STORE FIELD语句
                VarPtr rVar = pointerFlowGraph.getVarPtr(stmt.getRValue());  // 获取右值变量指针
                StaticField staticField = pointerFlowGraph.getStaticField(loadField);  // 获取静态字段指针
                addPFGEdge(rVar, staticField);  // 添加边到pfg
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {  // 对于STATIC INVOKE语句
            if (stmt.isStatic()) {
                Var lVar = stmt.getLValue();  // 获取左值变量
                JMethod callee = resolveCallee(null, stmt);  // 获取调用的函数
                Edge<Invoke, JMethod> edge = new Edge(CallKind.STATIC, stmt, callee);  // 构造静态类型函数调用边
                if (callGraph.addEdge(edge)) {  // 如果调用图中没有该边
                    addReachable(callee);  // 添加该边到调用图
                    InvokeExp invokeExp = stmt.getInvokeExp();  // 获取调用函数表达式
                    for (int i = 0; i < invokeExp.getArgCount(); i++) {  // 按位置在实参和形参之间添加边到pfg
                        Var actual = invokeExp.getArg(i);
                        VarPtr actualPtr = pointerFlowGraph.getVarPtr(actual);
                        Var form = callee.getIR().getParam(i);
                        VarPtr formPtr = pointerFlowGraph.getVarPtr(form);
                        addPFGEdge(actualPtr, formPtr);
                    }
                    if (lVar != null) {  // 在所有返回值和接收参数之间添加边到pfg
                        for (Var returnVar : callee.getIR().getReturnVars()) {
                            VarPtr returnVarPtr = pointerFlowGraph.getVarPtr(returnVar);
                            VarPtr lVarPtr = pointerFlowGraph.getVarPtr(lVar);
                            addPFGEdge(returnVarPtr, lVarPtr);
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
        //if s->t not belong to PFG
        if(!pointerFlowGraph.getSuccsOf(source).contains(target)){
            //add s -> t to PFG
            pointerFlowGraph.addEdge(source, target);
            //if pts not empty, then add <t,pts> to worklist
            PointsToSet pointsToSet = source.getPointsToSet();
            if (!pointsToSet.isEmpty()){
                workList.addEntry(source,source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        if (callGraph.entryMethods().findAny().isPresent()) {
            addReachable(callGraph.entryMethods().findAny().get());
        }
        while (!workList.isEmpty()) {
            //remove <n,pts> from worklist
            //第一次到这里取出来的是一个a = new b
            WorkList.Entry n_pts = workList.pollEntry();
            //derta = pts - pt(n)
            // propagate(n,derta)
            Pointer n = n_pts.pointer();//取出来LHS
            PointsToSet pts = n_pts.pointsToSet();//pts
            PointsToSet derta = propagate(n, pts);//根据pfg做传播，并得到derta（）
            //if n represents a variable x
            if (n instanceof VarPtr varPtr) {
                //for each oi belong to derta do
                Var var = varPtr.getVar();
                derta.forEach(Oi -> {
                    //for each x.f = y(store) do AddEdge(y,oi.f)
                    var.getStoreFields().forEach(
                            storeField -> {
                                JField f = storeField.getFieldRef().resolve();
                                InstanceField oi_f = pointerFlowGraph.getInstanceField(Oi, f);
                                Var vy = storeField.getRValue();
                                Pointer y = pointerFlowGraph.getVarPtr(vy);
                                pointerFlowGraph.addEdge(y, oi_f);
                            });
                    //for each y = x.f do addEdge(oi.f,y)
                    var.getLoadFields().forEach(
                            loadField -> {
                                JField f = loadField.getFieldRef().resolve();
                                InstanceField oi_f = pointerFlowGraph.getInstanceField(Oi, f);
                                Var vy = loadField.getLValue();
                                Pointer y = pointerFlowGraph.getVarPtr(vy);
                                pointerFlowGraph.addEdge(oi_f, y);
                            }
                    );
                    //fpr each x[i] = y do  addEdge(y,Pointer points to all object in X[i])
                    var.getStoreArrays().forEach(
                            storeArray -> {
                                VarPtr y = pointerFlowGraph.getVarPtr(storeArray.getRValue());
                                VarPtr x_i = pointerFlowGraph.getVarPtr(storeArray.getLValue().getBase());
                                pointerFlowGraph.addEdge(y, x_i);
                            }
                    );
                    //for each y = x[i] do addEdge(x_i,y)
                    var.getLoadArrays().forEach(
                            loadArray -> {
                                VarPtr x_i = pointerFlowGraph.getVarPtr(loadArray.getRValue().getBase());
                                VarPtr y = pointerFlowGraph.getVarPtr(loadArray.getLValue());
                                pointerFlowGraph.addEdge(x_i,y);
                            }
                    );
                    //process call
                    processCall(var, Oi);
                });
            }
        }

    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        if (!pointsToSet.isEmpty()) {
            PointsToSet derta = new PointsToSet();
            //pt(n) = pt(n) union pts
            PointsToSet pt_n = pointer.getPointsToSet();
            pointsToSet.forEach( obj -> {
                if(!pt_n.contains(obj)) {
                    pt_n.addObject(obj);
                    derta.addObject(obj);
                }
            }
            );
            //foreach n->s  belong to PFG, do add <s,pts> to WL
            Set<Pointer> succsOfn = pointerFlowGraph.getSuccsOf(pointer);
            succsOfn.forEach(pfgNode->{
                workList.addEntry(pfgNode, pointsToSet);
            });

            //return derta
            return  derta;
        }
        return null;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     * 这里是抄的，没太懂
     */
    private void processCall(Var var, Obj recv) {
        //for each l:r = x.l(a1,...,an)   belong to S ,do
        List<Invoke> invokes = var.getInvokes();
        for (Invoke invoke : invokes) {
            JMethod callee = resolveCallee(recv,invoke);
            Var thisVar = callee.getIR().getThis();
            VarPtr thisVarPtr = pointerFlowGraph.getVarPtr(thisVar);
            workList.addEntry(thisVarPtr,new PointsToSet(recv));
            Edge edge = null;
            if (invoke.isInterface()){
                edge = new Edge(CallKind.INTERFACE,invoke,callee);
            } else if (invoke.isDynamic()) {
                edge = new Edge(CallKind.DYNAMIC,invoke,callee);
            } else if (invoke.isSpecial()) {
                edge = new Edge(CallKind.SPECIAL,invoke,callee);
            } else if (invoke.isVirtual()) {
                edge = new Edge(CallKind.VIRTUAL,invoke,callee);
            } else{
                edge = new Edge(CallKind.OTHER,invoke,callee);
            }
            if(callGraph.addEdge(edge)){
                addReachable(callee);
                InvokeExp invokeExp = invoke.getInvokeExp();
                for(int i = 0;i < invokeExp.getArgCount();i++){
                    Var arg = invokeExp.getArg(i);
                    VarPtr argPtr = pointerFlowGraph.getVarPtr(arg);
                    Var param = callee.getIR().getParam(i);
                    VarPtr paramPtr = pointerFlowGraph.getVarPtr(param);
                    addPFGEdge(argPtr,paramPtr);
                }
                Var lValue = invoke.getLValue();
                if(lValue!=null){
                    for(Var returnVar : callee.getIR().getReturnVars()){
                        VarPtr returnVarPtr = pointerFlowGraph.getVarPtr(returnVar);
                        VarPtr lValuePtr = pointerFlowGraph.getVarPtr(lValue);
                        addPFGEdge(returnVarPtr,lValuePtr);
                    }
                }

            }
        }
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
