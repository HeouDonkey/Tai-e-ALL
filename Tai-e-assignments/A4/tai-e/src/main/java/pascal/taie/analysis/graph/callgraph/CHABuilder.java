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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.*;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        LinkedList<JMethod> WL = new LinkedList<>();

        WL.add(entry);
        while (!WL.isEmpty()) {
            JMethod jMethod = WL.removeFirst();
            if (callGraph.addReachableMethod(jMethod)) {
                //这里有一个坑，要是不用上面给的callgraph,那callsites里面没有东西
                Stream<Invoke> invokeStream = callGraph.callSitesIn(jMethod);
                List<Invoke> invokes = invokeStream.toList();
                for (Invoke invoke : invokes) {
                    Set<JMethod> T = resolve(invoke);
                    for (JMethod m : T) {
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, m));
                        WL.add(m);
                    }
                }
            }

        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        //taget Method
        Set<JMethod> T = new HashSet<>();
        //调用类型
        CallKind callKind = CallGraphs.getCallKind(callSite);
        //method描述
        MethodRef methodRef = callSite.getMethodRef();
        JClass declaringClass = methodRef.getDeclaringClass();

        //static call直接返回就行
        if (callKind == CallKind.STATIC) {
            JMethod declaredMethod = declaringClass.getDeclaredMethod(methodRef.getSubsignature());
            T.add(declaredMethod);
        }
        //special call主要调用构造器，私有方法和父类方法，需要dispatch
        else if (callKind == CallKind.SPECIAL) {
            JMethod method = dispatch(declaringClass, methodRef.getSubsignature());
            if (method != null)
                T.add(method);
        }
        //vitual需要对每一个子类方法去dispatch
        else if (callKind == CallKind.VIRTUAL || callKind == CallKind.INTERFACE) {
            LinkedList<JClass> subClasses = new LinkedList<>();
            subClasses.add(declaringClass);
            while (!subClasses.isEmpty()) {
                JClass jClass = subClasses.removeFirst();
                Collection<JClass> subclasses;
                //区分类和接口
                if(jClass.isInterface()){
                    subclasses = hierarchy.getDirectImplementorsOf(jClass);
                }else {
                    subclasses = hierarchy.getDirectSubclassesOf(jClass);
                }
                subClasses.addAll(subclasses);
                if (dispatch(jClass, methodRef.getSubsignature()) != null)
                    T.add(dispatch(jClass, methodRef.getSubsignature()));
            }
        }
        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        //如果这个类中包含改方法签名，则直接返回这个方法。如果没有，则递归调用父类
        if (jclass.getDeclaredMethod(subsignature) != null && !jclass.isAbstract()) {
            return jclass.getDeclaredMethod(subsignature);
        }
        //抽象方法下，如果是构造器的话，需要返回
        else if (jclass.isAbstract() && jclass.getDeclaredMethod(subsignature).isConstructor()) {
            return jclass.getDeclaredMethod(subsignature);
        }
        else {
            //如果jclass已经是顶层方法了，就直接返回null
            if (jclass.getSuperClass() != null)
                return dispatch(jclass.getSuperClass(), subsignature);
            else return null;
        }
    }
}
