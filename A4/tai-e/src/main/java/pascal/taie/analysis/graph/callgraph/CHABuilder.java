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
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;


import java.util.*;

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
        Queue<JMethod> worklist = new LinkedList<>();
        worklist.add(entry);
        Set<JMethod> rm = new HashSet<>();
        while(!worklist.isEmpty()){
            JMethod method = worklist.poll();
            if(!rm.contains(method)){
                rm.add(method);
                callGraph.addReachableMethod(method);
                //获取method的所有call sites
                Set<Invoke> allCallSites = callGraph.getCallSitesIn(method);
                for(Invoke callSite: allCallSites){
                    CallKind kind = null;
                    if(callSite.isStatic()) kind = CallKind.STATIC;
                    else if(callSite.isSpecial()) kind = CallKind.SPECIAL;
                    else if(callSite.isInterface()) kind = CallKind.INTERFACE;
                    else if(callSite.isVirtual()) kind = CallKind.VIRTUAL;
                    if(kind != null){
                        Set<JMethod> T = resolve(callSite);
                        for(JMethod target: T) {
                            callGraph.addEdge(new Edge<>(kind, callSite, target));
                            worklist.add(target);
                        }
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
        //return null;
        MethodRef methodRef = callSite.getMethodRef();
        Set<JMethod>res = new HashSet<>();
        if(callSite.isStatic()){//若callSite是static call,直接查找methodRef对应的方法
            res.add(methodRef.getDeclaringClass().getDeclaredMethod(methodRef.getSubsignature()));
        }
        else if(callSite.isSpecial()){
            //若callSite是special call,dispatch(c^m,m).
            //m is the method signature at callsite. c^m is the class type of m
            JClass callsite_class = methodRef.getDeclaringClass();
            JMethod method = dispatch(callsite_class, methodRef.getSubsignature());
            if (method != null) {//注意这里要判断method是否为null
                res.add(method);
            }
        }
        else{//Virtual Call. 包括InvokeVirtual和InvokeInterface
            JClass callsite_class = methodRef.getDeclaringClass();
            Queue<JClass> queue = new LinkedList<>();
            //遍历callsite_class及其的所有子类
            queue.add(callsite_class);
            while(!queue.isEmpty()) {
                JClass current = queue.poll();
                JMethod method = dispatch(current, methodRef.getSubsignature());
                if (method != null) {
                    res.add(method);
                }
                if(current.isInterface()){
                    queue.addAll(hierarchy.getDirectImplementorsOf(current));
                    queue.addAll(hierarchy.getDirectSubinterfacesOf(current));
                }
                else queue.addAll(hierarchy.getDirectSubclassesOf(current));
            }
        }
        return res;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        //return null;
        JMethod method = jclass.getDeclaredMethod(subsignature);
        if(method != null && !method.isAbstract()) {
            return method;
        }
        else if(jclass.getSuperClass() == null) {
            return null;
        }
        else {
            return dispatch(jclass.getSuperClass(), subsignature);
        }
    }
}
