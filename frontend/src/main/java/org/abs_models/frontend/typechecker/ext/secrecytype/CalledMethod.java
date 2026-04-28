/**
 * Copyright (c) 2009-2011, The HATS Consortium. All rights reserved. 
 * This file is licensed under the terms of the Modified BSD License.
 * Written by @Maximilian_Paul for questions please refer to uukln@student.kit.edu
 */
package org.abs_models.frontend.typechecker.ext;

import org.abs_models.frontend.ast.*;
import java.util.Objects;

//What do I need to ensure a method calling another is ok ?
class CalledMethod {

    ClassDecl classContainingBoth; //class that contains the method that calls another as well as the other (filtered by the ThisExp)

    Call callToMethod; //the call from one method of a class to another

    MethodImpl methodImplOfCalledMethod;//the implementation of the method that we have called

    CalledMethod (ClassDecl classContainingBoth, Call callToMethod, MethodImpl methodImplOfCalledMethod) {
        this.classContainingBoth = classContainingBoth;
        this.callToMethod = callToMethod;
        this.methodImplOfCalledMethod = methodImplOfCalledMethod;
    }

    public ClassDecl getCallParentClass() {
        return classContainingBoth;
    }

    public MethodImpl getMethodImpl() {
        return methodImplOfCalledMethod;
    }

    public Call getMethodCall() {
        return callToMethod;
    }

    @Override
    public String toString() {
        return callToMethod + " to " + classContainingBoth.getName() + "." + methodImplOfCalledMethod.getMethodSig().getName();
    } 

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;
        CalledMethod other = (CalledMethod) obj;
        return this.classContainingBoth == other.classContainingBoth && this.callToMethod == other.callToMethod && this.methodImplOfCalledMethod == other.methodImplOfCalledMethod;
    }

    @Override
    public int hashCode() {
        return Objects.hash(classContainingBoth, callToMethod, methodImplOfCalledMethod);
    }

}