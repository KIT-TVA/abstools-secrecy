/**
 * Copyright (c) 2009-2011, The HATS Consortium. All rights reserved. 
 * This file is licensed under the terms of the Modified BSD License.
 * Written by @Maximilian_Paul for questions please refer to uukln@student.kit.edu
 */
package org.abs_models.frontend.typechecker.ext;

import org.abs_models.frontend.ast.*;

public class SecrecyMethod {


    //TODO DOCUMENTATION AND SO ON

    /**
     * 
     */
    private ClassDecl parentClassOfMethod;

    private MethodImpl methodNode;

    private boolean isChecked = false;

    private boolean isSecure = false;

    SecrecyMethod (ClassDecl parentClassOfMethod, MethodImpl methodNode) {
        this.parentClassOfMethod = parentClassOfMethod;
        this.methodNode = methodNode;
    }

    public boolean getIsChecked() {
        return isChecked;
    }

    public void setIsChecked(boolean isChecked) {
        this.isChecked = isChecked;
    }

    public boolean getIsSecure() {
        return isSecure;
    }

    public void setIsSecure(boolean isSecure) {
        this.isSecure = isSecure;
    }
}