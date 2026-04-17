/**
 * Copyright (c) 2009-2011, The HATS Consortium. All rights reserved. 
 * This file is licensed under the terms of the Modified BSD License.
 * Written by @Maximilian_Paul for questions please refer to uukln@student.kit.edu
 */
package org.abs_models.frontend.typechecker.ext;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Iterator;
import java.util.Set;

import org.abs_models.frontend.analyser.ErrorMessage;
import org.abs_models.frontend.analyser.TypeError;
import org.abs_models.frontend.analyser.SemanticConditionList;

import org.abs_models.frontend.ast.*;

/**
 * This class is used to extract the secrecylevels for the different expressions and enforce rules with it.
 */
public class SecrecyExpVisitor {

    /**
     * Stores mappings between ASTNode's (declarations) and the assigned maximum secrecy values.
     * Meaning e.g. a variable may never hold a value higher than it's value from this _maxSecrecy.
     */
    private HashMap<ASTNode<?>,String> _maxSecrecy = new HashMap<>();

    //todo current secrecy is here 
    /**
     * Stores mappings between ASTNode's (declarations) and the assigned current secrecy values.
     * Meaning e.g. a variable may hold a vlaue smaller than it's max secrecy value which would allow certain actions. 
     */
    private HashMap<ASTNode<?>,String> _currentSecrecy = new HashMap<>();

    /**
     * Contains the secrecy lattice either given by the user or a default. (default is: Low < High)
     */
    private SecrecyLatticeStructure secrecyLatticeStructure;

    /**
     * Visitor for statements that performs typechecking for the secrecy rules.
     */
    private SecrecyStmtVisitor stmtVisitor;  

    /**
     * List holds entries for confidentiality levels if evaluated at a point in time it is the current secrecylevel. 
     */
    private LinkedList<ProgramCountNode> programConfidentiality;

     /**
     * The list for errors that we can add to if a rule isn't respected.
     */
    private final SemanticConditionList errors;

    /**
     * Constructor for the secrecy expression visitor that retrieves the secrecyvalues of different expressions.
     * @param _maxSecrecy - the hashmap that links ASTNode's to their assigned secrecylevel.
     * @param secrecyLatticeStructure - the datastructure that holds the information for the lattice.
     * @param programConfidentiality - the list for the confidentiality at a certain point in time.
     * @param stmtVisitor - the visitor that called this so that we can visit statements with it.
     */
    public SecrecyExpVisitor(HashMap<ASTNode<?>,String> _maxSecrecy, HashMap<ASTNode<?>,String> _currentSecrecy, SecrecyLatticeStructure secrecyLatticeStructure, SemanticConditionList errors, LinkedList<ProgramCountNode> programConfidentiality, SecrecyStmtVisitor stmtVisitor) {
        this._maxSecrecy = _maxSecrecy;
        this._currentSecrecy = _currentSecrecy;
        this.secrecyLatticeStructure = secrecyLatticeStructure;
        this.errors = errors;
        this.programConfidentiality = programConfidentiality;
        this.stmtVisitor = stmtVisitor;
    }

    /**
     * Visit function for expressions tries to return an attached secrecylevel.
     * Dependinding on the kind of expression the matching implementation of visit is called.
     * @param expression - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the expressions secrecylevel and the secrecylevel of the current program point.
     */
    public String visit(Exp expression) {

        if (expression instanceof Binary binaryExp) {
            return this.visit(binaryExp);
        } else if(expression instanceof Unary unaryExp){
            return this.visit(unaryExp);
        } else if (expression instanceof VarOrFieldUse varOrFieldUse) {
            return this.visit(varOrFieldUse);
        } else if (expression instanceof GetExp getExp) {
            return this.visit(getExp);
        } else if (expression instanceof AsyncCall asyncCall) {
            return this.visit(asyncCall);
        } else if (expression instanceof SyncCall syncCall) {
            return this.visit(syncCall);
        } else if (expression instanceof FnApp fnApp) {
            return this.visit(fnApp);
        }

        return secrecyLatticeStructure.evaluateListLevel(programConfidentiality);
    }


    public String visit(Binary binaryExp) {
        
        String leftLevel = binaryExp.getLeft().accept(this);
        String rightLevel = binaryExp.getRight().accept(this);
        String combined = secrecyLatticeStructure.join(leftLevel, rightLevel);

        return secrecyLatticeStructure.join(combined, secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
    }

    public String visit(Unary unaryExp) {

        ASTNode<?> child = unaryExp.getChild(0);
        String listLevel = secrecyLatticeStructure.evaluateListLevel(programConfidentiality);

        if(child instanceof Exp expr) {
            return secrecyLatticeStructure.join(expr.accept(this), listLevel);
        }

        return listLevel;
    }

    /**
     * Visit function for var or field use expressions.
     * 
     * @param varOrFieldUse - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the secrecylevel of the variable or field and the secrecylevel of the current program point.
     * if there is no secrecy attached to the variable or field then use the lowest value from the lattice structure (which is guaranteed to be >= minimum secrecy level of the lattice).
     */
    public String visit(VarOrFieldUse varOrFieldUse) {

        ASTNode<?> variable = varOrFieldUse.getDecl();
        String variableSecrecy = _currentSecrecy.get(variable);
        String listLevel = secrecyLatticeStructure.evaluateListLevel(programConfidentiality);

        if (variableSecrecy != null) {
            return secrecyLatticeStructure.join(variableSecrecy, secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
        }

        return listLevel;
    }

    /**
     * Visit function for get expressions.
     * When we have a get we remove the associated await change from the programConfidentiality list!
     * 
     * @param getExp - the expression for which we want to retrieve the secrecylevel.
     * @return - the lowest possible value from the lattice
     */
    public String visit(GetExp getExp) {

        ASTNode<?> target = (Exp) getExp.getChild(0);
        String targetString = target.toString();
        String varUseSecrecy = null;
        String listLevel = secrecyLatticeStructure.evaluateListLevel(programConfidentiality);

        if(target instanceof VarOrFieldUse varUse) {
            targetString = varUse.getName();
            varUseSecrecy = this.visit(varUse);
        }
        
        Iterator<ProgramCountNode> iter = programConfidentiality.iterator();
        while (iter.hasNext()) {
            ProgramCountNode node = iter.next();
            if (node.levelChangingNode.equals(targetString)) {
                iter.remove();
            }
        }

        stmtVisitor.updateProgramPoint(programConfidentiality);

        String minLevel = secrecyLatticeStructure.join(secrecyLatticeStructure.getMinSecrecyLevel(), varUseSecrecy);

        return secrecyLatticeStructure.join(minLevel, secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
    }

    //TODO simplify by making both methods async/sync call => call a checkCallSecrecy() helper function 
    //AS THEY PROBABLY WORK EXACTLY THE SAME!
    /*
    /**
     * Visit function for async call expressions.
     * 
     * @param asyncCall - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the secrecylevel of the returnvalue of the called method and the secrecylevel of the current program point.
     * //TODO missing /
    public String visit(AsyncCall asyncCall) {
        
        String secrecyLevel = null;
        
        if (!(asyncCall.getMethodSig() == null)) {
        

            MethodSig calledMethod = asyncCall.getMethodSig();

            List<ParamDecl> parameterList = calledMethod.getParamList();
            List<PureExp> calledParams = asyncCall.getParamList();
            int numberOfDefinedParameters = parameterList.getNumChild();

            if(numberOfDefinedParameters > 0) {

                for(int i = 0; i < parameterList.getNumChild(); i++) {

                    String definedSecrecy = _maxSecrecy.get(parameterList.getChild(i));
                    String calledSecrecy = this.visit(calledParams.getChild(i));
                    if(definedSecrecy == null) { 
                        definedSecrecy = secrecyLatticeStructure.getMinSecrecyLevel();
                    }

                    Set<String> calledSecrecySet = secrecyLatticeStructure.getSetForSecrecyLevel(calledSecrecy);

                    if(!(definedSecrecy.equals(calledSecrecy)||calledSecrecySet.contains(definedSecrecy))) {
                        errors.add(new TypeError(asyncCall, ErrorMessage.SECRECY_PARAMETER_TO_HIGH, calledSecrecy, definedSecrecy));
                    }
                }
            }

        //TODO think about the _maxSecrecy/_currentSecrecy level here and what it will/would/should say
        //secrecyLevel = _maxSecrecy.get(calledMethod);
        secrecyLevel = _currentSecrecy.get(calledMethod);
        String listLevel = secrecyLatticeStructure.evaluateListLevel(programConfidentiality);

        if(secrecyLevel != null) {
            return secrecyLatticeStructure.join(secrecyLevel, listLevel);
        }
        return listLevel;
    }

    /**
     * Visit function for sync call expressions.
     * 
     * @param syncCall - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the secrecylevel of the returnvalue of the called method and the secrecylevel of the current program point.
     * //TODO missing /
    public String visit(SyncCall syncCall) {

        String secrecyLevel = null;
        
        if (!(syncCall.getMethodSig() == null)) {

        MethodSig calledMethod = syncCall.getMethodSig();
        //TODO might require a catch/if to ensure there is a methodsig or not perform it otherwise
        
        List<ParamDecl> parameterList = calledMethod.getParamList();
        List<PureExp> calledParams = syncCall.getParamList();
        int numberOfDefinedParameters = parameterList.getNumChild();
        
        if(numberOfDefinedParameters > 0) {

            for(int i = 0; i < parameterList.getNumChild(); i++) {
                
                String definedSecrecy = _maxSecrecy.get(parameterList.getChild(i));
                String calledSecrecy = this.visit(calledParams.getChild(i));
                if(definedSecrecy == null) { 
                    definedSecrecy = secrecyLatticeStructure.getMinSecrecyLevel();
                }
                
                Set<String> calledSecrecySet = secrecyLatticeStructure.getSetForSecrecyLevel(calledSecrecy);
                
                if(!(definedSecrecy.equals(calledSecrecy)||calledSecrecySet.contains(definedSecrecy))) {
                    //TODO only add the error if we hadn't done that already? (Maybe due to how I check the methods)
                    errors.add(new TypeError(syncCall, ErrorMessage.SECRECY_PARAMETER_TO_HIGH, calledSecrecy, definedSecrecy));
                }
            }
        }

        //TODO think about the _maxSecrecy/_currentSecrecy level here and what it will/would/should say
        //secrecyLevel = _maxSecrecy.get(calledMethod);
        secrecyLevel = _currentSecrecy.get(calledMethod);
        String listLevel = secrecyLatticeStructure.evaluateListLevel(programConfidentiality);

        if(secrecyLevel != null) {
            return secrecyLatticeStructure.join(secrecyLevel, listLevel);
        }
        return listLevel;
    }

    /**
     * Visit function for call expressions.
     * 
     * @param functionCall - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the secrecylevel of the returnvalue of the called method and the secrecylevel of the current program point.
     */
    public String visit(Call functionCall) {
        
        String secrecyLevel = null;
        String listLevel = secrecyLatticeStructure.evaluateListLevel(programConfidentiality);
        
        if (!(functionCall.getMethodSig() == null)) {
        
            MethodSig calledMethod = functionCall.getMethodSig();

            List<ParamDecl> parameterList = calledMethod.getParamList();
            List<PureExp> calledParams = functionCall.getParamList();
            int numberOfDefinedParameters = parameterList.getNumChild();

            if(numberOfDefinedParameters > 0) {

                for(int i = 0; i < parameterList.getNumChild(); i++) {

                    String definedSecrecy = _maxSecrecy.get(parameterList.getChild(i));
                    String calledSecrecy = this.visit(calledParams.getChild(i));

                    if(definedSecrecy == null) { 
                        definedSecrecy = secrecyLatticeStructure.getMinSecrecyLevel();
                    }

                    Set<String> calledSecrecySet = secrecyLatticeStructure.getSetForSecrecyLevel(calledSecrecy);

                    if(!(definedSecrecy.equals(calledSecrecy) || calledSecrecySet.contains(definedSecrecy))) {
                        errors.add(new TypeError(functionCall, ErrorMessage.SECRECY_PARAMETER_TO_HIGH, calledSecrecy, parameterList.getChild(i).getName(), definedSecrecy));
                    }
                }
            }

            //TODO think about the _maxSecrecy/_currentSecrecy level here and what it will/would/should say
            //secrecyLevel = _maxSecrecy.get(calledMethod);
            secrecyLevel = _currentSecrecy.get(calledMethod);
            
            if (secrecyLevel != null) {
                return secrecyLatticeStructure.join(secrecyLevel, listLevel);
            }
        }

        return listLevel;
    }

    /**
     * Visit function fnApp expressions.
     * 
     * @param fnApp - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the secrecylevel of the variable or field and the secrecylevel of the current program point.
     * if there is no secrecy attached to the variable or field then use the lowest value from the lattice structure.
     */
    public String visit(FnApp fnApp) {

        List<PureExp> fnAppParameters = fnApp.getParamList();
        String secrecy = null;
        String listLevel = secrecyLatticeStructure.evaluateListLevel(programConfidentiality);

        for(PureExp fnAppParam : fnAppParameters) {

            String paramSecrecy = this.visit(fnAppParam);

            if (secrecy != null) {
                secrecy = secrecyLatticeStructure.join(secrecy, paramSecrecy);
            } else {
                secrecy = paramSecrecy;
            }
        }

        if (secrecy != null) {
            return secrecyLatticeStructure.join(secrecy, listLevel);
        }

        return listLevel;
    }

    /**
     * Allows to update the current program secrecy list on a change.
     * @param newConfidentiality - the list but with the new changes.
     */
    public void updateProgramPoint(LinkedList<ProgramCountNode> newConfidentiality) {
        programConfidentiality = newConfidentiality;
    }

    public void updateCurrentSecrecy(HashMap<ASTNode<?>, String> newCurrentSecrecy) {
        this._currentSecrecy = newCurrentSecrecy;
    }
}
