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
     * Stores mappings between ASTNode's (declarations) and the assigned secrecy values.
     */
    private HashMap<ASTNode<?>,String> _secrecy = new HashMap<>();

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
     * @param _secrecy - the hashmap that links ASTNode's to their assigned secrecylevel.
     * @param secrecyLatticeStructure - the datastructure that holds the information for the lattice.
     * @param programConfidentiality - the list for the confidentiality at a certain point in time.
     * @param stmtVisitor - the visitor that called this so that we can visit statements with it.
     */
    public SecrecyExpVisitor(HashMap<ASTNode<?>,String> _secrecy, SecrecyLatticeStructure secrecyLatticeStructure, SemanticConditionList errors, LinkedList<ProgramCountNode> programConfidentiality, SecrecyStmtVisitor stmtVisitor) {
        this._secrecy = _secrecy;
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
    public String visit(Exp expression){

        
        if(expression instanceof AddAddExp addAddExp) {
            return this.visit(addAddExp);
        } else if (expression instanceof SubAddExp subAddExp) {
            return this.visit(subAddExp);
        } else if (expression instanceof VarOrFieldUse varOrFieldUse) {
            return this.visit(varOrFieldUse);
        } else if (expression instanceof MultMultExp multMultExp) {
            return this.visit(multMultExp);
        } else if (expression instanceof DivMultExp divMultExp) {
            return this.visit(divMultExp);
        } else if (expression instanceof ModMultExp modMultExp) {
            return this.visit(modMultExp);
        } else if (expression instanceof AndBoolExp andExp) {
            return this.visit(andExp);
        } else if (expression instanceof OrBoolExp orExp) {
            return this.visit(orExp);
        } else if (expression instanceof EqExp eqExp) {
            return this.visit(eqExp);
        } else if (expression instanceof NotEqExp noteqExp) {
            return this.visit(noteqExp);
        } else if (expression instanceof LTEQExp lessThanEqualsExp) {
            return this.visit(lessThanEqualsExp);
        } else if (expression instanceof GTEQExp greaterThanEqualsExp) {
            return this.visit(greaterThanEqualsExp);
        } else if (expression instanceof LTExp lessThanExp) {
            return this.visit(lessThanExp);
        } else if (expression instanceof GTExp greaterThanExp) {
            return this.visit(greaterThanExp);
        } else if (expression instanceof MinusExp minusExp) {
            return this.visit(minusExp);
        } else if (expression instanceof NegExp negExp) {
            return this.visit(negExp);
        } else if (expression instanceof VarOrFieldUse varOrFieldUse) {
            return this.visit(varOrFieldUse);
        } else if (expression instanceof GetExp getExp) {
            return this.visit(getExp);
        } else if (expression instanceof AsyncCall asyncCall) {
            return this.visit(asyncCall);
        } else if (expression instanceof SyncCall syncCall) {
            return this.visit(syncCall);
        }

        return secrecyLatticeStructure.join(secrecyLatticeStructure.getMinSecrecyLevel(), secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
    }

    /**
     * Visit function for additive expressions.
     * Set combine as the join of the left and right values.
     * 
     * @param addAddExp - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the combine and the secrecylevel of the current program point.
     */
    public String visit(AddAddExp addAddExp) {
        
        String leftLevel = addAddExp.getLeft().accept(this);
        String rightLevel = addAddExp.getRight().accept(this);
        String combined = secrecyLatticeStructure.join(leftLevel, rightLevel);

        return secrecyLatticeStructure.join(combined, secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
    }

    /**
     * Visit function for subtractive expressions.
     * Set combine as the join of the left and right values.
     * 
     * @param subAddExp - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the combine and the secrecylevel of the current program point.
     */
    public String visit(SubAddExp subAddExp) {
        
        String leftLevel = subAddExp.getLeft().accept(this);
        String rightLevel = subAddExp.getRight().accept(this);
        String combined = secrecyLatticeStructure.join(leftLevel, rightLevel);

        return secrecyLatticeStructure.join(combined, secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
    }

    /**
     * Visit function for multiplicative expressions.
     * Set combine as the join of the left and right values.
     * 
     * @param multMultExp - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the combine and the secrecylevel of the current program point.
     */
    public String visit(MultMultExp multMultExp) {
        
        String leftLevel = multMultExp.getLeft().accept(this);
        String rightLevel = multMultExp.getRight().accept(this);
        String combined = secrecyLatticeStructure.join(leftLevel, rightLevel);

        return secrecyLatticeStructure.join(combined, secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
    }

    /**
     * Visit function for divisive expressions.
     * Set combine as the join of the left and right values.
     * 
     * @param divMultExp - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the combine and the secrecylevel of the current program point.
     */
    public String visit(DivMultExp divMultExp) {
        
        String leftLevel = divMultExp.getLeft().accept(this);
        String rightLevel = divMultExp.getRight().accept(this);
        String combined = secrecyLatticeStructure.join(leftLevel, rightLevel);

        return secrecyLatticeStructure.join(combined, secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
    }

    /**
     * Visit function for modulative expressions.
     * Set combine as the join of the left and right values.
     * 
     * @param modMultExp - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the combine and the secrecylevel of the current program point.
     */
    public String visit(ModMultExp modMultExp) {
        
        String leftLevel = modMultExp.getLeft().accept(this);
        String rightLevel = modMultExp.getRight().accept(this);
        String combined = secrecyLatticeStructure.join(leftLevel, rightLevel);

        return secrecyLatticeStructure.join(combined, secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
    }

    /**
     * Visit function for and expressions.
     * Set combine as the join of the left and right values.
     * 
     * @param andExp - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the combine and the secrecylevel of the current program point.
     */
    public String visit(AndBoolExp andExp) {
        
        String leftLevel = andExp.getLeft().accept(this);
        String rightLevel = andExp.getRight().accept(this);
        String combined = secrecyLatticeStructure.join(leftLevel, rightLevel);

        return secrecyLatticeStructure.join(combined, secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
    }

    /**
     * Visit function for or expressions.
     * Set combine as the join of the left and right values.
     * 
     * @param orExp - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the combine and the secrecylevel of the current program point.
     */    
    public String visit(OrBoolExp orExp) {
        
        String leftLevel = orExp.getLeft().accept(this);
        String rightLevel = orExp.getRight().accept(this);
        String combined = secrecyLatticeStructure.join(leftLevel, rightLevel);

        return secrecyLatticeStructure.join(combined, secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
    }

    /**
     * Visit function for equality expressions.
     * Set combine as the join of the left and right values.
     * 
     * @param eqExp - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the combine and the secrecylevel of the current program point.
     */
    public String visit(EqExp eqExp) {
        
        String leftLevel = eqExp.getLeft().accept(this);
        String rightLevel = eqExp.getRight().accept(this);
        String combined = secrecyLatticeStructure.join(leftLevel, rightLevel);

        return secrecyLatticeStructure.join(combined, secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
    }

    /**
     * Visit function for inequality expressions.
     * Set combine as the join of the left and right values.
     * 
     * @param notEqExp - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the combine and the secrecylevel of the current program point.
     */
    public String visit(NotEqExp notEqExp) {
        
        String leftLevel = notEqExp.getLeft().accept(this);
        String rightLevel = notEqExp.getRight().accept(this);
        String combined = secrecyLatticeStructure.join(leftLevel, rightLevel);

        return secrecyLatticeStructure.join(combined, secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
    }

    /**
     * Visit function for less than equals expressions.
     * Set combine as the join of the left and right values.
     * 
     * @param lessThanEqualsExp - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the combine and the secrecylevel of the current program point.
     */
    public String visit(LTEQExp lessThanEqualsExp) {

        String leftLevel = lessThanEqualsExp.getLeft().accept(this);
        String rightLevel = lessThanEqualsExp.getRight().accept(this);
        String combined = secrecyLatticeStructure.join(leftLevel, rightLevel);

        return secrecyLatticeStructure.join(combined, secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
    }

    /**
     * Visit function for greater than equals expressions.
     * Set combine as the join of the left and right values.
     * 
     * @param greaterThanEqualsExp - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the combine and the secrecylevel of the current program point.
     */
    public String visit(GTEQExp greaterThanEqualsExp) {

        String leftLevel = greaterThanEqualsExp.getLeft().accept(this);
        String rightLevel = greaterThanEqualsExp.getRight().accept(this);
        String combined = secrecyLatticeStructure.join(leftLevel, rightLevel);

        return secrecyLatticeStructure.join(combined, secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
    }
   
    /**
     * Visit function for less than expressions.
     * Set combine as the join of the left and right values.
     * 
     * @param lessThanExp - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the combine and the secrecylevel of the current program point.
     */
    public String visit(LTExp lessThanExp) {

        String leftLevel = lessThanExp.getLeft().accept(this);
        String rightLevel = lessThanExp.getRight().accept(this);
        String combined = secrecyLatticeStructure.join(leftLevel, rightLevel);

        return secrecyLatticeStructure.join(combined, secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
    }

    /**
     * Visit function for greater than expressions.
     * Set combine as the join of the left and right values.
     * 
     * @param greaterThanExp - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the combine and the secrecylevel of the current program point.
     */
    public String visit(GTExp greaterThanExp) {

        String leftLevel = greaterThanExp.getLeft().accept(this);
        String rightLevel = greaterThanExp.getRight().accept(this);
        String combined = secrecyLatticeStructure.join(leftLevel, rightLevel);

        return secrecyLatticeStructure.join(combined, secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
    }

    /**
     * Visit function for minus expressions.
     * 
     * @param minusExp - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the secrecylevel of the exp below and the secrecylevel of the current program point.
     */
    public String visit(MinusExp minusExp) {
        
        ASTNode<?> child = minusExp.getChild(0);

        if(child instanceof Exp expr) {
            return secrecyLatticeStructure.join(expr.accept(this), secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
        }

        return null;
    }

    /** 
     * Visit function for negate expressions.
     * 
     * @param negExp - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the secrecylevel of the exp below and the secrecylevel of the current program point.
     */
    public String visit(NegExp negExp) {
        
        ASTNode<?> child = negExp.getChild(0);

        if(child instanceof Exp expr) {
            return secrecyLatticeStructure.join(expr.accept(this), secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
        }

        return null;
    }

    /**
     * Visit function for var or field use expressions.
     * 
     * @param varOrFieldUse - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the secrecylevel of the variable or field and the secrecylevel of the current program point.
     * if there is no secrecy attached to the variable or field then use the lowest value from the lattice structure.
     */
    public String visit(VarOrFieldUse varOrFieldUse) {

        //Todo here is the varOrFieldUse and this is where I need to check for the SumExample's issue
        //[Secrecy: High] List<Int> values = nil;
        //while (i < length(values)) {...}
        //System.out.println(varOrFieldUse);

        ASTNode<?> variable = varOrFieldUse.getDecl();
        String secrecy = _secrecy.get(variable);

        if (secrecy != null) {
            return secrecyLatticeStructure.join(secrecy, secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
            //If there was a secrecy found then return it combined with the current pc otherwise combine pc with lowest possible.
        }

        return secrecyLatticeStructure.join(secrecyLatticeStructure.getMinSecrecyLevel(), secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
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

        if(target instanceof VarOrFieldUse varUse)targetString = varUse.getName();
        
        Iterator<ProgramCountNode> iter = programConfidentiality.iterator();
        while (iter.hasNext()) {
            ProgramCountNode node = iter.next();
            if (node.levelChangingNode.equals(targetString)) {
                iter.remove();
            }
        }

        stmtVisitor.updateProgramPoint(programConfidentiality);
        return secrecyLatticeStructure.join(secrecyLatticeStructure.getMinSecrecyLevel(), secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
    }

    /**
     * Visit function for async call expressions.
     * 
     * @param asyncCall - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the secrecylevel of the returnvalue of the called method and the secrecylevel of the current program point.
     */
    public String visit(AsyncCall asyncCall) {
        MethodSig calledMethod = asyncCall.getMethodSig();
        //TODO REMOVE ALL BELOW HERE AND

        List<ParamDecl> parameterList = calledMethod.getParamList();
        List<PureExp> calledParams = asyncCall.getParamList();
        int numberOfDefinedParameters = parameterList.getNumChild();
        
        if(numberOfDefinedParameters > 0) {

            //System.out.println(calledMethod.getName() + " with the call: " + asyncCall + "\n"); //TODO REMOVE THIS LATER
            //System.out.println(parameterList + "\n" + calledParams);

            for(int i = 0; i < parameterList.getNumChild(); i++) {
                
                String definedSecrecy = _secrecy.get(parameterList.getChild(i));
                String calledSecrecy = this.visit(calledParams.getChild(i));
                if(definedSecrecy == null) { 
                    definedSecrecy = secrecyLatticeStructure.getMinSecrecyLevel();
                }
                
                //System.out.println("Child " + i + " is defined " + parameterList.getChild(i) + " and called " + calledParams.getChild(i));
                //System.out.println("defined is: " + definedSecrecy + ", called is: " + calledSecrecy);
                
                Set<String> calledSecrecySet = secrecyLatticeStructure.getSetForSecrecyLevel(calledSecrecy);
                
                if(!(definedSecrecy.equals(calledSecrecy)||calledSecrecySet.contains(definedSecrecy))) {
                    errors.add(new TypeError(asyncCall, ErrorMessage.SECRECY_PARAMETER_TO_HIGH, calledSecrecy, definedSecrecy));
                }
            }
        }

        //ABOVE HERE THAT ISN'T FUNCTIONAL
        String secrecyLevel = _secrecy.get(calledMethod);
        if(secrecyLevel == null) secrecyLevel = secrecyLatticeStructure.getMinSecrecyLevel();
        return secrecyLatticeStructure.join(secrecyLevel, secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
    }

    /**
     * Visit function for sync call expressions.
     * 
     * @param syncCall - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the secrecylevel of the returnvalue of the called method and the secrecylevel of the current program point.
     */
    public String visit(SyncCall syncCall) {
        MethodSig calledMethod = syncCall.getMethodSig();
        //TODO REMOVE ALL BELOW HERE AND
        //stmtVisitor.visit()

        List<ParamDecl> parameterList = calledMethod.getParamList();
        List<PureExp> calledParams = syncCall.getParamList();
        int numberOfDefinedParameters = parameterList.getNumChild();
        
        if(numberOfDefinedParameters > 0) {

            //System.out.println(calledMethod.getName() + " with the call: " + syncCall + "\n"); //TODO REMOVE THIS LATER
            //System.out.println(parameterList + "\n" + calledParams);

            for(int i = 0; i < parameterList.getNumChild(); i++) {
                
                String definedSecrecy = _secrecy.get(parameterList.getChild(i));
                String calledSecrecy = this.visit(calledParams.getChild(i));
                if(definedSecrecy == null) { 
                    definedSecrecy = secrecyLatticeStructure.getMinSecrecyLevel();
                }
                
                //System.out.println("Child " + i + " is defined " + parameterList.getChild(i) + " and called " + calledParams.getChild(i));
                //System.out.println("defined is: " + definedSecrecy + ", called is: " + calledSecrecy);
                
                Set<String> calledSecrecySet = secrecyLatticeStructure.getSetForSecrecyLevel(calledSecrecy);
                
                if(!(definedSecrecy.equals(calledSecrecy)||calledSecrecySet.contains(definedSecrecy))) {
                    errors.add(new TypeError(syncCall, ErrorMessage.SECRECY_PARAMETER_TO_HIGH, calledSecrecy, definedSecrecy));
                }
            }
            
            //TODO 1: Fix the probably existing error(s) with local variables
                //1.1: Does it work over the local variables declaration - I Believe so
                //1.2: Do we improve runtime by removing it before we exit a method we checked / or not store it at all in the same list and keep a temp list - no we don't yet
                //1.3: Does the retrival work for local variables - seems like it
        }

        //ABOVE HERE THAT ISN'T FUNCTIONAL
        String secrecyLevel = _secrecy.get(calledMethod);
        if(secrecyLevel == null) secrecyLevel = secrecyLatticeStructure.getMinSecrecyLevel();
        return secrecyLatticeStructure.join(secrecyLevel, secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
    }

    /**
     * Visit function fnApp expressions.
     * 
     * @param fnApp - the expression for which we want to retrieve the secrecylevel.
     * @return - the join of the secrecylevel of the variable or field and the secrecylevel of the current program point.
     * if there is no secrecy attached to the variable or field then use the lowest value from the lattice structure.
     */
    public String visit(FnApp fnApp) {

        //System.out.println(fnApp);

        List<PureExp> fnAppParameters = fnApp.getParamList();

        //System.out.println(fnAppParameters);

        String secrecy = null;

        for(PureExp fnAppParam : fnAppParameters) {
            String paramSecrecy = this.visit(fnAppParam);
            //System.out.println(fnAppParam + " with secrecy: " + paramSecrecy);

            if (secrecy != null) {
                secrecy = secrecyLatticeStructure.join(secrecy, paramSecrecy);
            } else {
                secrecy = paramSecrecy;
            }
        }

        //FnApp is defined as: FnApp : PureExp ::= <Name> Param:PureExp* ;
        //so retrieve the value of the pureExp below! (or if multiple of all of the ones below)
        //then combine them to one value and with the pc level and return that
        //or otherwise return min level combined with pc directly

        //ASTNode<?> variable = varOrFieldUse.getDecl();
        //String secrecy = _secrecy.get(variable);
        //
        if (secrecy != null) {
            return secrecyLatticeStructure.join(secrecy, secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
        }
        //
        //return secrecyLatticeStructure.join(secrecyLatticeStructure.getMinSecrecyLevel(), secrecyLatticeStructure.evaluateListLevel(programConfidentiality));
        return secrecyLatticeStructure.getMinSecrecyLevel();
    }

    /**
     * Allows to update the current program secrecy list on a change.
     * @param newConfidentiality - the list but with the new changes.
     */
    public void updateProgramPoint(LinkedList<ProgramCountNode> newConfidentiality) {
        programConfidentiality = newConfidentiality;
    }
}
