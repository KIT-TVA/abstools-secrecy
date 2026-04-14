/**
 * Copyright (c) 2009-2011, The HATS Consortium. All rights reserved. 
 * This file is licensed under the terms of the Modified BSD License.
 * Written by @Maximilian_Paul for questions please refer to uukln@student.kit.edu
 */
package org.abs_models.frontend.typechecker.ext;

import java.util.HashMap;
import java.util.Set;
import java.util.LinkedList;

import org.abs_models.frontend.ast.*;
import org.abs_models.frontend.analyser.ErrorMessage;
import org.abs_models.frontend.analyser.TypeError;
import org.abs_models.frontend.analyser.SemanticConditionList;


/**
 * This class is used to extract the secrecylevels for the different statements and enforce rules with it.
 */
public class SecrecyStmtVisitor {

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
     * Visitor for expressions that performs typechecking for the secrecy rules.
     */
    private SecrecyExpVisitor ExpVisitor;               

    /**
     * List holds entries for confidentiality levels if evaluated at a point in time it is the current secrecylevel. 
     */
    private LinkedList<ProgramCountNode> programConfidentiality;

    /**
     * The list for errors that we can add to if a rule isn't respected.
     */
    private final SemanticConditionList errors;

    /**
     * Constructor for the SecrecyStmtVisitor.
     * @param _maxSecrecy - the hashmap that links ASTNode's to their assigned secrecylevel.
     * @param secrecyLatticeStructure - the datastructure that holds the information for the lattice. 
     * @param errors - the error list that we can add typeerrors to.
     * @param programConfidentiality - the list for the confidentiality at a certain point in time.
     */
    public SecrecyStmtVisitor(HashMap<ASTNode<?>,String> _maxSecrecy, HashMap<ASTNode<?>,String> _currentSecrecy, SecrecyLatticeStructure secrecyLatticeStructure, SemanticConditionList errors,LinkedList<ProgramCountNode> programConfidentiality) {
        this._maxSecrecy = _maxSecrecy;
        this._currentSecrecy = _currentSecrecy;
        this.secrecyLatticeStructure = secrecyLatticeStructure;
        this.errors = errors;
        this.programConfidentiality = programConfidentiality;

        ExpVisitor = new SecrecyExpVisitor(_maxSecrecy, _currentSecrecy, secrecyLatticeStructure, errors, programConfidentiality, this);
    }

    /**
     * Visit function for statements.
     * Depending on the kind of statement we call the matching implementation of visit. 
     * @param stmt - the stmt we want to visit and check.
     */
    public void visit(Stmt stmt) {

        if(stmt instanceof Block blockStmt) {
            this.visit(blockStmt);
        } else if (stmt instanceof AssignStmt assignStmt) {
            this.visit(assignStmt);
        } else if (stmt instanceof ReturnStmt returnStmt) {
            this.visit(returnStmt);
        } else if (stmt instanceof IfStmt ifStmt) {
            this.visit(ifStmt);
        } else if (stmt instanceof WhileStmt whileStmt) {
            this.visit(whileStmt);
        } else if (stmt instanceof ExpressionStmt expressionStmt) {
            this.visit(expressionStmt);
        } else if (stmt instanceof VarDeclStmt varDeclStmt) {
            this.visit(varDeclStmt);
        } else if (stmt instanceof AwaitStmt awaitStmt) {
            this.visit(awaitStmt);
        }

        return;
    }

    /**
     * Visit function for block statements. We check every statement in the block with this visitor.
     * @param blockStmt - the blockstmt from which we want to visit each stmt.
     */
    public void visit(Block blockStmt){
        for(Stmt stmt : blockStmt.getStmtList()) {
            stmt.accept(this);
        }
    }

    /**
     * Visit function for assign statements. 
     * We check that for a:High and b:Low we never assign b = a however a = b, b = b or a = a is fine.
     * Secrecylevel of LHS has to be higher or equal to RHS. (default: Low)
     * @param assignStmt - the assign stmt that has to respect the assignment rule.
     */
    public void visit(AssignStmt assignStmt){

        ASTNode<?> LHS = assignStmt.getVar().getDecl();
        Exp RhsExp = assignStmt.getValue();

        if(RhsExp instanceof Call calling) {
            System.out.println("Call: " + calling);
            //TODO get the name of the class and the name of the method
            //Then get the method implementation
            //Then perform a recursive check on the method implementation 
            //if there is no error added return nothing
            //If the called method is insecure => add an insecure error to the method containing the call
            //Careful the call may NOT ONLY BE WRITTEN HERE => BUT ALSO IN AN EXPRSTMT
        }

        String minSecLevel = secrecyLatticeStructure.getMinSecrecyLevel();
        String LHSsecLevel = minSecLevel;
        String RHSsecLevel = minSecLevel;

        String possibleLHSLevel = _maxSecrecy.get(LHS);
        String possibleRhsLevel = RhsExp.accept(ExpVisitor);

        if(possibleLHSLevel != null)LHSsecLevel = possibleLHSLevel;
        if(possibleRhsLevel != null)RHSsecLevel = possibleRhsLevel;
        
        Set<String> LHScontainedIn = secrecyLatticeStructure.getSetForSecrecyLevel(LHSsecLevel);
        
        if(LHScontainedIn.contains(RHSsecLevel)) {
            errors.add(new TypeError(assignStmt, ErrorMessage.SECRECY_LEAKAGE_ERROR_FROM_TO, RHSsecLevel, assignStmt.getValue().toString(), LHSsecLevel, assignStmt.getVar().getName()));
            return;
        }

        //Update the current secrecy level if it has a max level != to the min secrecy level
        if (!LHSsecLevel.equals(minSecLevel)) {
            _currentSecrecy.put(LHS, RHSsecLevel);
        }
    }

    /**
     * Visit function for return statements. 
     * We check that for methoda:High and b:Low we never return b.
     * Secrecylevel of return has to be lower or equal the return secrecylevel of the method. (default: Low)
     * @param returnStmt - the return stmt that has to respect the returnstmt rule.
     */
    public void visit(ReturnStmt returnStmt){
        
        ASTNode<?> returnExp = returnStmt.getChild(1);
        ASTNode<?> parentNode = returnStmt.getParent();

        String returnDefinitionLevel = secrecyLatticeStructure.getMinSecrecyLevel();
        String returnActualLevel = secrecyLatticeStructure.getMinSecrecyLevel();

        while(!(parentNode instanceof MethodImpl)) {
            parentNode = parentNode.getParent();
        }

        if((parentNode instanceof MethodImpl methodImpl)) {

            MethodSig methodSig = methodImpl.getMethodSig();
            String possibleMethodSigSecrecy = _maxSecrecy.get(methodSig);

            if(possibleMethodSigSecrecy != null)returnDefinitionLevel = possibleMethodSigSecrecy;
        }

        if(returnExp instanceof Exp exp) {

            if(exp.accept(ExpVisitor) != null)returnActualLevel = exp.accept(ExpVisitor);

        }

        Set<String> methodReturnSet = secrecyLatticeStructure.getSetForSecrecyLevel(returnActualLevel);

        if(!(methodReturnSet.contains(returnDefinitionLevel)) && !(returnActualLevel.equals(returnDefinitionLevel))) {
            errors.add(new TypeError(returnStmt, ErrorMessage.SECRECY_LEAKAGE_ERROR_FROM_TO, returnActualLevel, "returnStmt", returnDefinitionLevel, "returnDefinition"));
        }
    }

    /**
     * Visit function for if-statements. 
     * When we check the then (or else) block we might have a higher program point context.
     * The program point is defined by the one we had joined with the secrecylevel of the condition. (default: Low)
     * For this we add the secrecylevel of the condition to the programConfidentiality list and remove it once checked. 
     * @param ifStmt - the if-stmt that has to respect the if-rule.
     */
    public void visit(IfStmt ifStmt){

        Exp condition = ifStmt.getCondition();

        if(condition.accept(ExpVisitor) != null) {
            ProgramCountNode ifNode = new ProgramCountNode("ifStmt", condition.accept(ExpVisitor));
            programConfidentiality.add(ifNode);
            //The print below can be used when one is not sure that the if-stmt's work properly
            //if(!ifNode.getSecrecyLevel().equals("Low")) System.out.println("Created new if stmt with secrecy level: " + ifNode.getSecrecyLevel());

            ExpVisitor.updateProgramPoint(programConfidentiality);
            Stmt thenCase = ifStmt.getThen();
            thenCase.accept(this);

            if(ifStmt.hasElse()) {
                Stmt elseCase = ifStmt.getElse();
                elseCase.accept(this);
            }

            programConfidentiality.remove(ifNode);
            ExpVisitor.updateProgramPoint(programConfidentiality);
        }
    }

    /**
     * Visit function for while-statements. 
     * When we check the while block we might have a higher program point context.
     * The program point is defined by the one we had joined with the secrecylevel of the condition. (default: Low)
     * For this we add the secrecylevel of the condition to the programConfidentiality list and remove it once checked. 
     * @param whileStmt - the while stmt that has to respect the while rule.
     * It is very similar to the if-stmt (without an else).
     */
    public void visit(WhileStmt whileStmt) {
        
        Exp condition = whileStmt.getCondition();

        if(condition.accept(ExpVisitor) != null){
            ProgramCountNode whileNode = new ProgramCountNode("whileStmt", condition.accept(ExpVisitor));
            programConfidentiality.add(whileNode);

            ExpVisitor.updateProgramPoint(programConfidentiality);
            Stmt body = whileStmt.getBody();
            body.accept(this);

            programConfidentiality.remove(whileNode);
            ExpVisitor.updateProgramPoint(programConfidentiality);
        }
    }

    //TODO 1. Update the documentation for this to contain a description of the FnApp addition I wrote
    //TODO 2. Once the differentiation between max/curr secrecy is added we want to return the level for the variable stored in curr
    /**
     * Visit function for expression statements. 
     * For an expression statement we want the expression below to be handled by the expression visitor.
     * @param expressionStmt - the expression stmt that should be visited by the expression visitor.
     */
    public void visit(ExpressionStmt expressionStmt) {
        Exp expStmtChild = expressionStmt.getExp();
        expStmtChild.accept(ExpVisitor);
        
        if(!containsFnAppHelper(expStmtChild)) {
            return;
        }

        FnApp possibleSecrecyFnApp = getFnAppHelper(expStmtChild);
        
        if(possibleSecrecyFnApp.getName().equals("secrecy")) {
            
            List<PureExp> fnAppParameters = possibleSecrecyFnApp.getParamList();
            
            if(fnAppParameters.getNumChild() == 2 && fnAppParameters.getChild(0) instanceof PureExp secPureExp) {
                String searchedVariable = secPureExp.toString();
                String secrecyFnAppValue = secPureExp.accept(ExpVisitor);
                    
                if (secrecyFnAppValue == null) {
                    secrecyFnAppValue = secrecyLatticeStructure.getMinSecrecyLevel();
                }

                String expectedLevelOfVariable = fnAppParameters.getChild(1).toString();
                expectedLevelOfVariable = expectedLevelOfVariable.replace("StringLiteral","").replace("(","").replace(")","");

                if(!secrecyLatticeStructure.isValidLabel(expectedLevelOfVariable)) {
                    //If the level is not valid then return that
                    errors.add(new TypeError(expressionStmt, ErrorMessage.SECRECY_LEVEL_NON_EXISTANT, expectedLevelOfVariable));
                } else {
                    if(!expectedLevelOfVariable.equals(secrecyFnAppValue)) {
                    //If the level is valid but it's not the same as the level of the exp return an error not equal!
                    errors.add(new TypeError(expressionStmt, ErrorMessage.SECRECY_FNAPP_NOT_EQUAL, searchedVariable.toString(), expectedLevelOfVariable, secrecyFnAppValue));
                    }
                }
            }
        }
    }

    /**
     * Visit function for varDeclStmt statements.
     * We want to ensure that if a declaration has an initialization (exp) that we visit the init with the expression visitor.
     * @param varDeclStmt - the variable declaration statement that has to respect the rule.
     */
    public void visit(VarDeclStmt varDeclStmt) {

        VarDecl varDecl = varDeclStmt.getVarDecl();
        
        //We need to get the level here for the check because we can't find it in the usual list
        //until after this check is performed (I assume)
        //Assume lowest possible value
        String lhsLevel = secrecyLatticeStructure.getMinSecrecyLevel();
        
        //If there is an annotation extract it if it's for our secrecy annotation
        if (varDeclStmt.getAnnotationList() != null) {
            for (Annotation ann : varDeclStmt.getAnnotationList()) {
                if (ann instanceof TypedAnnotation typedAnn) {

                    ASTNode<?> valueNode = typedAnn.getChild(0);
                    ASTNode<?> nameNode  = typedAnn.getChild(1);

                    if ("Secrecy".equals(nameNode.toString()) && valueNode instanceof DataConstructorExp dataCon) {
                        String levelName = dataCon.getConstructor();

                        if (!secrecyLatticeStructure.isValidLabel(levelName)) {
                            errors.add(new TypeError(typedAnn, ErrorMessage.WRONG_SECRECY_ANNOTATION_VALUE, levelName));
                            return;
                        }

                        //TODO about this one I am not completly sure if thats right
                        //1. Asma thought I had an open issue and it might have been the vardeclstmt
                        //2. In this branch the _currentSecrecy got added and the old became _maxSecrecy which now is also used below here
                        //Requires testing but need to ensure it should be max and not current below!!!
                        //System.out.println("HERE NOW WORKS?"+varDeclStmt);
                        //System.out.println("Levelname: " + levelName);
                        lhsLevel = levelName;
                        if(levelName != null)_maxSecrecy.put(varDecl, levelName);
                        break;
                    }
                }
            }
        }

        if(varDecl.hasInitExp()){
            Exp initExp = varDecl.getInitExp();
            String rhsLevel = initExp.accept(ExpVisitor);
            Set<String> rhsLevelSet = secrecyLatticeStructure.getSetForSecrecyLevel(rhsLevel);
            
            if(!(lhsLevel.equals(rhsLevel) || rhsLevelSet.contains(lhsLevel))) {
                errors.add(new TypeError(varDeclStmt, ErrorMessage.SECRECY_LEAKAGE_ERROR_FROM_TO, rhsLevel, initExp.toString(), lhsLevel, varDecl.getName()));
            }
        }
    }

    /**
     * Visit function for await statements. 
     * When we check an await we need to add it to the programConfidentiality.
     * Once the await finishes we have a get so between await and get everything gets the higher program context.
     * The level of the "higher context" is defined by the level of the await's value.
     * @param awaitStmt - the await stmt that has to be handled similar to the if-stmt.
     * Handling performed by with the helper function handleGuards().
     */
    public void visit(AwaitStmt awaitStmt) {

        Guard getGuard = awaitStmt.getGuard();
        handleGuards(getGuard);
    
    }

    /**
     * Helper for the handling of the different guard kinds.
     * If the guard is an And call it recursive for the two sub guards. 
     * If it is an ExpGuard or ClaimGuard we want to add it to the programConfidentiality. (Remove only on the get)
     * @param inGuard - the gurad we want to handle.
     */
    private void handleGuards(Guard inGuard) {

        String inGuardChild = inGuard.getChild(0).toString();
        
        if (inGuard instanceof ExpGuard expGuard) {
  
            Exp awaitExpr = (Exp) expGuard.getChild(0);
            String getAwaitSecrecy = awaitExpr.accept(ExpVisitor);
            programConfidentiality.add(new ProgramCountNode(inGuardChild, getAwaitSecrecy));

        } else if (inGuard instanceof ClaimGuard claimGuard) {

            VarOrFieldUse awaitClaim = (VarOrFieldUse) claimGuard.getChild(0);
            String getAwaitSecrecy = awaitClaim.accept(ExpVisitor);

            programConfidentiality.add(new ProgramCountNode(inGuardChild, getAwaitSecrecy));

        } else if (inGuard instanceof AndGuard andGuard) {

            handleGuards(andGuard.getLeft());
            handleGuards(andGuard.getRight());
        }
        
        ExpVisitor.updateProgramPoint(programConfidentiality);
    }

    /**
     * Allows to update the current program secrecy list on a change.
     * @param newConfidentiality - the list but with the new changes.
     */
    public void updateProgramPoint(LinkedList<ProgramCountNode> newConfidentiality) {
        programConfidentiality = newConfidentiality;
    }

    public boolean containsFnAppHelper(Exp expression) {

        if(expression instanceof FnApp) {
            return true;
        }

        if(expression instanceof Unary unaryExp) {
            containsFnAppHelper(unaryExp);
        } else if(expression instanceof Binary binaryExp) {
            if (containsFnAppHelper(binaryExp.getLeft()) || (containsFnAppHelper(binaryExp.getRight()))) {
                return true;
            }
        }

        return false;
    }

    public FnApp getFnAppHelper(Exp expression) {

        if(expression instanceof FnApp fnapp) {
            return fnapp;
        }

        if(expression instanceof Unary unaryExp) {
            getFnAppHelper(unaryExp);
        } else if(expression instanceof Binary binaryExp) {
            if (containsFnAppHelper(binaryExp.getLeft())) {
                getFnAppHelper(binaryExp.getRight());
            } else if (containsFnAppHelper(binaryExp.getRight())) {
                getFnAppHelper(binaryExp.getRight());
            }
        }

        return null;
    }
}
