/**
 * Copyright (c) 2009-2011, The HATS Consortium. All rights reserved. 
 * This file is licensed under the terms of the Modified BSD License.
 * Written by @Maximilian_Paul for questions please refer to uukln@student.kit.edu
 */
package org.abs_models.frontend.typechecker.ext;

import java.util.HashSet;
import java.util.Set;
import java.util.HashMap;
import java.util.LinkedList;

import org.abs_models.frontend.analyser.ErrorMessage;
import org.abs_models.frontend.analyser.TypeError;
import org.abs_models.frontend.ast.*;

/**
 * This class is using two phases which both run over the model. 
 * The first phase extracts the secrecy annotations and their level, as well as running a few basic checks.
 * The second phase performs a check for each statement/expression
 */
public class SecrecyAnnotationChecker extends DefaultTypeSystemExtension {

    /**
     * Stores all methods for each class and information about if they are already checked and/or if they held (were secure).
     */
    private static LinkedList<SecrecyMethod> methodList = new LinkedList<SecrecyMethod>();

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
    private SecrecyStmtVisitor visitor;               

    /**
     * List holds entries for confidentiality levels if evaluated at a point in time it is the current secrecylevel. 
     */
    private LinkedList<ProgramCountNode> programConfidentiality;
    
    /**
     * The constructor for the SecrecyAnnotationChecker a class that checks a given model.
     * @param m - the ABS model that we want to check, is already parsed before.
     */
    protected SecrecyAnnotationChecker(Model m) {
        super(m);

        programConfidentiality = new LinkedList<ProgramCountNode>();

        if (m.secrecyLatticeStructure != null) {
            secrecyLatticeStructure = m.secrecyLatticeStructure;
            programConfidentiality.add(new ProgramCountNode("default", secrecyLatticeStructure.getMinSecrecyLevel()));
        }
    }

    /**
     * This is the main method for the SecrecyAnnotationChecker it calls the two phases and contains some prints for sanity checking.
     * @param model - the ABS model that we want to check
     */
    @Override
    public void checkModel(Model model) {

        if (secrecyLatticeStructure == null){
            System.out.println("Secrecy lattice was null!"); //means we dont want to perform any of these checks
            return;
        }

        firstExtractionPhasePass(model); 

        visitor = new SecrecyStmtVisitor(_maxSecrecy, _currentSecrecy, secrecyLatticeStructure, errors, programConfidentiality);

        secondTypecheckPhasePass(model); 
        

        //todo if there is something I need/want to do as last thing I can/should do it here
        
        //todo to be removed later
        System.out.println("Print new annotated Values (MAX): " + _maxSecrecy.toString());
        System.out.println("Print new annotated Values (CURR): " + _currentSecrecy.toString());
        System.out.println("Print all Levels: " + secrecyLatticeStructure.getSecrecyLevels().toString());
        System.out.println("Print the order" + secrecyLatticeStructure.getLatticeOrder().toString());
        System.out.println("Confidentiality of current program point is: " + programConfidentiality.getLast().getSecrecyLevel());
        System.out.println("Print all methods in from all classes:" + methodList);
    }

    /**
     * First phase (extraction) retrieves and stores the following information from the model/ast.
     * 
     * 1. Stores all the methods declared from the interfaces that are implemented by the class
     * 2. Extracts field annotations and stores them to the secrecy hashmap
     * 3. Extracts the annotation for methods of the CLASS for their return values and their parameters && running the check from 1.
     *  3.1 - the returnvalue | 3.2 - each parameter | 3.3 - the check between method declaration and it's implementation
     * 
     * 4. Extracts the annotation for methods of INTERFACES for their return values and their parameters
     *  4.1 - the returnvalue | 4.2 - each parameter
     * 
     * @param model - the model from which we retrieve the secrecy values and on which we perform the first check
     * 
     */
    private void firstExtractionPhasePass(Model model){
        for (CompilationUnit cu : model.getCompilationUnits()) {
            for (ModuleDecl moduleDecl : cu.getModuleDecls()) {
                for (Decl decl : moduleDecl.getDecls()) {
                    if (decl instanceof ClassDecl classDecl) {

                        //1.
                        Set<MethodSig> declaredInterfaceMethods = new HashSet<MethodSig>();
                        
                        if(classDecl.hasImplementedInterfaceUse()) {
                            
                            ASTNode<?> interfaceSet = classDecl.getImplementedInterfaceUseList();

                            for(InterfaceTypeUse implementedInterface : classDecl.getImplementedInterfaceUseList()) {

                                InterfaceDecl usedInterfaceDecl = (InterfaceDecl) implementedInterface.getDecl();

                                for(MethodSig declaredMethod : usedInterfaceDecl.getBodyList()) {

                                    declaredInterfaceMethods.add(declaredMethod);  
                                }

                            }
                        }
        
                        //2.
                        for(FieldDecl fieldDecl : classDecl.getFields()) {
                            String level = extractSecrecyValue(fieldDecl);
                            if(level != null)_maxSecrecy.put(fieldDecl, level);
                        }
                        
                        //3.
                        for (MethodImpl method : classDecl.getMethods()) {

                            methodList.add(new SecrecyMethod(classDecl, method));

                            for (Stmt stmt : method.getBlock().getStmtList()) {

                                extractVarDeclStmt(stmt);
                                
                            }
                            
//                            if (method.getMethodSig() == null) {
//                                return;
//                            }
//
                            MethodSig methodSigNat = method.getMethodSig();

                            //3.1
                            String Returnlevel = extractSecrecyValue(method.getMethodSig());
                            if(Returnlevel != null)_maxSecrecy.put(method.getMethodSig(), Returnlevel);

                            //3.2
                            for(ParamDecl parameter : method.getMethodSig().getParamList()) {
                                String Parameterlevel = extractSecrecyValue(parameter);
                                if(Parameterlevel != null)_maxSecrecy.put(parameter, Parameterlevel);
                            }

                            //3.3
                            for(MethodSig declaredCandidate : declaredInterfaceMethods) {
                                if (compareMethodSignatures(method.getMethodSig(), declaredCandidate)) {
                                    //System.out.println(method.getMethodSig() + " is implementation of " + declaredCandidate);
                                    checkRespectingSecrecyLevels(method.getMethodSig(), declaredCandidate);
                                }
                            }

                        }

                    //4.0
                    } else if (decl instanceof InterfaceDecl interfaceDecl) {
                        for (MethodSig methodSig : interfaceDecl.getBodyList()) {
                            
                            //4.1
                            String Returnlevel = extractSecrecyValue(methodSig);
                            if(Returnlevel != null)_maxSecrecy.put(methodSig, Returnlevel);

                            //4.2
                            for(ParamDecl parameter : methodSig.getParamList()) {
                                String Parameterlevel = extractSecrecyValue(parameter);
                                if(Parameterlevel != null)_maxSecrecy.put(parameter, Parameterlevel);
                            }
                        }
                    }
                }
            }
        }
        //_currentSecrecy = new HashMap<>(_maxSecrecy);
    }

    /**
     * This methods "extracts" the secrecylevel for a given node.
     * For this it reads the secrecylevel out of the annotationlist and ensures it is part of our lattice structure (validity).
     * If the user uses his own secrecy lattice structure than that is considerd! 
     * 
     * @param ASTNode<?> - the ast node that "might" have the secrecy annotation
     * @return - returns the secrecylevel or if there is none returns null
     */
    private String extractSecrecyValue(ASTNode<?> declNode) {

        List<Annotation> annotations = null;

        //TODO check which of these are used at any time
        if (declNode instanceof ParamDecl param) {
            annotations = param.getAnnotationList();
        } else if (declNode instanceof FieldDecl field) {
            annotations = field.getTypeUse().getAnnotationList();
        } else if (declNode instanceof VarDeclStmt varDeclStmt) {
            annotations = varDeclStmt.getAnnotationList();
        } else if (declNode instanceof MethodSig sig) {
            annotations = sig.getReturnType().getAnnotationList();
        } else if (declNode instanceof TypedVarOrFieldDecl typedVar) {
            annotations = typedVar.getTypeUse().getAnnotationList();
        } 

        if (annotations == null) return null;

        for (Annotation ann : annotations) {
            if (ann instanceof TypedAnnotation typedAnn) {

                ASTNode<?> valueNode = typedAnn.getChild(0);
                ASTNode<?> nameNode  = typedAnn.getChild(1);

                if ("Secrecy".equals(nameNode.toString()) && valueNode instanceof DataConstructorExp dataCon) {
                    String levelName = dataCon.getConstructor();

                    if (!secrecyLatticeStructure.isValidLabel(levelName)) {
                        errors.add(new TypeError(typedAnn, ErrorMessage.WRONG_SECRECY_ANNOTATION_VALUE, levelName));
                        return null;
                    }

                    //System.out.println("Levelname: " + levelName);
                    return levelName;
                }
            }
        }
        return null;
    }

    private void extractVarDeclStmt(Stmt inputStmt) {
        if(inputStmt instanceof VarDeclStmt localVariable) {

            String localVariableLevel = extractSecrecyValue(localVariable);
            if(localVariableLevel != null)_maxSecrecy.put(localVariable.getVarDecl(), localVariableLevel);
            //System.out.println(localVariable);

        } else if (inputStmt instanceof Block blockStmt) {

            for (Stmt stmt : blockStmt.getStmtList()) {
                extractVarDeclStmt(stmt);
            }

        } else if (inputStmt instanceof IfStmt ifStmt) {

            extractVarDeclStmt(ifStmt.getThen());

            if(ifStmt.hasElse()) extractVarDeclStmt(ifStmt.getElse());

        } else if (inputStmt instanceof WhileStmt whileStmt) {

            extractVarDeclStmt(whileStmt.getBody());

        }
    }

    /**
     * Second phase which checks for the secrecy typerules.
     * A class satisfies the secrecy typerules if each method of a class satisfies them.
     * A method satisfies the secrecy typerules if each statement, expression, etc. satisfies them.
     * We have a SecrecyStmtVisitor which performs the statement checks and it is called on each statement here.
     * 
     * @param model - the ABS model on which we want to check the respecting of the secrecy typerules
     */
    private void secondTypecheckPhasePass(Model model){
        
        for (CompilationUnit cu : model.getCompilationUnits()) {
            for (ModuleDecl moduleDecl : cu.getModuleDecls()) {
                for (Decl decl : moduleDecl.getDecls()) {
                    if (decl instanceof ClassDecl classDecl) {
                        //For each class 
                        //TODO this is to "later" reset the current secrecy before we check the next method
                        //_currentSecrecy = new HashMap<>(_maxSecrecy);
                        for (MethodImpl method : classDecl.getMethods()) {
                            _currentSecrecy = new HashMap<>(_maxSecrecy);
                            visitor.updateCurrentSecrecy(_currentSecrecy);
                            //For each method of that class
                            //TODO probably it's best to start a check here and after each method check we have to reset the current to be the same as max
                            method.getBlock().accept(visitor);
                            //Get the block and then perform a check on each statement in the block!
                            //for (Stmt stmt : block.getStmtList()) {
                            //    stmt.accept(visitor);
                            //}
                        }
                    }
                }
            }
        }
        /*
       //This should now be replaceable by instead checking each method in the methodList
        for (SecrecyMethod methodToCheck : methodList) {
            if(!methodToCheck.getIsChecked()) {

                MethodImpl methodToCheckImpl = methodToCheck.getMethodNode();
                MethodSig methodToCheckSig = methodToCheckImpl.getMethodSig();
                String methodToCheckName = methodToCheckSig.getName();
                int errorCountBefore = errors.getErrorCount();
                //System.out.println("Error Count before checking: " + methodToCheckName + ":" + errorCountBefore);

                Block methodToCheckBlock = methodToCheckImpl.getBlock();
                methodToCheckBlock.accept(visitor);
                
                int errorCountAfter = errors.getErrorCount();
                //System.out.println("Error Count after checking: " + methodToCheckName + ":" + errorCountAfter);
                if(errorCountAfter == errorCountBefore) {
                    methodToCheck.setIsSecure(true);
                } else {
                    methodToCheck.setIsSecure(false);
                    System.out.println(methodToCheck);
                }
                methodToCheck.setIsChecked(true);
                _currentSecrecy = new HashMap<>(_maxSecrecy);
            }
        }*/
    }

    /**
     * Helper method that checks if a two methods a and b have the same signature.
     * To have the same signature they have to have matching: Name, Returntype, Parameter (count, names and types)
     * 
     * @param methodA - the first method that might have the same signature
     * @param methodB - the second method that might have the same signature
     * 
     * @return true if the method signatures match in the listed aspects, false otherswise
     */
    private boolean compareMethodSignatures(MethodSig methodA, MethodSig methodB) {

        if(methodA.getName().equals(methodB.getName())){

            if(methodA.getReturnType().toString().equals(methodB.getReturnType().toString())){

                
                List<ParamDecl> paramListA = methodA.getParamList();
                List<ParamDecl> paramListB = methodB.getParamList();

                if (paramListA.getNumChild() != paramListB.getNumChild()) {
                    return false;
                }

                LinkedList<ParamDecl> paramAList = new LinkedList<ParamDecl>();
                for(ParamDecl paramA:methodA.getParamList()){
                    paramAList.add(paramA);
                }
                LinkedList<ParamDecl> paramBList = new LinkedList<ParamDecl>();
                for(ParamDecl paramB:methodB.getParamList()){
                    paramBList.add(paramB);
                }

                for(ParamDecl paramA : paramListA) {
                    for(ParamDecl paramB : paramListB) {
                        if (paramB.getName().equals(paramA.getName())){ 
                            if(paramB.getTypeUse().toString().equals(paramA.getTypeUse().toString())){
                                paramAList.remove(paramA);
                                paramBList.remove(paramB);
                            } else {
                                return false;
                            }
                        }
                    }
                }

                if(!paramAList.isEmpty() || !paramBList.isEmpty())return false;

            } else {
                return false;
            }
        } else {
            return false;
        }
        return true;
    }

    /**
     * This method checks a method implementation of a class that implements an interface that has a declaration of the same method.
     * The rules have to be as follows:
     * 1. the secrecylevel of the implementation can at most be as high as the methods declaration in the interface.
     * 2. the secrecylevel of each parameter of the implementation can at most be as high as the parameter from the methods declaration.
     * 
     * @param implementation - the method signature of a method that was implemented in a class that implements the interface
     * @param definition - the method signature of a method that was declared in an interface
     */
    private void checkRespectingSecrecyLevels(MethodSig implementation, MethodSig definition) {

        String definitionLevel = _maxSecrecy.get(definition);
        
        if(definitionLevel == null) {
            definitionLevel = secrecyLatticeStructure.getMinSecrecyLevel();
        }
        
        String implementationLevel = _maxSecrecy.get(implementation);
        
        if(implementationLevel == null) {
            implementationLevel = secrecyLatticeStructure.getMinSecrecyLevel();
        }

        Set<String> implementationSet = secrecyLatticeStructure.getSetForSecrecyLevel(implementationLevel);
        
        if(!implementationSet.contains(definitionLevel) && !implementationLevel.equals(definitionLevel)) {
            errors.add(new TypeError(implementation.getReturnType(), ErrorMessage.SECRECY_LEAKAGE_ERROR_AT_MOST, definitionLevel, implementationLevel));
        }
        
        for(ParamDecl implementationParam : implementation.getParamList()) {
            for(ParamDecl definitionParam : definition.getParamList()) {

                if(definitionParam.getName().equals(implementationParam.getName())){
                    
                    implementationLevel = _maxSecrecy.get(implementationParam);
                    definitionLevel = _maxSecrecy.get(definitionParam);

                    if(definitionLevel == null) {
                        definitionLevel = secrecyLatticeStructure.getMinSecrecyLevel();
                    }

                    if(implementationLevel == null) {
                        implementationLevel = secrecyLatticeStructure.getMinSecrecyLevel();
                    }

                    if(!implementationLevel.equals(definitionLevel)){
                        implementationSet = secrecyLatticeStructure.getSetForSecrecyLevel(implementationLevel);

                        if(!implementationSet.contains(definitionLevel)) {
                            errors.add(new TypeError(implementation.getReturnType(), ErrorMessage.SECRECY_LEAKAGE_ERROR_AT_MOST, definitionLevel, implementationLevel));
                        }
                    }
                }
            }
        }
    }

}

