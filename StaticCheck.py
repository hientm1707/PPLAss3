
"""
 * @author nhphung
"""
from abc import ABC, abstractmethod, ABCMeta
from dataclasses import dataclass
from typing import List, Tuple
from AST import * 
from Visitor import *
from Utils import Utils
from StaticError import *
from functools import *

class Type(ABC):
    __metaclass__ = ABCMeta
    pass
class Prim(Type):
    __metaclass__ = ABCMeta
    pass
class IntType(Prim):
    pass
class FloatType(Prim):
    pass
class StringType(Prim):
    pass
class BoolType(Prim):
    pass
class VoidType(Type):
    pass
class Unknown(Type):
    pass

@dataclass
class ArrayType(Type):
    dimen:List[int]
    eletype: Type

@dataclass
class MType:
    intype:List[Type]
    restype:Type

@dataclass
class Symbol:
    name: str
    mtype:Type

class StaticChecker(BaseVisitor,Utils):
    def __init__(self,ast):
        self.ast = ast
        self.global_envi = [
Symbol("int_of_float",MType([FloatType()],IntType())),
Symbol("float_of_int",MType([IntType()],FloatType())),
Symbol("int_of_string",MType([StringType()],IntType())),
Symbol("string_of_int",MType([IntType()],StringType())),
Symbol("float_of_string",MType([StringType()],FloatType())),
Symbol("string_of_float",MType([FloatType()],StringType())),
Symbol("bool_of_string",MType([StringType()],BoolType())),
Symbol("string_of_bool",MType([BoolType()],StringType())),
Symbol("read",MType([],StringType())),
Symbol("printLn",MType([],VoidType())),
Symbol("printStr",MType([StringType()],VoidType())),
Symbol("printStrLn",MType([StringType()],VoidType()))]   

    def findnameinscope(self,name,lst,func):
        for x in lst:
            if name == func(x):
                return x
        return None  

        
    def check(self):
        return self.visit(self.ast,self.global_envi)

    def extendScope(self, scope, name, dimen, init): #name:str, dimen: List[Exp], init bat ki
        if len(dimen) > 0: # ArrayType
            if init is None: # ArrayType and Unknown
                scope += [Symbol(name, ArrayType(dimen, Unknown()))]
            else:
                varType = self.visit(init, scope) #ArrayType and PrimType
                scope += [Symbol(name, ArrayType(dimen, varType))]
        else: #Scalar
            if init is None: # Unknown
                scope += [Symbol(name,Unknown())]
            else: #PrimType
                varType = self.visit(init, scope)
                scope += [Symbol(name, varType)]
        return scope
    


    def kind(self,element):
        if isinstance(element,tuple) and len(element)==2:
            return 'ID'
        elif isinstance(element, tuple) and len(element) == 3:
            return 'ArrayCell'
        elif isinstance(element,list)and len(element)==2:
            return 'N-aryOp'
        elif isinstance(element,list) and len(element)==3:
            return 'CallExpression'
        else:
            return 'Literal'


    def getNearestElewName(self, name, scope): #return not None la ko bi Undeclare
        #RETURN VE THANG CHECK TRONG SCOPE
        # name : Id name : str
        # scope = [c, paramScope, localScope] 
        # scope[1] = c : global scope
        # scope[2] = paramScope
        # scope[3] = localScope
        i = len(scope) - 1 
        while i >= 1:
            check = self.findnameinscope(name, scope[i], lambda x : x.name)
            if check is None:
                if i == 1:
                    raise Undeclared(Identifier(), name)
                else:
                    i = i - 1
            else:
                return check        


    def inferAtoBinC(self, name, typeInferred, scope):
        i = len(scope) - 1
        while i >= 1:
            check = self.findnameinscope(name, scope[i], lambda x : x.name)
            if check is not None:
                if i == 2: 
                    ind = scope[i].index(check)
                    funcname = scope[0] 
                    funcsymbol = self.findnameinscope(funcname, scope[1], lambda x : x.name)
                    funcsymbol.mtype.intype[ind] = typeInferred
                if type(check.mtype) is ArrayType: # arraytype
                    check.mtype.eletype = typeInferred
                else: # id
                    check.mtype = typeInferred
                break
            else: i = i - 1
    
    def funcInferType(self, funcName, paramIndex, typeInferred, scope):
        # scope[1] = c = global scope
        # funcdecl chi duoc chua o global scope 
        func = self.findnameinscope(funcName, scope[1], lambda x: x.name)
        if paramIndex is None: # function return type inferred
            func.mtype.restype = typeInferred
        else: # function param type inferred
            if type(func.mtype.intype[paramIndex]) is ArrayType:
                func.mtype.intype[paramIndex].eletype = typeInferred
            else:
                func.mtype.intype[paramIndex] = typeInferred

    def checkOpisType(self, operandExpr, operandType, scope):
        #1: An toan
        #2: Type mismatch
        #3: sau nay Typecannot be inferred
        if (self.kind(operandExpr)=='ID'): #Id
            if type(operandExpr[1]) is Unknown:
                self.inferAtoBinC(operandExpr[0], operandType(), scope)
            else: # Id type is not unknown
                if type(operandExpr[1]) is not operandType:
                    return 2
                else:
                    return 1
                if (self.checkOpisType):
                    return scope
        elif (self.kind(operandExpr)=='ArrayCell'): # ArrayCell
            if operandExpr[2] == False:
                return 3
            else:
                if type(operandExpr[1]) is Unknown:
                    self.inferAtoBinC(operandExpr[0], operandType(), scope)
                else:
                    if type(operandExpr[1]) is not operandType:
                        return 2
                    else:
                        return 1
        elif (self.kind(operandExpr)=='N-aryOp'): # BinaryOp / UnaryOp
            if operandExpr[1] == False:
                return 3
            else:
                if type(operandExpr[0]) is not operandType:
                    return 2
                else:
                    return 1
        elif (self.kind(operandExpr)=='CallExpression'): # CallExpr
            if operandExpr[2] == False:
                return 3
            else:
                if type(operandExpr[1]) is Unknown:
                    self.funcInferType(operandExpr[0], None, operandType(), scope)
                else:
                    if type(operandExpr[1]) is not operandType:
                        return 2
                    else:
                        return 1
        else: # Literal
            if type(operandExpr) is not operandType:
                return 2
            else:
                return 1

    def traverseThruStmt(self, listVardecl, listStmt, Scope):
        # outerScope[0] = globalScope []
        # outerScope[1] = paramScope []
        # outerScope[2] = function local Scope hoac outer Scope []
        stmtLocalScope = []
        for varDecl in listVardecl:
            stmtLocalScope = self.visit(varDecl, stmtLocalScope)
            # tao moi mot stmt local scope va them scope do vao list cac scope hien tai de visit stmt 
        Scope += [stmtLocalScope] 
        stmtInBody = [self.visit(x, Scope) for x in listStmt]
        return stmtInBody    
        
        
    def visitProgram(self, ast, c): #ast = Program()
        # visit VarDecl
        for x in ast.decl:
            if type(x) is VarDecl:
                self.visit(x, c)
                
        entryPoint = False
        # visit FuncDecl lan thu 1 - get All FuncDecl Prototype
        for decl in ast.decl:
            if type(decl) is FuncDecl:
                funcDecl = self.visit(decl,True) # funcDecl = Symbol
                if self.findnameinscope(funcDecl.name, c, lambda o : o.name) is not None:
                    raise Redeclared(Function(),decl.name.name)
                else:
                    c = c+ [funcDecl]
                    
        # visit FuncDecl lan thu 2
        for x in ast.decl:
            if type(x) is FuncDecl:
                self.visit(x, c)

        if entryPoint == False:
            raise NoEntryPoint()



    def visitVarDecl(self, ast, c): #ast = VarDecl()
        vardeclname = ast.variable.name #string
        dimen = ast.varDimen #list[int]
        init = ast.varInit #Literal
        check = self.findnameinscope(vardeclname,c, lambda x: x.name) #Tim tronmg environ co thang Vardecl nay chua, neu chua thi add vo environ
        if check is not None: #Da co trong environ roi, raise
            raise Redeclared(Variable(),vardeclname)
        else: # c = scope truyen vao trong VarDecl, sau khi thuc thi xong thi tra nguoc scope do ra lai
            c= self.extendScope(c,vardeclname,dimen,init) # them variable va cap nhat scope
            return c

    def visitFuncDecl(self, ast, c):
        # lay ra cac thong tin cua Fundecl
        name = ast.name.name #ast cua FunCDECL
        # check parameter decl part in funcdecl
        paramScope = []
        listParameter = ast.param # ast.param = list[VarDecl[] #ast cua FuncDecl
        for param in listParameter:
            parameterName = param.variable.name
            parameterDimen =  param.varDimen #
            parameterInit = param.varInit
            if len(paramScope) == 0: # funcscope = rong~ chi can them vao khong can check
                paramScope = self.extendScope(paramScope, name, parameterDimen, parameterInit)
            else: #funscope != rong~
                check = self.findnameinscope(parameterName, paramScope, lambda x: x.name)
                if check is not None:
                    raise Redeclared(Parameter(),parameterName)
                else: # add parameter vao paramScope
                    paramScope = self.extendScope(paramScope, parameterName, parameterDimen, parameterInit)

        if c == True:    
            #return Symbol function to c
            listEletype = [param.mtype for param in paramScope]
            return Symbol(name,MType(listEletype, Unknown()))


        else: # c = global_envi 
            # lan visit funcdecl thu 2 chi can visit den cac thanh phan cua no, khong cac check cac rang buoc nua~
            # trong body scope thi can tao mot local scope rieng biet, cac vardecl trong local scope nay
            # co the redeclare lai id/func/parameters
            bodyVarDeclList = ast.body[0]
            for bodyvardecl in bodyVarDeclList:
                if bodyvardecl.variable.name in list(map(lambda x:x.name,paramScope)):
                    raise Redeclared(Parameter(),bodyvardecl.variable.name)
            localScope = paramScope
            for bodyvardecl in bodyVarDeclList: # ast.body[0] = [VarDecl()] => x = VarDecl()
                localScope = self.visit(bodyvardecl, localScope)  #visit tung VarDecl trong local scope  
            # local scope = 1 list[vardecl()]
            for x in ast.body[1]:
                self.visit(x, [name, c, paramScope, localScope])
                #Note
    #Den cho nay dang bi '


    def visitId(self, ast, c):
        return (ast.name, self.getNearestElewName(ast.name, c).mtype)
    
    def visitArrayCell(self, ast, c): # ArrayCell la mot expression #ID or ArrayCell
        arr = self.visit(ast.arr,c)
        arrname = arr[0]
        if (self.kind(arr)=='ID'):
           isID = True
        else:
           isID = False

        checker = self.getNearestElewName(arrname, c)

        listDimen = [self.visit(x,c) for x in ast.idx] # ast.idx = [expression], chi co the la int
        inferred = True
        for dimen in listDimen: # check tung dimension cua array, dimen = expression
            if (self.kind(dimen) == 'Id'): # dimen la mot Id
                if type(dimen[1]) is Unknown:
                    self.inferAtoBinC(dimen[0], IntType(), c)
                elif type(dimen[1]) is not IntType:
                    raise TypeMismatchInExpression(ast)
            elif (self.kind(dimen) == 'ArrayCell'): # 
                ########dimen la mot ArrayCell
                if dimen[2] == False:
                    inferred = False
                else:
                    if type(dimen[1]) is Unknown:
                        self.inferAtoBinC(dimen[0], IntType(), c)
                    elif type(dimen[1]) is not IntType:
                        raise TypeMismatchInExpression(ast)
            elif (self.kind(dimen) == 'N-aryOp'): # dimen la mot BinaryOp hoac UnaryOp
                if dimen[1] == False:
                    inferred = False
                else:
                    if type(dimen[0]) is not IntType:
                        raise TypeMismatchInExpression(ast)
            elif (self.kind(dimen) == 'CallExpression'): # dimen la mot CallExpr
                if dimen[2] == False:
                    inferred = False
                else:
                    if type(dimen[1]) is Unknown:
                        self.funcInferType(dimen[0], None, IntType(), c)
                    elif type(dimen[1]) is not IntType:
                        raise TypeMismatchInExpression(ast)
            else: # dimen la mot Literal
                if type(dimen) is not IntType:
                    raise TypeMismatchInExpression(ast)
       
        if type(checker.mtype) is MType:
            returntype = checker.mtype.restype
        else:
            returntype= checker.mtype.eletype

        return (arrname,  returntype, inferred)
        
#Xem lai cho ìnferred = false
    def visitBinaryOp(self, ast, c):
        operator = ast.op 
        leftExpr = self.visit(ast.left, c)
        rightExpr = self.visit(ast.right, c)
        inferred = True
        # check BinaryOp:
        # Arithmetic operators
        if operator in ['+','-','*','\\','%']:
            left = self.checkOpisType(leftExpr, IntType, c)
            right = self.checkOpisType(rightExpr, IntType, c)
            if (left == 3) or (right == 3):
                inferred = False
                return [IntType(), inferred]
            elif (left == 2) or (right == 2):
                raise TypeMismatchInExpression(ast)
            else:
                return [IntType(), inferred]
        elif operator in ['-.','+.','*.','\\.']:
            left = self.checkOpisType(leftExpr, FloatType, c)
            right = self.checkOpisType(rightExpr, FloatType, c)
            if (left == 3) or (right == 3):
                inferred = False
                return [FloatType(), inferred]
            elif (left == 2) or (right == 2):
                raise TypeMismatchInExpression(ast)
            else:
                return [FloatType(), inferred]
        # Boolean operators
        elif operator in ['&&','||']:
            left = self.checkOpisType(leftExpr, BoolType, c)
            right = self.checkOpisType(rightExpr, BoolType, c)
            if (left == 3) or (right == 3):
                inferred = False
                return [BoolType(), inferred]
            elif (left == 2) or (right == 2):
                raise TypeMismatchInExpression(ast)
            else:
                return [BoolType(), inferred]
        # Relations operators
        elif operator in ['==','!=','<','>','<=','>=']:
            left = self.checkOpisType(leftExpr, IntType, c)
            right = self.checkOpisType(rightExpr, IntType, c)
            if (left == 3) or (right == 3):
                inferred = False
                return [BoolType(), inferred]
            elif (left == 2) or (right == 2):
                raise TypeMismatchInExpression(ast)
            else:
                return [BoolType(), inferred]
        elif operator in ['=/=','<.','>.','<=.','>=.']:
            left = self.checkOpisType(leftExpr, FloatType, c)
            right = self.checkOpisType(rightExpr, FloatType, c)
            if (left == 3) or (right == 3):
                inferred = False
                return [BoolType(), inferred]
            elif (left == 2) or (right == 2):
                raise TypeMismatchInExpression(ast)
            else:
                return [BoolType(), inferred]
            
    def visitUnaryOp(self,ast,c):
        operator = ast.op
        body = self.visit(ast.body,c)
        inferred = True
        if operator ==  '-': # integer unary sign negation
            expr = self.checkOpisType(body, IntType, c)
            if expr == 3:
                inferred = False
                return [IntType(), inferred]
            elif expr == 2:
                raise TypeMismatchInExpression(ast)
            else:
                return [IntType(), inferred]
        elif operator == '-.' : #float unary sign negation
            expr = self.checkOpisType(body, FloatType, c)
            if expr == 3:
                inferred = False
                return [FloatType(), inferred]
            elif expr == 2:
                raise TypeMismatchInExpression(ast)
            else:
                return [FloatType(), inferred]
        else: # ! negation
            expr = self.checkOpisType(body, BoolType, c)
            if expr == 3:
                inferred = False
                return [BoolType(), inferred]
            elif expr == 2:
                raise TypeMismatchInExpression(ast)
            else:
                return [BoolType(), inferred]

    def visitCallExpr(self,ast,c):
        callerName = ast.method.name # method:Id
        listCallerParam = [self.visit(x,c) for x in ast.param] # param:List[Expr]
        check = self.findnameinscope(callerName, c[1], lambda x : x.name) # c[1] = c = global scope
        if check is None: # khong tim thay function
            raise Undeclared(Function(), callerName)
        elif type(check.mtype) is not MType: # tim thay nhung khong phai la function #
            raise Undeclared(Function(), callerName)
        else: # tim thay function
            inferred = True
            listCalleeParam = check.mtype.intype # check.mtype[0] = Mtype[0] = intype:List[Type]
            calleeReturnType = check.mtype.restype # check.mtype[1] = Mtype[1] = restype:Type
            if len(listCallerParam) != len(listCalleeParam):
                raise TypeMismatchInExpression(ast)
            else:
                for i in range(0, len(listCalleeParam)):
                    callerParam = listCallerParam[i]
                    calleeParam = listCalleeParam[i]
                    if (self.kind(callerParam)=='Id'): # CallerParam = Id
                        if type(callerParam[1]) is Unknown:
                            if type(calleeParam) is Unknown:
                                inferred = False
                            elif type(calleeParam) is ArrayType:
                                if type(calleeParam.eletype) is Unknown:
                                    inferred = False
                                else:
                                    self.inferAtoBinC(callerParam[0], calleeParam.eletype, c)
                            else:
                                self.inferAtoBinC(callerParam[0], calleeParam, c)
                        else: # type caller Param != Unknown
                            if type(calleeParam) is not Unknown: # calleeParam co the la ArryType hoac Id non-Unknown type
                                if type(calleeParam) is ArrayType: # calleeParam la mot ArrayType
                                    if type(calleeParam.eletype) is not Unknown:
                                        if type(callerParam[1]) is not type(calleeParam.eletype):
                                            raise TypeMismatchInExpression(ast)
                                    else:
                                        self.funcInferType(callerName, i , callerParam[1], c)
                                elif type(callerParam[1]) is Unknown:
                                    self.funcInferType(callerName, i , callerParam[1], c)
                                    # CalleeParam la Id non-Unknown type
                                elif type(callerParam[1]) is not type(calleeParam):
                                    raise TypeMismatchInExpression(ast)
                    elif (self.kind(callerParam)=='ArrayCell'): # CallerParam = ArrayCell
                        if callerParam[2] == False:
                            inferred = False
                        else:
                            if type(callerParam[1]) is Unknown: # ArrayCell return type = Unknown
                                if type(calleeParam) is Unknown:
                                    inferred = False
                                elif type(calleeParam) is ArrayType:
                                    if type(calleeParam.eletype) is Unknown:
                                        inferred = False
                                    else:
                                        self.inferAtoBinC(callerParam[0], calleeParam.eletype, c)
                                else:
                                    self.inferAtoBinC(callerParam[0], calleeParam, c)
                            else: # callerParam la mot ArrayCell return type = non Unknown
                                if type(calleeParam) is ArrayType:
                                    if type(calleeParam.eletype) is not Unknown:
                                        if type(callerParam[1]) is not type(calleeParam.eletype):
                                            raise TypeMismatchInExpression(ast)
                                    else:
                                        self.funcInferType(callerName, i, callerParam[1], c)
                                elif type(calleeParam) is Unknown:
                                    self.funcInferType(callerName, i, callerParam[1], c)
                                elif type(callerParam[1]) is not type(calleeParam):
                                    raise TypeMismatchInExpression(ast)
                    elif (self.kind(callerParam)=='N-aryOp'): # CallerParam = UnaryOp hoặc BinaryOp
                        if callerParam[1] == False:
                            inferred = False
                        else:
                            if type(calleeParam) is Unknown:
                                self.funcInferType(callerName, i, callerParam[0], c)
                            elif type(calleParam) is ArrayType:
                                if type(calleeParam.eleType) is Unknown:
                                    self.funcInferType(callerName, i, callerParam[0], c)
                                elif type(calleeParam.eleType) is not type(callerParam[0]):
                                    raise TypeMismatchInExpression(ast)
                            elif type(callerParam[0]) is not type(calleeParam):
                                raise TypeMismatchInExpression(ast)
                    elif (self.kind(callerParam)=='CallExpression'): # callerparam = CallExpr = (name, returntype, True)
                        if callerParam[2] == False:
                            inferred = False
                        else:
                            if type(callerParam[1]) is Unknown: # callerparam = CallExpr = (name, Unknown Type, True)
                                if type(calleeParam) is Unknown:
                                    inferred = False
                                elif type(calleeParam) is ArrayType:
                                    if type(callerParam.eletype) is Unknown:
                                        inferred = False
                                    else:
                                        self.funcInferType(callerParam[0], None, calleeParam.eletype, c)
                                else: # callee param is non-unknown type Id
                                    self.funcInferType(callerParam[0], None, calleeParam, c)
                            else: # callerParam return type is non-Unknown type (name, non-Unknown type, True)
                                if type(calleeParam) is ArrayType:
                                    if type(calleeParam.eletype) is Unknown:
                                        self.funcInferType(callerName, i, callerParam[1], c)
                                    elif type(callerParam[1]) is not type(calleeParam.eletype):
                                        raise TypeMismatchInExpression(ast)
                                elif type(calleeParam) is Unknown:
                                    self.funcInferType(callerName, i, callerParam[1], c)
                                elif type(calleeParam) is not type(callerParam[1]):
                                    raise TypeMismatchInExpression(ast)
                    else: # CallerParam = literral
                        if type(calleeParam) is ArrayType:
                            if type(calleeParam.eletype) is Unknown:
                                self.funcInferType(callerName, i, callerParam, c)
                            elif type(calleeParam.eletype) is not type(callerParam):
                                raise TypeMismatchInExpression(ast)
                        elif type(calleeParam) is Unknown:
                            self.funcInferType(callerName, i, callerParam, c)
                        elif type(calleeParam) is not type(callerParam):
                            raise TypeMismatchInExpression(ast)         
        return [callerName, calleeReturnType, inferred]


    def visitIntLiteral(self, ast, c):
        return IntType()

    def visitFloatLiteral(self, ast, c):
        return FloatType()
    
    def visitStringLiteral(self, ast, c):
        return StringType()

    def visitBooleanLiteral(self, ast, c):
        return BoolType()

    def visitArrayLiteral(self,ast, c):
        if type(ast.value[0])is not ArrayLiteral:
            elementType=self.visit(ast.value[0],c)
            return ArrayType([len(ast.value)],elementType)
        else:
            dimen=[]
            dimensions = ast
            while (type(dimensions) is ArrayLiteral):
                dimen.append(len(dimensions.value))
                dimensions = dimensions.value[0]
            return ArrayType(dimen,self.visit(ast.value[0],c))

    

    def visitAssign(self, ast, c):
        # c = [c, paramScope, localScope] 
        # c[0] = c : global scope
        # c[1] = paramSope
        # c[2] = localScope
        left = self.visit(ast.lhs, c) # lhs = Id hoac ArrayCell
        right = self.visit(ast.rhs, c) # rhs = expression
        if type(left[1]) is VoidType:
            raise TypeMismatchInStatement(ast)
        elif (len(left) == 3) and (left[2] == False): # neu left la mot ArrayCell co type la 
            raise TypeCannotBeInferred(ast)
        else: # ArrayCell co inferred = True / Id
            if type(left[1]) == Unknown: # left la mot type Unknown
                if (self.kind(right) == 'ID'): # right la mot id
                    if type(right[1]) is Unknown:
                        raise TypeCannotBeInferred(ast)
                    else:
                        self.inferAtoBinC(left[0], right[1], c)

                elif (self.kind(right)=='ArrayCell'): # right la mot arrayCell
                    if right[2] == False:
                        raise TypeCannotBeInferred(ast)
                    elif type(right[1]) is Unknown:
                        raise TypeCannotBeInferred(ast)
                    else:
                        self.inferAtoBinC(left[0], right[1], c)

                elif (self.kind(right)=='N-aryOp'): # right la mot BinaryOp / UnaryOp
                    if right[1] == False:
                        raise TypeCannotBeInferred(ast)
                    else:
                        self.inferAtoBinC(left[0], right[0], c)

                elif (self.kind(right)== 'CallExpression'): # right la mot CallExpr
                    if right[2] == False:
                        raise TypeCannotBeInferred(ast)
                    elif type(right[1]) is Unknown:
                        raise TypeCannotBeInferred(ast)
                    else:
                        self.inferAtoBinC(left[0], right[1], c)
                else: # right la mot literal
                    self.inferAtoBinC(left[0], right, c)

            else: # left la mot type non Unknown
                if (self.kind(right) == 'ID'): # right la mot id
                    if type(right[1]) is Unknown:
                        self.inferAtoBinC(right[0], left[1], c)
                    elif type(left[1]) is not type(right[1]):
                        raise TypeMismatchInStatement(ast)
                elif (self.kind(right) == 'ArrayCell'): # right la mot arrayCell
                    if right[2] == False:
                        raise TypeCannotBeInferred(ast)
                    elif type(right[1]) is Unknown:
                        self.inferAtoBinC(right[0], left[1], c)
                    elif type(left[1]) is not type(right[1]):
                        raise TypeMismatchInStatement(ast)
                elif (self.kind(right) == 'N-aryOp'): # right la mot BinaryOp / UnaryOp
                    if right[1] == False:
                        raise TypeCannotBeInferred(ast)
                    elif type(left[1]) is not type(right[0]):
                        raise TypeMismatchInStatement(ast)
                elif (self.kind(right) == 'CallExpression'): # right la mot CallExpr
                    if right[2] == False:
                        raise TypeCannotBeInferred(ast)
                    elif type(right[1]) is Unknown:
                        self.funcInferType(right[0], None, left[1], c)
                    elif type(left[1]) is not type(right[1]):
                        raise TypeMismatchInStatement(ast)
                else: # right la mot literal
                    if type(left[1]) is not type(right):
                        raise TypeMismatchInStatement(ast)

    def visitIf(self, ast, c):
        # c[0] = global enviroment
        # c[1] = param enviroment
        # c[2] = function local enviroment
        for x in ast.ifthenStmt: #ifthenStmt:List[Tuple[Expr,List[VarDecl],List[Stmt]]] => x = Tuple[]
            expression = self.visit(x[0],c) # conditional expression
            listVarDecl = x[1]
            listStmt = x[2]
            check = self.checkOpisType(expression, BoolType, c)
            if check == 3: 
                raise TypeCannotBeInferred(ast)
            elif check == 2:
                raise TypeMismatchInStatement(ast)
            else:
                ifThenBodyStmt = self.traverseThruStmt(listVarDecl,listStmt,c)
       # elseVardecl =
       # elseStmt = 
        elseBodyStmt = self.traverseThruStmt( ast.elseStmt[0], ast.elseStmt[1], c) 
    
    def visitFor(self, ast, c):
        e1 = self.visit(ast.expr1, c)
        e2 = self.visit(ast.expr2, c)
        e3 = self.visit(ast.expr3, c)
        id = ast.idx1
        idname = id.name
        if type(id) != IntType:
            if type(id) == Unknown:
                check = self.findnameinscope(idname,c[3],lambda symbol: symbol.name)
                check.mtype=IntType()
            else:
                raise TypeMismatchInStatement(ast)
        tc1 = self.checkOpisType(e1,IntType,c)
        tc2 = self.checkOpisType(e2,BoolType,c)
        tc3 = self.checkOpisType(e3,IntType,c)
        if tc1 == 3: 
            raise TypeCannotBeInferred(ast)
        elif tc1 == 2:
            raise TypeMismatchInStatement(ast)
        elif tc2 == 3:
            raise TypeCannotBeInferred(ast)
        elif tc2 == 2:
            raise TypeMismatchInStatement(ast)
        elif tc3 == 3:   
            raise TypeCannotBeInferred(ast)
        elif tc3 == 2:
            raise TypeMismatchInStatement(ast)
        else:
            forBodyStmt = self.traverseThruStmt(ast.loop[0], ast.loop[1], c)
    
    def visitDowhile(self, ast, c):
        listVardecl = ast.sl[0]
        listStmt = ast.sl[1]
        doWhileBodyStmt = self.traverseThruStmt(listVardecl, listStmt, c)
        e = self.visit(ast.exp,c)
        getFlag = self.checkOpisType(e,BoolType,c)
        if getFlag == 3: 
            raise TypeCannotBeInferred(ast)
        elif getFlag == 2:
            raise TypeMismatchInStatement(ast)
        else:
            pass
    
    def visitWhile(self, ast, c):
        x1 = ast.sl[0]
        x2 = ast.sl[1]
        e = self.visit(ast.exp,c)
        getFlag = self.checkOpisType(e,BoolType,c)
        if getFlag == 3: 
            raise TypeCannotBeInferred(ast)
        elif getFlag == 2:
            raise TypeMismatchInStatement(ast)
        else:
            whileBodyStmt = self.traverseThruStmt(x1, x2, c)

    def visitReturn(self, ast, c): # c[0] = funcName, c[1] = Global Scope
        funcSym = self.findnameinscope(c[0], c[1], lambda x : x.name)
        funcName = funcSym.name
        funcType = funcSym.mtype.restype
        if ast.expr is None:
            if type(funcType) is VoidType:
                pass
            elif type(funcType) is Unknown:
                self.funcInferType(funcSym.name, None, VoidType(), c)
            else:
                raise TypeMismatchInStatement(ast)
        else: # ast.expr is not None
            returnExpr = self.visit(ast.expr,c)
            if type(funcType) is VoidType:
                raise TypeMismatchInStatement(ast)
            if (self.kind(returnExpr) == 'ID'): # returnExpr = id
                if type(returnExpr[1]) is Unknown:
                    if type(funcType) is Unknown:
                        raise TypeCannotBeInferred(ast)
                    else:
                        self.inferAtoBinC(returnExpr[0], funcType)
                else:
                    if type(funcType) is Unknown:
                        self.funcInferType(funcName, None, returnExpr[1], c)
                    else:
                        if type(funcType) is not type(returnExpr[1]):
                            raise TypeMismatchInStatement(ast)
            elif (self.kind(returnExpr) == 'ArrayCell'): # returnExpr = array cell
                if returnExpr[2] == False:
                    raise TypeCannotBeInferred(ast)
                else:
                    if type(returnExpr[1]) is Unknown:
                        if type(funcType) is Unknown:
                            raise TypeCannotBeInferred(ast)
                        else:
                            self.inferAtoBinC(returnExpr[0], funcType)
                    else:
                        if type(funcType) is Unknown:
                            self.funcInferType(funcName, None, returnExpr[1], c)
                        else:
                            if type(funcType) is not type(returnExpr[1]):
                                raise TypeMismatchInStatement(ast)     
            elif (self.kind(returnExpr) == 'N-aryOp'): # return Expr = BinaryOp / UnaryOp               
                if returnExpr[1] == False:
                    raise TypeCannotBeInferred(ast)
                else:
                    if type(funcType) is Unknown:
                        self.funcInferType(funcName, None, returnExpr[0], c)
                    elif type(funcType) is not type(returnExpr[0]):
                        raise TypeMismatchInStatement(ast)
            elif (self.kind(returnExpr) == 'CallExpression'): # return Expr = Call expr
                if returnExpr[2] == False:
                    raise TypeCannotBeInferred(ast)
                else:
                    if type(returnExpr[1]) is Unknown:
                        if type(funcType) is Unknown:
                            raise TypeCannotBeInferred(ast)
                        else:
                            self.funcInferType(returnExpr[0], None, funcType, c)
                    else:
                        if type(funcType) is Unknown:
                            self.funcInferType(funcName, None, returnExpr[1], c)
                        elif type(returnExpr[1]) is not type(funcType):
                            raise TypeMismatchInStatement(ast)
            else: # return expr = literal
                if type(funcType) is Unknown:
                    self.funcInferType(funcName, None, returnExpr, c)
                elif type(funcType) is not type(returnExpr):
                    raise TypeMismatchInStatement(ast)

    def visitCallStmt(self, ast, c):
        funcName = ast.method.name 
        listCallerParameters = [self.visit(x, c) for x in ast.param] # list[Expr]
        callee = self.findnameinscope(funcName, c[1], lambda x: x.name)
        if callee is None:# khong tim thay callee
            raise Undeclared(Function(), funcName)
        elif type(callee.mtype) is not MType:
            raise Undeclared(Function(), funcName)
        else: # tim thay callee
            listCalleeParameters = callee.mtype.intype # = list [Type]
            calleeReturnType = callee.mtype.restype # Type
            if len(listCallerParameters) != len(listCalleeParameters):
                raise TypeMismatchInStatement(ast)
            elif type(calleeReturnType) not in [Unknown, VoidType]:
                raise TypeMismatchInStatement(ast)
            else:
                if type(calleeReturnType) is Unknown:
                    self.funcInferType(funcName, None, VoidType(), c)
                    callee = self.findnameinscope(funcName, c[1], lambda x: x.name)
                    listCalleeParameters = callee.mtype.intype # = list [Type]
                    calleeReturnType = callee.mtype.restype # Type
                # OK, check type cua tung parameter

                
                for i in range(0, len(listCallerParameters)):
                    callerParam = listCallerParameters[i]
                    calleeParam = listCalleeParameters[i]
                    if (self.kind(callerParam) == 'Id'): # CallerParam = Id
                        if type(callerParam[1]) is Unknown:
                            if type(calleeParam) is Unknown:
                                raise TypeCannotBeInferred(ast)
                            elif type(calleeParam) is ArrayType:
                                if type(calleeParam.eletype) is Unknown:
                                    raise TypeCannotBeInferred(ast)
                                else:
                                    self.inferAtoBinC(callerParam[0], calleeParam.eletype, c)
                            else:
                                self.inferAtoBinC(callerParam[0], calleeParam, c)
                        else: # type caller Param != Unknown
                            if type(calleeParam) is not Unknown: # calleeParam co the la ArryType hoac Id non-Unknown type
                                if type(calleeParam) is ArrayType: # calleeParam la mot ArrayType
                                    if type(calleeParam.eletype) is not Unknown:
                                        if type(callerParam[1]) is not type(calleeParam.eletype):
                                            raise TypeMismatchInStatement(ast)
                                    else:
                                        self.funcInferType(funcName, i , callerParam[1], c)
                                elif type(callerParam[1]) is Unknown:
                                    self.funcInferType(funcName, i , callerParam[1], c)
                                    # CalleeParam la Id non-Unknown type
                                elif type(callerParam[1]) is not type(calleeParam):
                                    raise TypeMismatchInStatement(ast)
                    elif (self.kind(callerParam) == 'ArrayCell'): # CallerParam = ArrayCell
                        if callerParam[2] == False:
                            raise TypeCannotBeInferred(ast)
                        else:
                            if type(callerParam[1]) is Unknown: # ArrayCell return type = Unknown
                                if type(calleeParam) is Unknown:
                                    raise TypeCannotBeInferred(ast)
                                elif type(calleeParam) is ArrayType:
                                    if type(calleeParam.eletype) is Unknown:
                                        raise TypeCannotBeInferred(ast)
                                    else:
                                        self.inferAtoBinC(callerParam[0], calleeParam.eletype, c)
                                else:
                                    self.inferAtoBinC(callerParam[0], calleeParam, c)
                            else: # callerParam la mot ArrayCell return type = non Unknown
                                if type(calleeParam) is ArrayType:
                                    if type(calleeParam.eletype) is not Unknown:
                                        if type(callerParam[1]) is not type(calleeParam.eletype):
                                            raise TypeMismatchInStatement(ast)
                                    else:
                                        self.funcInferType(funcName, i, callerParam[1], c)
                                elif type(calleeParam) is Unknown:
                                    self.funcInferType(funcName, i, callerParam[1], c)
                                elif type(callerParam[1]) is not type(calleeParam):
                                    raise TypeMismatchInStatement(ast)
                    elif (self.kind(callerParam) == 'N-aryOp'): # CallerParam = UnaryOp hoặc BinaryOp
                        if callerParam[1] == False:
                            raise TypeCannotBeInferred(ast)
                        else:
                            if type(calleeParam) is Unknown:
                                self.funcInferType(funcName, i, callerParam[0], c)
                            elif type(calleParam) is ArrayType:
                                if type(calleeParam.eleType) is Unknown:
                                    self.funcInferType(funcName, i, callerParam[0], c)
                                elif type(calleeParam.eleType) is not type(callerParam[0]):
                                    raise TypeMismatchInStatement(ast)
                            elif type(callerParam[0]) is not type(calleeParam):
                                raise TypeMismatchInStatement(ast)
                    elif (self.kind(callerParam) == 'CallExpression'): # callerparam = CallExpr = (name, returntype, True)
                        if callerParam[2] == False:
                            raise TypeCannotBeInferred(ast)
                        else:
                            if type(callerParam[1]) is Unknown: # callerparam = CallExpr = (name, Unknown Type, True)
                                if type(calleeParam) is Unknown:
                                    raise TypeCannotBeInferred(ast)
                                elif type(calleeParam) is ArrayType:
                                    if type(callerParam.eletype) is Unknown:
                                        raise TypeCannotBeInferred(ast)
                                    else:
                                        self.funcInferType(callerParam[0], None, calleeParam.eletype, c)
                                else: # callee param is non-unknown type Id
                                    self.funcInferType(callerParam[0], None, calleeParam, c)
                            else: # callerParam return type is non-Unknown type (name, non-Unknown type, True)
                                if type(calleeParam) is ArrayType:
                                    if type(calleeParam.eletype) is Unknown:
                                        self.funcInferType(funcName, i, callerParam[1], c)
                                    elif type(callerParam[1]) is not type(calleeParam.eletype):
                                        raise TypeMismatchInStatement(ast)
                                elif type(calleeParam) is Unknown:
                                    self.funcInferType(funcName, i, callerParam[1], c)
                                elif type(calleeParam) is not type(callerParam[1]):
                                    raise TypeMismatchInStatement(ast)
                    else: # CallerParam = literral
                        if type(calleeParam) is ArrayType:
                            if type(calleeParam.eletype) is Unknown:
                                self.funcInferType(funcName, i, callerParam, c)
                            elif type(calleeParam.eletype) is not type(callerParam):
                                raise TypeMismatchInStatement(ast)
                        elif type(calleeParam) is Unknown:
                            self.funcInferType(funcName, i, callerParam, c)
                        elif type(calleeParam) is not type(callerParam):
                            raise TypeMismatchInStatement()                          
        if type(calleeReturnType) is not VoidType:
            raise TypeMismatchInStatement(ast)
