# -*- coding: utf-8 -*-
# system lib
import os
import sys
import copy
import time
import datetime
import eventlet
import platform

from graphviz import Digraph

# pysmt lib
from pysmt import operators
from pysmt.typing import INT
from pysmt.shortcuts import *

# clang lib
import clang.cindex
from clang.cindex import Index  #主要 API
from clang.cindex import Config  #配置
from clang.cindex import CursorKind  #索引结点的类别
from clang.cindex import TypeKind    #节点的语义类别

if platform.system().lower() == "windows":
    libclangPath = r'./lib/libclang.dll'
elif platform.system().lower() == "linux":
    libclangPath = r'./lib/libclang.so'
else:
    print("ERROR: can't recognize system name")

# init eventlet
eventlet.monkey_patch()

# filename = r"ARMC_sat.c"
# filename = r"Branch_sat.c"
filename = r"Loop_sat.c"
# filename = r"tut1_unsat.c "
# filename = r"tut2_unsat.c"
# filename = r"tut3_unsat.c"
# filename = r"test1_sat.c"
# filename = r"test1_unsat.c"
# filename = r"test2_sat.c"
# filename = r"test2_unsat.c"

########################
##  Golbal Variables  ##
########################
directory = r"./TestFiles/"     # 测试文件路径

AST_root_node = None            # AST根节点
varsPool = []                   # 文本类型变量池
TransList = dict()              # 转移字典
StateList = dict()              # 状态字典

Z3AllVars = dict()              # Z3变量池
VrasDict = dict()               # Z3变量字典

g = Digraph(name='CFA', comment="comment", format='png')    # 图对象

########################
##      Utilities     ##
########################
# P -> Q  ::=    P(X) <= Q(X)
def entailed(P, Q):
    res = is_sat(And(P, Not(Q)), solver_name="z3")
    return not res

#if inequal1->inequal2,delete inequal2      
def del_redundant(inequals):
    l=len(inequals)
    del_index=[]
    for i in range(l):
        for j in range(i+1,l):
            if entailed(inequals[i],inequals[j]):
                del_index.append(j)
                continue
            if entailed(inequals[j],inequals[i]):
                del_index.append(i)
    for i in del_index:
        del inequals[i]

#move an item to left, the others to right
def move_item(var, formula):
    create_node = get_env().formula_manager.create_node
    lFormula, rFormula = formula.args()
    # 判断变量在左边还是在右边
    VarInLeft = True if var in lFormula.get_free_variables() else False
    if VarInLeft:   # 变量在左边怎么办
        lsub = lFormula.args()
        IsNull = True if len(lsub) == 0 else False
        if IsNull:  # 左子树没有叶子，只有这个变量
            return formula
        else:       # 变量在左子树里面，还需要继续寻找
            op = lFormula.node_type()
            if op == operators.PLUS:
                op = operators.MINUS
                VarInLLeft = True if var in lsub[0].get_free_variables() else False 
                if VarInLLeft:  # 确定在左子树的左树上
                    r1 = create_node(node_type=op, args=(rFormula, lsub[1]))
                    r2 = create_node(node_type=formula.node_type(), args=(lsub[0], r1))
                    return move_item(var, r2)
                else:           # 确定在左子树的右树上
                    r1 = create_node(node_type=op, args=(rFormula, lsub[0]))
                    r2 = create_node(node_type=formula.node_type(), args=(lsub[1], r1))
                    return move_item(var, r2)
            elif op == operators.MINUS:
                VarInLLeft = True if var in lsub[0].get_free_variables() else False 
                if VarInLLeft:  # 确定在左子树的左树上
                    r1 = create_node(node_type=PLUS, args=(rFormula, lsub[1]))
                    r2 = create_node(node_type=formula.node_type(), args=(lsub[0], r1))
                    return move_item(var, r2)
                else:
                    r1 = create_node(node_type=PLUS, args=(rFormula, lsub[1]))
                    r2 = create_node(node_type=formula.node_type(), args=(lsub[0], r1))
                    return move_item(var, r2)
            elif op == operators.TIMES:
                return formula
    else:           # 变量在右边怎么办
        rsub = rFormula.args()
        IsNull = True if len(rsub) == 0 else False
        if IsNull:   # 右子树没有叶子，只有这个变量
            if formula.node_type() == operators.EQUALS:
                return create_node(node_type=operators.EQUALS, args=(rFormula, lFormula))
            else:
                return formula
        else:
            op = rFormula.node_type()
            if op == operators.PLUS:
                op = operators.MINUS
                VARInRLeft = True if var in rsub[0].get_free_variables() else False
                if VARInRLeft:
                    r1 = create_node(node_type=op, args=(lFormula, rsub[1]))
                    r2 = create_node(node_type=formula.node_type(), args=(r1, rsub[0]))
                    return move_item(var, r2)
                else:
                    r1 = create_node(node_type=op, args=(lFormula, rsub[0]))
                    r2 = create_node(node_type=formula.node_type(), args=(r1, rsub[1]))
                    return move_item(var, r2)
            elif op == operators.MINUS:
                VARInRLeft = True if var in rsub[0].get_free_variables() else False
                if VARInRLeft:
                    r1 = create_node(node_type=PLUS, args=(lFormula, rsub[1]))
                    r2 = create_node(node_type=formula.node_type(), args=(r1, rsub[1]))
                    return move_item(var, r2)
                else:
                    r1 = create_node(node_type=PLUS, args=(lFormula, rsub[1]))
                    r2 = create_node(node_type=formula.node_type(), args=(r1, rsub[0]))
                    return move_item(var, r2)
            elif op == operators.TIMES:
                return operators.formula

#eliminate a variables from a set of formulas
def eliminate_one(var, formulas):
    #search if ther is  anequation in expressions including var
    for formula in formulas:
        if formula.node_type() != operators.EQUALS:   # 只要等式，非等式跳过
            continue
        vs = formula.get_free_variables()
        if var not in vs:           # 某个等式存在删除变量，下一步，否则过滤掉
            continue

        #find the one
        formulas.remove(formula)
        formula=move_item(var, formula)
        for j in range(len(formulas)):
            vs=formulas[j].get_free_variables()
            if var not in vs:
                continue
            formulas[j] = formulas[j].substitute({var : formula.arg(1)}).simplify()
        return

    #not a equation including var
    choose=[]
    for formula in formulas:
        vs=formula.get_free_variables()
        if var not in vs:
            continue
        choose.append(formula)  # choose保存了含有var的不等式

    for j in range(len(choose)):    # 剔除formulas中所有包含var变量的不等式
        formulas.remove(choose[j]) 
        choose[j]=move_item(var, choose[j]) # 转化choose不等式

    for j in range(len(choose)):             
        for i in range(j+1,len(choose)):
            if choose[i].arg(1) ==var and choose[j].arg(0) == var:
                if choose[i].node_type() == LT and choose[j].node_type == LT:
                    formula.append(LT(choose[i].arg(0), choose[j].arg(1)))
                else:
                    formula.append(LE(choose[i].arg(0), choose[j].arg(1)))

#[test] eliminate_one(x,[x>y,x<z,x<pc])

# 返回替换对
def getSubtiPairList(VrasDict, NewType = -1, DeleteType = 0):
    # _x : New x : Delete x_ : 

    Pair = dict()
    if NewType == 0 and DeleteType == 1:
        for VarName, VarDict in VrasDict.items():
            Pair[VarDict[VarName]] = VarDict[VarName + "_"]
        return Pair
    if NewType == 1 and DeleteType == -1:
        for VarName, VarDict in VrasDict.items():
            Pair[VarDict[VarName + "_"]] = VarDict["_" + VarName]
        return Pair
    if NewType == 0 and DeleteType == -1:
        for VarName, VarDict in VrasDict.items():
            Pair[VarDict[VarName]] = VarDict["_" + VarName]
        return Pair
    if NewType == 1 and DeleteType == 0:
        for VarName, VarDict in VrasDict.items():
            Pair[VarDict[VarName + "_"]] = VarDict[VarName]
        return Pair

# variables in p1 is eq to variables in p2
def eqVariables(p1, p2):
    vars1 = getVars(p1)
    vars2 = getVars(p2)
    if [set(vars1)] == [set(vars2)]:
        return True
    else:
        return False

# True 表示有交集 False 表示没有交集
def isIntersection(phi1, phi2):
    f = []
    for p in phi1 + phi2:
        if p == True:
            return False
        if p == False:
            return True
        f.append(p)
    res = is_sat(And(f), solver_name="z3")
    if res:
        return True
    else:
        return False
    pass

# 自己定义了一个判断字符串是否为整型数字的方法；python自带的判断字符串是否为数字的方法isdigit()好像不能判断负数，
# 比如isdigit()认为“-11”不是数字。
def isDigit(x):
    x = x.strip()
    if len(x) > 0 and x[0] == "-":
        x = x[1:]
    return x.isdigit()

# ['x', '>', '1'] return (x>1)
# ['x', '=', '1'] return (x==1)
def list_2_z3Formula(formula):
    opLoc = -1
    z3Str = ""
    z3Expr = None
    for index in range(len(formula)):
        if isDigit(formula[index]):
            formula[index] = 'Int(' + formula[index] + ")"
        if formula[index] in ['>', '>=', '<', '<=', '==', '!=', '=']:
            opLoc = index
    if formula[opLoc] in ['=', '==']:
        z3Str = "Equals({left}, {right})".format(left="".join(formula[:opLoc]), right="".join(formula[opLoc+1:]))
    if formula[opLoc] == "!=":
        z3Str = "NotEquals({left}, {right})".format(left="".join(formula[:opLoc]), right="".join(formula[opLoc+1:]))
    if formula[opLoc] == ">":
        z3Str = "GT({left}, {right})".format(left="".join(formula[:opLoc]), right="".join(formula[opLoc+1:]))
        return GT("".join(formula[:opLoc]), "".join(formula[opLoc+1:]))
    if formula[opLoc] == ">=":
        z3Str = "GE({left}, {right})".format(left="".join(formula[:opLoc]), right="".join(formula[opLoc+1:]))
    if formula[opLoc] == "<":
        z3Str = "LT({left}, {right})".format(left="".join(formula[:opLoc]), right="".join(formula[opLoc+1:]))
    if formula[opLoc] == "<=":
        z3Str = "LE({left}, {right})".format(left="".join(formula[:opLoc]), right="".join(formula[opLoc+1:]))
    z3Expr = eval(z3Str)
    return z3Expr

########################
##       Parsing      ##
########################


# 配置lib,参数是传入libclang.dll路径
def configLibClang(libclangPath):
    #这个路径需要自己先在笔记本上安装	
    if Config.loaded == True:
        print("Config.loaded == True:")
        #pass
    else:
        Config.set_library_file(libclangPath)
        print("install path")

# 生成AST根节点,参数是 *.c file
def getRootNode(filename = filename):
    index = Index.create() # 创建AST索引
    print(directory,filename)
    tu = index.parse(directory + filename)  # tu:=TranslationUnit
    AST_root_node= tu.cursor  #cursor根节点
    if AST_root_node is not None:
        print("file: " + filename + " parse succeed")    # 有输出表示读取文件成功
    else:
        print("Error! file"+ filename + "parse error")
        exit(0)
    return AST_root_node

# 前序遍历函数 cursor is root node
def preorder_travers_AST(cursor):
    for cur in cursor.get_children():
        if cur.kind == CursorKind.FUNCTION_DECL:
            parseFunctionDecl(cur)
        preorder_travers_AST(cur)

class StateNode(object):
    id = 0 # static class variable
    '''
    每个结点有名字，有唯一ID，有自己的公式，公式如果是逻辑判断，changed就是不改变。
    changed是记录变量被修改，下次转化时候方便一些
    '''
    def __init__(self, line, formula):
        self.line = line
        self.ID = self.getID()
        self.formula = formula          # ['x', '>', '1']
        self.z3Formula = []
        self.name = self.getName()      # line : formula
        self.relatedRhoIDs = []         # [0,1] TransNode.ID
        self.toStateIDs = []            # [1,2] StateNode.ID
        self.fromStateIDs = []          # [3,4] Statenode.ID
        self.vars = []
        StateNode.id += 1
    
    def getID(self):
        if self.line == "-2":
            StateNode.id -= 1
            return -2
        elif self.line == "-1":
            StateNode.id -= 1
            return -1
        else:
            return StateNode.id

    def getName(self):
        name = self.line + ":" + "".join(self.formula)
        return name
    
    def initZ3Formula(self): # 考虑sat
        selfFormula = copy.copy(self.formula)
        if len(selfFormula) == 1:
            formulas = [["pc", "=", self.line]]
        else:
            formulas = [selfFormula] + [["pc", "=", self.line]]
        for formula in formulas:
            self.z3Formula.append(list_2_z3Formula(formula))
            

class TransNode(object):
    id = 0
    def __init__(self, fromStateID, toStateID, reversed=False):
        self.ID = TransNode.id
        self.reversed = reversed
        self.fromStateID = fromStateID
        self.toStateID = toStateID
        self.formulas = None
        self.z3Formulas = []
        self.name = ""
        TransNode.id += 1

    def initFormulas(self):
        f1 = copy.copy(StateList[self.fromStateID].formula)
        f2 = unChanged(StateList[self.fromStateID].vars)
        unChangedStr = "{" + ",".join(StateList[self.fromStateID].vars) + "}"
        if self.reversed:
            self.formulas = [reversedFormula(f1)] + f2
            self.name = str(self.ID)+":"+"".join(f1)+unChangedStr
        else:
            if f1[1] in ['>', ">=", '<', '<=', '==', '!=']:
                self.formulas = [f1] + f2
                self.name = str(self.ID)+":"+"".join(f1)+unChangedStr
            else:
                f1[0] = f1[0] + "_"
                self.formulas = [f1] + f2
                self.name = str(self.ID)+":"+"".join(f1)+unChangedStr

    def initZ3Formulas(self):
        selfFormulas = copy.copy(self.formulas)
        formulas = selfFormulas + [["pc", "=", StateList[self.fromStateID].line], ["pc_", "=", StateList[self.toStateID].line]]
        for formula in formulas:
            self.z3Formulas.append(list_2_z3Formula(formula))

# 解析Function
def parseFunctionDecl(FunctionDecl):
    for FunctionCompound in FunctionDecl.get_children():
        traversFuncCompoundStmt(FunctionCompound)
    pass

# Compound结点
def traversFuncCompoundStmt(CompoundStmt):
    StmtIDs = []    # 缓存池
    ThenEndIDs = [] # If.Then返回结点
    ElseEndIDs = [] # If.Else返回结点

    for node in CompoundStmt.get_children():
        if node.kind == CursorKind.IF_STMT: # if statement
            stateID, ThenEndIDs_, ElseEndIDs_ = traversIfStmt(node)

            # 承上 1 连接点 2 完善转移
            # 启下 生成一个不完整的转移
            if len(ThenEndIDs + ElseEndIDs) > 0:
                for ID in ThenEndIDs + ElseEndIDs:
                    StateList[ID].toStateIDs.append(stateID)
                    TransList[StateList[ID].relatedRhoIDs[-1]].toStateID = stateID
                ThenEndIDs = ThenEndIDs_
                ElseEndIDs = ElseEndIDs_

            if len(StmtIDs) > 0 :
                StateList[StmtIDs[-1]].toStateIDs.append(stateID)
                TransList[StateList[StmtIDs[-1]].relatedRhoIDs[-1]].toStateID = StmtIDs[-1]

        if node.kind == CursorKind.WHILE_STMT or node.kind == CursorKind.DECL_STMT or node.kind == CursorKind.BINARY_OPERATOR or node.kind == CursorKind.CALL_EXPR: 
            if node.kind == CursorKind.WHILE_STMT:
                stateID = traversWhileStmt(node)
            if node.kind == CursorKind.DECL_STMT:
                stateID = parseDeclStmt(node)
            if node.kind == CursorKind.BINARY_OPERATOR:
                stateID = parseEvaluationStmt(node)
            if node.kind == CursorKind.CALL_EXPR and node.spelling == "sassert":
                stateID = parseAssertStmt(node)

            if len(ThenEndIDs + ElseEndIDs) > 0:
                for ID in ThenEndIDs + ElseEndIDs:
                    StateList[ID].toStateIDs.append(stateID)
                    TransList[StateList[ID].relatedRhoIDs[-1]].toStateID = stateID
                ThenEndIDs = []
                ElseEndIDs = []

            if len(StmtIDs) > 0 :
                StateList[StmtIDs[-1]].toStateIDs.append(stateID)
                TransList[StateList[StmtIDs[-1]].relatedRhoIDs[-1]].toStateID = stateID

            StmtIDs.append(stateID)

        if node.kind == CursorKind.RETURN_STMT:
            return

# IfStmt结点
def traversIfStmt(IfStmt):
    condStateID = None
    ThenEndIDs = []
    ElseEndIDs = []
    CompoundStmts = []
    for node in IfStmt.get_children():
        if node.kind == CursorKind.BINARY_OPERATOR: # if condition
            stateID = parseCondtionStmt(node)
        if node.kind == CursorKind.COMPOUND_STMT:   # if body and else body
            CompoundStmts.append(node)
    if len(CompoundStmts) != 2:
        print("Error: Code not formalized! IF-Then-Else")
        return
    ThenEndIDs = traversIfCompound(CompoundStmts[0], stateID)
    ElseEndIDs = traversIfCompound(CompoundStmts[1], stateID, True)

    return stateID, ThenEndIDs, ElseEndIDs

# IfStmt结点 Then块和Else块都是一样的
def traversIfCompound(CompoundStmt, condStateID, reversed=False):
    StmtIDs = []
    ThenEndIDs = []
    ElseEndIDs = []

    for node in CompoundStmt.get_children():
        if node.kind == CursorKind.IF_STMT:
            # if 内的if 必有头节点(if.conditon)
            stateID, ThenEndIDs_, ElseEndIDs_ = traversIfStmt(node)

            if len(ThenEndIDs + ElseEndIDs) > 0:
                for ID in ThenEndIDs + ElseEndIDs:
                    StateList[ID].toStateIDs.append(stateID)
                    TransList[StateList[ID].relatedRhoIDs[-1]].toStateID = stateID
                ThenEndIDs = ThenEndIDs_
                ElseEndIDs = ElseEndIDs_ 
            else:
                if len(StmtIDs) > 0 :
                    StateList[StmtIDs[-1]].toStateIDs.append(stateID)
                    TransList[StateList[StmtIDs[-1]].relatedRhoIDs[-1]].toStateID = stateID
                else:
                    StateList[condStateID].toStateIDs.append(stateID)
                    # 创建第二条转移
                    trans = TransNode(condStateID, 0, reversed)
                    TransList[trans.ID] = copy.copy(trans)
                    StateList[condStateID].relatedRhoIDs.append(trans.ID)

        # decl, assignment,callexpr, assert
        if node.kind == CursorKind.DECL_STMT or node.kind == CursorKind.BINARY_OPERATOR or node.kind == CursorKind.WHILE_STMT or node.kind == CursorKind.CALL_EXPR:
            stateID = 0
            if node.kind == CursorKind.DECL_STMT:
                stateID = parseDeclStmt(node)
            if node.kind == CursorKind.BINARY_OPERATOR:
                stateID = parseEvaluationStmt(node)
            if node.kind == CursorKind.WHILE_STMT:
                stateID = traversWhileStmt(node)
            if node.kind == CursorKind.CALL_EXPR and node.spelling == "sassert":
                stateID = parseAssertStmt(node)

            if len(ThenEndIDs + ElseEndIDs) > 0:
                for ID in ThenEndIDs + ElseEndIDs:
                    StateList[ID].toStateIDs.append(stateID)
                    TransList[StateList[ID].relatedRhoIDs[-1]].toStateID = stateID
                ThenEndIDs = []
                ElseEndIDs = []
            else:
                if len(StmtIDs) > 0 :
                    StateList[StmtIDs[-1]].toStateIDs.append(stateID)
                    TransList[StateList[StmtIDs[-1]].relatedRhoIDs[-1]].toStateID = stateID
                else:   # 只考虑if.condition
                    StateList[condStateID].toStateIDs.append(stateID)

                    trans = TransNode(condStateID, stateID, reversed)
                    TransList[trans.ID] = copy.copy(trans)
                    StateList[condStateID].relatedRhoIDs.append(trans.ID)

            StmtIDs.append(stateID)
       
        if node.kind == CursorKind.RETURN_STMT:
            return

    # 先检查时候又if.ends结点，再判断是否又缓存
    if len(ThenEndIDs + ElseEndIDs) > 0:
        return ThenEndIDs + ElseEndIDs
    else:
        if len(StmtIDs) > 0:
            return [StmtIDs[-1]]
        else:
            return [condStateID]

# WhileStmt结点
def traversWhileStmt(WhileStmt):
    stateID = None
    for node in WhileStmt.get_children():
        if node.kind == CursorKind.BINARY_OPERATOR:
            stateID = parseCondtionStmt(node)
        if node.kind == CursorKind.COMPOUND_STMT:
            traversWhileBody(node, stateID)

    trans = TransNode(stateID, 0, True) # 生成condition的第二条转移
    TransList[trans.ID] = copy.copy(trans)
    StateList[stateID].relatedRhoIDs.append(trans.ID)
    return stateID

#WhileBody块
def traversWhileBody(CompoundStmt, condStateID):
    StmtIDs = []
    ThenEndIDs = []
    ElseEndIDs = []
    stateID = None
    for node in CompoundStmt.get_children():
        if node.kind == CursorKind.IF_STMT:
            stateID, ThenEndIDs_, ElseEndIDs_ = traversIfStmt(node)

            if len(ThenEndIDs + ElseEndIDs) > 0:
                for ID in ThenEndIDs + ElseEndIDs:
                    StateList[ID].toStateIDs.append(stateID)
                    TransList[StateList[ID].relatedRhoIDs[-1]].toStateID = stateID
                ThenEndIDs = ThenEndIDs_
                ElseEndIDs = ElseEndIDs_
            else:    
                if len(StmtIDs) > 0 :
                    StateList[StmtIDs[-1]].toStateIDs.append(stateID)
                    TransList[StateList[StmtIDs[-1]].relatedRhoIDs[-1]].toStateID = stateID
                else:
                    StateList[condStateID].toStateIDs.append(stateID)
                    TransList[StateList[condStateID].relatedRhoIDs[-1]].toStateID = stateID

        # decl, assignment,callexpr, assert
        if node.kind == CursorKind.DECL_STMT or node.kind == CursorKind.BINARY_OPERATOR or node.kind == CursorKind.WHILE_STMT or node.kind == CursorKind.CALL_EXPR:
            stateID = 0
            if node.kind == CursorKind.DECL_STMT:
                stateID = parseDeclStmt(node)
            if node.kind == CursorKind.BINARY_OPERATOR:
                stateID = parseEvaluationStmt(node)
            if node.kind == CursorKind.WHILE_STMT:
                stateID = traversWhileStmt(node)
            if node.kind == CursorKind.CALL_EXPR and node.spelling == "sassert":
                stateID = parseAssertStmt(node)

            if len(ThenEndIDs + ElseEndIDs) > 0:
                for ID in ThenEndIDs + ElseEndIDs:
                    StateList[ID].toStateIDs.append(stateID)
                    TransList[StateList[ID].relatedRhoIDs[-1]].toStateID = stateID
                ThenEndIDs = []
                ElseEndIDs = []
            else:
                if len(StmtIDs) > 0 :
                    StateList[StmtIDs[-1]].toStateIDs.append(stateID)
                    TransList[StateList[StmtIDs[-1]].relatedRhoIDs[-1]].toStateID = stateID
                else:
                    StateList[condStateID].toStateIDs.append(stateID)
                    TransList[StateList[condStateID].relatedRhoIDs[-1]].toStateID = stateID

            StmtIDs.append(stateID)

        if node.kind == CursorKind.RETURN_STMT:
            return

    # 在结束位置处，回接while.condition
    if len(ThenEndIDs + ElseEndIDs) > 0:
        for ID in ThenEndIDs + ElseEndIDs:
            StateList[ID].toStateIDs.append(condStateID)
            TransList[StateList[ID].relatedRhoIDs[-1]].toStateID = condStateID
    else:
        if len(StmtIDs) > 0:
            StateList[StmtIDs[-1]].toStateIDs.append(condStateID)
            TransList[StateList[StmtIDs[-1]].relatedRhoIDs[-1]].toStateID = condStateID
        else:
            print("dead loop")  #while(){} 死循环
            sys.exit(0)

####################
#    Parse Node    #
####################
# 赋值
def parseEvaluationStmt(BinaryOperator):
    line, formula = parseOperator2Formula(BinaryOperator)
    state = StateNode(line = line, formula = formula)
    state.vars = [var for var in varsPool if formula[0] != var]
    StateList[state.ID] = copy.copy(state)

    trans = TransNode(state.ID, 0)  # 创建转移
    TransList[trans.ID] = copy.copy(trans)  # 添加到转移栈中
    StateList[state.ID].relatedRhoIDs.append(trans.ID)  # 连接到状态上
    return state.ID

# 声明
def parseDeclStmt(DeclStmt):
    line, formula = parseDecl2Formula(DeclStmt)
    state = StateNode(line = line, formula = formula)
    state.vars = copy.copy(varsPool[:-1])
    StateList[state.ID] = copy.copy(state)

    trans = TransNode(state.ID, 0)  # 创建转移
    TransList[trans.ID] = copy.copy(trans)  # 添加到转移栈中
    StateList[state.ID].relatedRhoIDs.append(trans.ID)  # 连接到状态上
    return state.ID

# 条件 If和While中的判断条件
def parseCondtionStmt(BinaryOperator):
    line, formula = parseOperator2Formula(BinaryOperator)
    state = StateNode(line = line, formula = formula)
    state.vars = copy.copy(varsPool)
    StateList[state.ID] = copy.copy(state)

    trans = TransNode(state.ID, 0)  # 创建转移
    TransList[trans.ID] = copy.copy(trans)  # 添加到转移栈中
    StateList[state.ID].relatedRhoIDs.append(trans.ID)  # 连接到状态上
    return state.ID

# Return 
def getReturnNode(formula = "End", line = '0'):
    state = StateNode(line = line, formula = formula)
    StateList[state.ID] = copy.copy(state)
    return state.ID

###################
#    Parse AST    #
###################
# x > 3
def parseOperator2Formula(BinaryOperator):
    tokens = []
    for tk in BinaryOperator.get_tokens():
        tokens.append(tk.spelling)
    line = str(BinaryOperator.location.line)
    return line, tokens

# int a = 3;
def parseDecl2Formula(DeclStmt):
    tokens = []
    for tk in DeclStmt.get_tokens():
        tokens.append(tk.spelling)
    # 声明语句 把新变量添加到变量池中
    if tokens[1] not in varsPool:
        varsPool.append(tokens[1])
    # 赋初值
    if len(tokens) == 3: # int a ; 3个
        if tokens[0] == "int" or tokens[0] == "char":
            tokens.insert(2, "0")
        if tokens[0] == "float" or tokens[0] == "double":
            tokens.insert(2, "0.0")
        tokens.insert(2, "=")
    line = str(DeclStmt.location.line)
    return line, tokens[1:-1]

# sassert(x>3)
def parseAssertStmt(AssertStmt):
    tokens = []
    for tk in AssertStmt.get_tokens():
        tokens.append(tk.spelling)
    
    formula = tokens[2:-1]
    line = str(AssertStmt.location.line)
    
    state = StateNode(line = line, formula = formula)
    state.vars = copy.copy(varsPool)
    StateList[state.ID] = copy.copy(state)

    # 生成SAT和UNSAT结点
    sat = StateNode(line = "-1", formula = ["sat"])
    unsat = StateNode(line = "-2", formula = reversedFormula(formula))
    StateList[sat.ID] = copy.copy(sat)
    StateList[unsat.ID] = copy.copy(unsat)
    # 状态连接
    StateList[state.ID].toStateIDs.append(sat.ID)
    StateList[state.ID].toStateIDs.append(unsat.ID)

    satTrans = TransNode(state.ID, sat.ID)
    unsatTrans = TransNode(state.ID, unsat.ID, True)
    TransList[satTrans.ID] = copy.copy(satTrans)
    TransList[unsatTrans.ID] = copy.copy(unsatTrans)
    StateList[state.ID].relatedRhoIDs=[satTrans.ID, unsatTrans.ID]

    return state.ID

# formula=['x', '>', '1']，反转
# 字符反转，方便之后操作
def reversedFormula(formula):
    if formula[1] == "<":
        formula[1] = ">="
    elif formula[1] == "<=":
        formula[1] = ">"
    elif formula[1] == ">":
        formula[1] = "<="
    elif formula[1] == ">=":
        formula[1] = "<"
    elif formula[1] == "==":
        formula[1] = "!="
    elif formula[1] == "!=":
        formula[1] = "=="
    return formula

# [x,y] return [[x_, =, x], [y_, =, y]]  
def unChanged(vars = []):
    return [[var + "_", "=", var]for var in vars]

def InitializedCFG(filename):
    configLibClang(libclangPath)
    AST_root_node = getRootNode(filename)
    starttime = datetime.datetime.now()
    preorder_travers_AST(AST_root_node)

    # Symbol 会调用符号管理
    # 动态生成所有变量的z3变量
    for var in varsPool + ["pc"]:
        exec('globals()["{var}_"] = Symbol("{var}_", INT)'.format(var=var))
        exec('globals()["{var}"]  =  Symbol("{var}", INT)'.format(var=var))
        exec('globals()["_{var}"] = Symbol("_{var}", INT)'.format(var=var))
        exec('Z3AllVars["{var}_"]= {var}_'.format(var=var))
        exec('Z3AllVars["{var}"] =  {var}'.format(var=var))
        exec('Z3AllVars["_{var}"]= _{var}'.format(var=var))
    # 生成变量字典，将来生成替换对
    for var in varsPool + ["pc"]:
        VrasDict[var] = {var + "_" : Z3AllVars[var + "_"], var : Z3AllVars[var], "_" + var : Z3AllVars["_" + var]}
    # 1 遍历状态栈，生成cfa图
    # 2 生成转移
    for ID, state in StateList.items():
        g.node(name=state.line, label=state.name)
        state.initZ3Formula()
        for transID in state.relatedRhoIDs:
            TransList[transID].initFormulas()
            TransList[transID].initZ3Formulas()
            StateList[TransList[transID].toStateID].fromStateIDs.append(ID)
    for ID, trans in TransList.items():
        g.edge(StateList[trans.fromStateID].line, StateList[trans.toStateID].line, trans.name)

    Preds = [Equals(Z3AllVars["pc"], Int(int(state.line))) for ID, state in StateList.items()]

    print("Initialized CFG!")
    print("Vars' Count:\t", len(VrasDict), "\tTransitions Count:\t", len(TransList))
    print("All Vars and Vars' dict form")
    print(VrasDict)
    print("ALL StateList")
    for ID, node in StateList.items():
        print("id:",ID, "line:", node.line, "formula:", node.z3Formula,"from id:", node.fromStateIDs, " to id:", node.toStateIDs, " vars:", node.vars)
    print("ALL TransList")
    for transID, trans in TransList.items():
        print("id:", transID, " From:", StateList[trans.fromStateID].line," To:", StateList[trans.toStateID].line," formula:", trans.z3Formulas)
    print("Preds")
    print(Preds)


    endtime = datetime.datetime.now()
    print("ParseT:\t", endtime - starttime)
    g.render(filename=filename[0:-2] + '.gv', directory=r'./CFA')
    
    return VrasDict, Z3AllVars, Preds, TransList, StateList


########################
##      Verificator   ##
########################
# Preds 全局变量
VarsDict, ALL_VARS, Preds, TransList, StateList = InitializedCFG(sys.argv[1])
initID  = 0
errID   = -2
TrueConstant = TRUE()
FalseConstant = FALSE()
starttime = None
endtime = None


# subtitute pairs
# -1 -- v" 0 -- v 1 -- v'
sub1 = getSubtiPairList(VarsDict, 0, 1)    # [V'/V]    inter
sub2 = getSubtiPairList(VarsDict, 1, -1)   # [V"/V']   connect1
sub3 = getSubtiPairList(VarsDict, 0, -1)   # [V"/V]    post1 connect2
sub4 = getSubtiPairList(VarsDict, 1, 0)    # [V/V']    post2

'''
# Test Subtitute
print("Sub Pairs")
print("[V'/V]", end=" ")
print(sub1)      # [V'/V]
print("[V\"/V']", end=" ")
print(sub2)      # [V"/V']
print("[V\"/V]", end=" ")
print(sub3)      # [V"/V]
print("[V/V']", end=" ")
print(sub4)      # [V/V']
'''

########################
##       ARTNode      ##
########################
class ARTNode(object):
    id = 0
    def __init__(self, stateID, z3Formula):
        self.ID= ARTNode.id
        self.stateID = stateID  # related state id in Statelist
        self.fromArtID = -10
        self.toArtIDs = []
        self.z3Formula = z3Formula
        self.label = False
        ARTNode.id += 1

ArtList = dict()

########################
##     Termination    ##
########################

# relational composition ρ o ρ
def connect_trans(rho1, rho2):
    if FalseConstant in rho1 + rho2:
        print("Error! False in formula rho1 or rho2")
        print("program is correct")
        endtime = datetime.datetime.now()
        print("VerifyT:\t",endtime - starttime)
        sys.exit(0)

    # substitute variables
    # rho1(z3Formula) :-> rho1(Transition)
    rho1 = [substitute(p, sub2) for p in rho1]  # [V"/V']
    rho2 = [substitute(p, sub3) for p in rho2]  # [V"/V]
 
    rho1=list(set(rho1+rho2))
    for VName, VZ3 in ALL_VARS.items():
        if VName.startswith("_"):
            eliminate_one(VZ3, rho1)
    if FalseConstant in rho1:
        print("False in result of rho1 o rho2")
        print("program is correct")
        endtime = datetime.datetime.now()
        print("VerifyT:\t",endtime - starttime)
        sys.exit(0)
    return rho1

########################
##       Safety       ##
########################

# post condition Function
def post(phi, rho):
    if phi is None:
        print("Error！phi is None in post-condition function")
        sys.exit(0)
    
    # backup formula
    phi = copy.copy(phi)
    rho = copy.copy(rho)
    
    # post 函数只做变量替换和表达式合并
    # 如果 phi中有True 就做直接转换
    if TrueConstant in phi:
        rho = [substitute(p, sub3) for p in rho]    # [V"/V]
        rho = [substitute(p, sub4) for p in rho]    # [V/V']        
       
        for VName, VZ3 in ALL_VARS.items():
            if "_" in VName:
                eliminate_one(VZ3, rho)
        return rho
    # 如果有False就返回Phi 
    if FalseConstant in phi:
        return phi

    # phi只能沿着该状态的可能出发路线移动
    # 如果点和边不对应就返回None
    phi = [substitute(p, sub3) for p in phi]    # [V"/V]
    rho = [substitute(p, sub3) for p in rho]    # [V"/V]
    rho = [substitute(p, sub4) for p in rho]    # [V/V']

    result=list(set(phi + rho))
    for VName, VZ3 in ALL_VARS.items():
        if "_" in VName:
            eliminate_one(VZ3, result)

    return result

# α function
def alpha(phi):
    if phi is None:
        return None
        
    result = []

    for p in Preds: # This is an error !!!
        if entailed(And(phi), p):
            result.append(p)
    # 这里感觉一定会有一个结果
    if len(result) == 0:
        result = [FalseConstant]

    return result

# post condition supset
def postSharp(phi, rho):
    return alpha(post(phi, rho))

# AbstractReach Function
def AbstractReach():
    artHead = ARTNode(initID, alpha(StateList[initID].z3Formula))
    ArtList[artHead.ID] = artHead
    WorkList = [artHead.ID]

    while len(WorkList) > 0:
        ArtID = WorkList[-1] # choose the last one state id from WorkList
        del WorkList[-1]
        for transID in StateList[ArtList[ArtID].stateID].relatedRhoIDs: #抽象状态->状态栈->相关转移
            phi_ = postSharp(ArtList[ArtID].z3Formula, TransList[transID].z3Formulas)
            print("phi_", phi_)
            flag = True

            for ArtID_, artState in ArtList.items():
                if entailed(And(phi_), And(artState.z3Formula)):
                    # label node
                    tmpArtState = ARTNode(artState.stateID, phi_)
                    tmpArtState.label = True
                    tmpArtState.fromArtID = ArtID
                    ArtList[tmpArtState.ID] = copy.copy(tmpArtState)    # 加入ART栈
                    ArtList[ArtID].toArtIDs.append(tmpArtState.ID)
                    flag = False
                    break
                
            if flag: # phi_ 对于ART中所有的ArtState 都不能蕴含
                tmpArtState = ARTNode(TransList[transID].toStateID, phi_)
                tmpArtState.fromArtID = ArtID
                ArtList[tmpArtState.ID] = copy.copy(tmpArtState)    #加入ART栈
                ArtList[ArtID].toArtIDs.append(tmpArtState.ID)
                WorkList.append(tmpArtState.ID)    # 临时池

    Path = []   # a set of transition id
    print("Abstract Reachability Tree Stack")
    for ArtID, artState in ArtList.items():
        print("artId:",ArtID," stateID:", artState.stateID, " fromArt", artState.fromArtID, " to", artState.toArtIDs," formula:", artState.z3Formula," label:",artState.label)

# CEID is ArtID
def MakePath(CEID):
    Path = []
    tmpID = CEID
    # 1 判断上一结点是否
    while ArtList[tmpID].fromArtID != -10 :
        fromArtID = ArtList[tmpID].fromArtID
        relatedRhoIDs = StateList[ArtList[fromArtID].stateID].relatedRhoIDs
        for transID in relatedRhoIDs:
            if TransList[transID].toStateID == ArtList[tmpID].stateID:
                Path.append(transID)
        tmpID = ArtList[tmpID].fromArtID
    return list(reversed(Path))

# Feasible Path Function, Counterexample Path(CEP)
def FeasiblePath(CEP):
    tmpPhi = copy.copy(StateList[initID].z3Formula)    #备份Phi_int
    for transID in CEP:
        tmpState = post(tmpPhi,TransList[transID].z3Formulas)
    res = is_sat(And(tmpPhi + StateList[errID].z3Formula), solver_name="z3")
    return res

# Refine Path Function
def RefinePath(CEP):
    # 计算插值过程不需要进行过滤检查，因为状态和转移关系一定是正确的

    phi_err = copy.copy(StateList[errID].z3Formula)
    phi_err = [substitute(p, sub1) for p in phi_err]    # [V'/V]
    
    inter = TrueConstant

    Result = []
    for i in range(len(CEP)):
        if i == 0:
            phi1 = StateList[initID].z3Formula
        else:
            phi1 = post([inter], TransList[CEP[i - 1]].z3Formulas)
        
        tmpTrans = TransList[CEP[i]].z3Formulas
        for j in range(1, len(CEP) - i):
            tmpTrans = connect_trans(tmpTrans, TransList[CEP[j + i]].z3Formulas)
        phi2 = list(set(phi_err + tmpTrans))
        
        for VName, VZ3 in ALL_VARS.items():
            if "_" in VName:
                eliminate_one(VZ3, phi2)
        
        inter = craigInterpolant(phi1, phi2)
        print(inter)

        if inter not in Result:
            Result.append(inter)
        # 过滤 True 我认为谓词中不应该出现True和False
        # 第一个一定是True 因为这是近似结果 * 存疑  
        # 最后一个一定是False 因为这是一个反例
    return [p for p in Result if p is not TrueConstant]

# Computing Least Solution for refining predicates
def LeastSolution(CEP):
    tmpPhi = StateList[initID].z3Formula    #备份Phi_int
    StateResult = []
    for rhoId in CEP:
        tmpState = post(StateList[initID], TransList[rhoId].z3Formula)
        StateResult.append(tmpState)
    return StateResult

def craigInterpolant(formulaA, formulaB):
    print("phi1 = ", end="")
    print(formulaA)
    print("phi2 = ", end="")
    print(formulaB)
    if FalseConstant in formulaB:
        return TrueConstant
    # 插值计算时候，去掉pc
    itp = Interpolator(name="msat")
    formulaANoPc = []
    formulaBNoPc = []
    for formula in formulaA:
        if formula not in [TrueConstant, FalseConstant]:
            if formula.arg(0) != ALL_VARS["pc"]:
                formulaANoPc.append(formula)
        else:
            formulaANoPc.append(formula)
    for formula in formulaB:
        if formula not in [TrueConstant, FalseConstant]:
            if formula.arg(0) != ALL_VARS["pc"]:
                formulaBNoPc.append(formula)
        else:
            formulaBNoPc.append(formula)
    inter = itp.binary_interpolant(And(formulaANoPc), And(formulaBNoPc))
    return inter

# AbstRefindLoop Function
def AbstRefineLoop():
    while True:
        flag = False
        AbstractReach()

        for ArtID, artState in ArtList.items():
            res = is_sat(And(artState.z3Formula + StateList[errID].z3Formula), solver_name="z3")
            if not res:
                continue
            flag = True

            CEP = MakePath(ArtID)
            print("CEP:", CEP)
                # 如果反例路径得到结果和State_err有交集，就输出反例路径
            if FeasiblePath(CEP):
                print("counter-example path:", CEP)
                return CEP
            else:
                print("counterExamplePath:", CEP)
                print("refining..")
                newPradicates = RefinePath(CEP)
                for np in newPradicates:
                    if np in Preds:
                        continue
                    else:
                        Preds.append(np)

        print("[Preds]", Preds)
        if not flag:
            print("Preds Count:", len(Preds))
            print("program is correct")
            return 


starttime = datetime.datetime.now()
with eventlet.Timeout(3, False):
    AbstRefineLoop()
    print("Time Out 10s")
endtime = datetime.datetime.now()
print("VerifyT:\t",endtime - starttime)