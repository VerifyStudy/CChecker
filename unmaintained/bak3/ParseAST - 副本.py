from graphviz import Digraph
import copy
import datetime

from pysmt.shortcuts import *
from pysmt.typing import INT

import clang.cindex
from clang.cindex import Index  #主要 API
from clang.cindex import Config  #配置
from clang.cindex import CursorKind  #索引结点的类别
from clang.cindex import TypeKind    #节点的语义类别

libclangPath = r'./lib/libclang.so'
# libclangPath = r'./lib/libclang.dll'

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


directory = r"./TestFiles/"     # 测试文件路径

AST_root_node = None # 根节点
varsPool = []   # 初始只有位置谓词
TransList = dict()      # 文本类型转化集
StateList = dict()      # 状态集

# Vars and Vars' dict
Z3AllVars = dict()
VrasDict = dict()

g = Digraph(name='CFA', comment="comment", format='png')    # graph object

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
def getRootNode(directory = directory, filename = filename):
    index = Index.create() # 创建AST索引
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
        self.z3Formula = None
        self.name = self.getName()      # line : formula
        self.relatedRhoIDs = []         # [0,1] TransNode.ID
        self.toStateIDs = []            # [1,2] StateNode.ID
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
    
    def initZ3Formula(self):
        z3Formula = []
        formula = copy.deepcopy(self.formula)
        formulas = [formula] + [["pc", "=", self.line]]
        for formula in formulas:
            if len(formula) == 1:
                self.z3Formula = z3Formula
                return
            for index in range(len(formula)):
                if isDigit(formula[index]):
                    formula[index] = "Int(" + formula[index].strip() + ")"
                elif formula[index] not in ["=", "==", "!=", ">", ">=", "<", "<=", "+", "-"] :
                    formula[index] = "Z3AllVars['{var}']".format(var = formula[index])
            if formula[1] == "=":
                exec("z3Formula.append(Equals({left},{right}))".format(left = formula[0], right = "".join(formula[2:])))
            elif formula[1] == "!=":
                exec("z3Formula.append(NotEquals({left},{right}))".format(left = formula[0], right = "".join(formula[2:])))
            elif formula[1] == "<=":
                exec("z3Formula.append(LE({left},{right}))".format(left = formula[0], right = "".join(formula[2:])))
            elif formula[1] == "<":
                exec("z3Formula.append(LT({left},{right}))".format(left = formula[0], right = "".join(formula[2:])))
            elif formula[1] == ">=":
                exec("z3Formula.append(GE({left},{right}))".format(left = formula[0], right = "".join(formula[2:])))
            elif formula[1] == ">":
                exec("z3Formula.append(GT({left},{right}))".format(left = formula[0], right = "".join(formula[2:])))
            
        self.z3Formula = z3Formula

class TransNode(object):
    id = 0
    def __init__(self, fromStateID, toStateID, reversed=False):
        self.ID = TransNode.id
        self.reversed = reversed
        self.fromStateID = fromStateID
        self.toStateID = toStateID
        self.formulas = None
        self.z3Formulas = None
        self.name = ""
        TransNode.id += 1

    def initFormulas(self):
        f1 = copy.copy(StateList[self.fromStateID].formula)
        f2 = unChanged(StateList[self.fromStateID].vars)
        unChangedStr = "{" + ",".join(StateList[self.fromStateID].vars) + "}"
        if self.reversed:
            self.formulas = [reveredFormula(f1)] + f2
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
        formulas = copy.deepcopy(self.formulas)
        formulas = formulas + [["pc", "=", StateList[self.fromStateID].line], ["pc_", "=", StateList[self.toStateID].line]]
        z3Formula = []
        for formula in formulas:
            for index in range(len(formula)):
                if isDigit(formula[index]):
                    formula[index] = "Int(" + formula[index].strip() + ")"
                elif formula[index] not in ["=", "==", "!=", ">", ">=", "<", "<=", "+" ,"-"] :
                    formula[index] = "Z3AllVars['{var}']".format(var = formula[index])
            if formula[1] == "=":
                exec("z3Formula.append(Equals({left},{right}))".format(left = formula[0], right = "".join(formula[2:])))
            elif formula[1] == "!=":
                exec("z3Formula.append(NotEquals({left},{right}))".format(left = formula[0], right = "".join(formula[2:])))
            elif formula[1] == "<=":
                exec("z3Formula.append(LE({left},{right}))".format(left = formula[0], right = "".join(formula[2:])))
            elif formula[1] == "<":
                exec("z3Formula.append(LT({left},{right}))".format(left = formula[0], right = "".join(formula[2:])))
            elif formula[1] == ">=":
                exec("z3Formula.append(GE({left},{right}))".format(left = formula[0], right = "".join(formula[2:])))
            elif formula[1] == ">":
                exec("z3Formula.append(GT({left},{right}))".format(left = formula[0], right = "".join(formula[2:])))                
        self.z3Formulas = z3Formula

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
                    TransList[trans.ID] = copy.deepcopy(trans)
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
                    TransList[trans.ID] = copy.deepcopy(trans)
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
    TransList[trans.ID] = copy.deepcopy(trans)
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

##################
#   Parse Node   #
##################
# 赋值
def parseEvaluationStmt(BinaryOperator):
    line, formula = parseOperator2Formula(BinaryOperator)
    state = StateNode(line = line, formula = formula)
    state.vars = [var for var in varsPool if formula[0] != var]
    StateList[state.ID] = copy.deepcopy(state)

    trans = TransNode(state.ID, 0)  # 创建转移
    TransList[trans.ID] = copy.deepcopy(trans)  # 添加到转移栈中
    StateList[state.ID].relatedRhoIDs.append(trans.ID)  # 连接到状态上
    return state.ID

# 声明
def parseDeclStmt(DeclStmt):
    line, formula = parseDecl2Formula(DeclStmt)
    state = StateNode(line = line, formula = formula)
    state.vars = copy.copy(varsPool[:-1])
    StateList[state.ID] = copy.deepcopy(state)

    trans = TransNode(state.ID, 0)  # 创建转移
    TransList[trans.ID] = copy.deepcopy(trans)  # 添加到转移栈中
    StateList[state.ID].relatedRhoIDs.append(trans.ID)  # 连接到状态上
    return state.ID

# 条件 If和While中的判断条件
def parseCondtionStmt(BinaryOperator):
    line, formula = parseOperator2Formula(BinaryOperator)
    state = StateNode(line = line, formula = formula)
    state.vars = copy.copy(varsPool)
    StateList[state.ID] = copy.deepcopy(state)

    trans = TransNode(state.ID, 0)  # 创建转移
    TransList[trans.ID] = copy.deepcopy(trans)  # 添加到转移栈中
    StateList[state.ID].relatedRhoIDs.append(trans.ID)  # 连接到状态上
    return state.ID

# Return 
def getReturnNode(formula = "End", line = '0'):
    state = StateNode(line = line, formula = formula)
    StateList[state.ID] = copy.deepcopy(state)
    return state.ID

################
# Parse  AST   #
################
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
    StateList[state.ID] = copy.deepcopy(state)

    # 生成SAT和UNSAT结点
    sat = StateNode(line = "-1", formula = ["sat"])
    unsat = StateNode(line = "-2", formula = ["unsat"])
    StateList[sat.ID] = copy.deepcopy(sat)
    StateList[unsat.ID] = copy.deepcopy(unsat)
    # 状态连接
    StateList[state.ID].toStateIDs.append(sat.ID)
    StateList[state.ID].toStateIDs.append(unsat.ID)

    satTrans = TransNode(state.ID, sat.ID)
    unsatTrans = TransNode(state.ID, unsat.ID, True)
    TransList[satTrans.ID] = copy.deepcopy(satTrans)
    TransList[unsatTrans.ID] = copy.deepcopy(unsatTrans)
    StateList[state.ID].relatedRhoIDs=[satTrans.ID, unsatTrans.ID]

    return state.ID

# formula=['x','>','1']，反转
def reveredFormula(formula):
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
    
def unChanged(vars = []):
    f = []
    for var in vars:
        f.append([var + "_", "=", var])
    return f


# 自己定义了一个判断字符串是否为整型数字的方法；python自带的判断字符串是否为数字的方法isdigit()好像不能判断负数，
# 比如isdigit()认为“-11”不是数字。
def isDigit(x):
    x = x.strip()
    if len(x) > 0 and x[0] == "-":
        x = x[1:]
    return x.isdigit()

def InitializedCFG():
    configLibClang(libclangPath)
    AST_root_node = getRootNode()
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
    for ID, trans in TransList.items():
        g.edge(StateList[trans.fromStateID].line, StateList[trans.toStateID].line, trans.name)

    Preds = [Equals(Z3AllVars["pc"], Int(int(state.line))) for ID, state in StateList.items()]

    print("Initialized CFG!")
    print("Vars' Count:\t", len(VrasDict), "\tTransitions Count:\t", len(TransList))
    print("All Vars and Vars' dict form")
    print(VrasDict)
    print("ALL StateList")
    for ID, node in StateList.items():
        print("id:",ID, "line:", node.line, "formula:", node.z3Formula, " next node id:", node.toStateIDs, " vars:", node.vars)
    print("ALL TransList")
    for transID, trans in TransList.items():
        print("id:", transID, " From:", StateList[trans.fromStateID].line," To:", StateList[trans.toStateID].line," formula:", trans.z3Formulas)
    print("Preds")
    print(Preds)


    endtime = datetime.datetime.now()
    print("ParseT:\t", endtime - starttime)
    g.render(filename=filename[0:-2] + '.gv', directory=r'./CFA')
    
    return VrasDict, Z3AllVars, Preds, TransList, StateList


# VrasDict, Z3AllVars, Preds, TransList, StateList = InitializedCFG()

# 可以将散落的g.edge写在一起，那样如果出了问题调试起来可能会很难