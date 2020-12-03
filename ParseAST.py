from graphviz import Digraph
import copy

from pysmt.shortcuts import *
from pysmt.typing import INT

import clang.cindex
from clang.cindex import Index  #主要API
from clang.cindex import Config  #配置
from clang.cindex import CursorKind  #索引结点的类别
from clang.cindex import TypeKind    #节点的语义类别


libclangPath = r'./lib/libclang.dll'
# file_path = r"./test/TestCFG.c" # 文件路径
# file_path = r"./test/TestWhile.c" # 文件路径
file_path = r"./test/While.c" # 文件路径
AST_root_node = None # 根节点
AssumeFlag = False
g = Digraph(name='CFG', comment="comment", format='png')

varsPool = []   # 初始只有位置谓词
Trans = []
Nodes = []
AssumeLoc = -1  # assume function location

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
def getRootNode(file_path):
    index = Index.create() # 创建AST索引

    tu = index.parse(file_path)
    AST_root_node= tu.cursor  #cursor根节点
    print(AST_root_node)    # 有输出表示读取文件成功
    return AST_root_node

# 前序遍历函数 cursor is root node
def preorder_travers_AST(cursor):
    for cur in cursor.get_children():
        # do something
        # print("kind:", cur.kind," \tcur.spelling:", cur.spelling)
        # solve(cur)  # 解析主函数
        if cur.kind == CursorKind.FUNCTION_DECL:
            print(cur.spelling)
            parseFunctionDecl(cur)
        preorder_travers_AST(cur)

class Node(object):
    id = 0 # static class variable
    def __init__(self, name, line, formula, changed):
        self.name = name
        self.ID = str(Node.id)
        self.line = str(line)
        self.formula = formula
        self.changed = changed
        Node.id += 1
        pass

def parseFunctionDecl(FunctionDecl):
    for compound in FunctionDecl.get_children():
        traversCompoundStmt(compound)
    pass

# Compound结点
def traversCompoundStmt(CompoundStmt):
    global AssumeLoc
    global AssumeFlag
    CompoundStmtNodes = []
    ifEndNode = None
    elseEndNode = None
    gNode = None
    for node in CompoundStmt.get_children():
        if node.kind == CursorKind.IF_STMT:
            gNode, ifEndNode, elseEndNode = traversIfStmt(node)
            g.node(name=gNode.ID, label=gNode.name)
            if len(CompoundStmtNodes) > 0:
                g.edge(CompoundStmtNodes[-1].ID, gNode.ID, label="to if")
                Trans.append("pc == " + CompoundStmtNodes[-1].line + ", pc_ == " + gNode.line + ", " + CompoundStmtNodes[-1].formula + unChanged([gNode.changed, CompoundStmtNodes[-1].changed]))
            CompoundStmtNodes.append(gNode)                        
        if node.kind == CursorKind.WHILE_STMT:
            cur = len(Trans)
            gNode = traversWhileStmt(node)
            g.node(name=gNode.ID, label=gNode.name)
            if len(CompoundStmtNodes) > 0:
                if ifEndNode is not None:
                    g.edge(ifEndNode.ID, gNode.ID, label="if-end")
                    Trans.append("pc == " + ifEndNode.line + ", pc_ == " + gNode.line + ", " + ifEndNode.formula + unChanged([gNode.changed, ifEndNode.changed]))
                    ifEndNode = None
                if elseEndNode is not None:
                    g.edge(elseEndNode.ID, gNode.ID, label="else-end")
                    Trans.append("pc == " + elseEndNode.line + ", pc_ == " + gNode.line + ", " + elseEndNode.formula + unChanged([gNode.changed, elseEndNode.changed]))
                    elseEndNode = None
                else:
                    g.edge(CompoundStmtNodes[-1].ID, gNode.ID, label="to while")
                    Trans.append("pc == " + CompoundStmtNodes[-1].line + ", pc_ == " + gNode.line + ", " + CompoundStmtNodes[-1].formula + unChanged([gNode.changed, CompoundStmtNodes[-1].changed]))
            CompoundStmtNodes.append(gNode)
            if AssumeFlag:
                Trans[-1], Trans[cur] = Trans[cur], Trans[-1]
                AssumeFlag = False
        if node.kind == CursorKind.DECL_STMT:
            gNode = parseDeclStmt(node)
            g.node(name=gNode.ID, label=gNode.name)
            if len(CompoundStmtNodes) > 0:
                if ifEndNode is not None:
                    g.edge(ifEndNode.ID, gNode.ID, label="if-end")
                    Trans.append("pc == " + ifEndNode.line + ", pc_ == " + gNode.line + ", " + ifEndNode.formula + unChanged([gNode.changed, ifEndNode.changed]))
                    ifEndNode = None
                if elseEndNode is not None:
                    g.edge(elseEndNode.ID, gNode.ID, label="else-end")
                    Trans.append("pc == " + elseEndNode.line + ", pc_ == " + gNode.line + ", " + elseEndNode.formula + unChanged([gNode.changed, elseEndNode.changed]))
                    elseEndNode = None
                else:
                    g.edge(CompoundStmtNodes[-1].ID, gNode.ID)
                    Trans.append("pc == " + CompoundStmtNodes[-1].line + ", pc_ == " + gNode.line + ", " + CompoundStmtNodes[-1].formula + unChanged([gNode.changed, CompoundStmtNodes[-1].changed]))
            CompoundStmtNodes.append(gNode)
        if node.kind == CursorKind.BINARY_OPERATOR:
            gNode = parseEvaluationStmt(node)
            g.node(name=gNode.ID, label=gNode.name)
            if len(CompoundStmtNodes) > 0:
                if ifEndNode is not None:
                    g.edge(ifEndNode.ID, gNode.ID, label="if-end")
                    Trans.append("pc == " + ifEndNode.line + ", pc_ == " + gNode.line + ", " + ifEndNode.formula + unChanged([gNode.changed, ifEndNode.changed]))
                    ifEndNode = None
                if elseEndNode is not None:
                    g.edge(elseEndNode.ID, gNode.ID, label="else-end")
                    Trans.append("pc == " + elseEndNode.line + ", pc_ == " + gNode.line + ", " + elseEndNode.formula + unChanged([gNode.changed, elseEndNode.changed]))
                    elseEndNode = None
                else:
                    g.edge(CompoundStmtNodes[-1].ID, gNode.ID)
                    Trans.append("pc == " + CompoundStmtNodes[-1].line + ", pc_ == " + gNode.line + ", " + CompoundStmtNodes[-1].formula + unChanged([gNode.changed, CompoundStmtNodes[-1].changed]))
            CompoundStmtNodes.append(gNode)
        if node.kind == CursorKind.RETURN_STMT:
            satNode = getReturnNode("SAT", -1)
            unsatNode = getReturnNode("UNSAT", -2)
            g.node(name = satNode.ID, label = satNode.name)
            g.node(name = unsatNode.ID, label = unsatNode.name)
            if len(CompoundStmtNodes) > 0:
                g.edge(CompoundStmtNodes[-1].ID, satNode.ID, "assert sat")
                Trans.append("pc == " + CompoundStmtNodes[-1].line + ", pc_ == " + satNode.line + ", " + CompoundStmtNodes[-1].formula + unChanged([satNode.changed, CompoundStmtNodes[-1].changed]))
                g.edge(CompoundStmtNodes[-1].ID, unsatNode.ID, "assert unsat")
                Trans.append("pc == " + CompoundStmtNodes[-1].line + ", pc_ == " + unsatNode.line + ", " + reveredFormula(CompoundStmtNodes[-1].formula) + unChanged([unsatNode.changed, CompoundStmtNodes[-2].changed]))
            else:
                print("Error No assert function")
                return
        if node.kind == CursorKind.CALL_EXPR:
            if node.spelling == "sassert":
                gNode = parseAssertStmt(node)
                g.node(name=gNode.ID, label=gNode.name)
                if ifEndNode is not None:
                    g.edge(ifEndNode.ID, gNode.ID, "if-assert")
                    Trans.append("pc == " + ifEndNode.line + ", pc_ == " + gNode.line + ", " + ifEndNode.formula + unChanged([ifEndNode.changed, gNode.changed]))
                if elseEndNode is not None:
                    g.edge(elseEndNode.ID, gNode.ID, "else-assert")
                    Trans.append("pc == " + elseEndNode.line + ", pc_ == " + gNode.line + ", " + elseEndNode.formula + unChanged([elseEndNode.changed, gNode.changed]))
                else:
                    g.edge(CompoundStmtNodes[-1].ID, gNode.ID, "to-assert")
                    Trans.append("pc == " + CompoundStmtNodes[-1].line + ", pc_ == " + gNode.line + ", " + CompoundStmtNodes[-1].formula + unChanged([CompoundStmtNodes[-1].changed, gNode.changed]))
                CompoundStmtNodes.append(gNode)
            if node.spelling == "assume":
                AssumeFlag = True
                gNode = parseAssumeStmt(node)
                g.node(name=gNode.ID, label=gNode.name)
                if ifEndNode is not None:
                    g.edge(ifEndNode.ID, gNode.ID, "if-assume")
                    Trans.append("pc == " + ifEndNode.line + ", pc_ == " + gNode.line + ", " + ifEndNode.formula + unChanged([ifEndNode.changed, gNode.changed]))
                if elseEndNode is not None:
                    g.edge(elseEndNode.ID, gNode.ID, "else-assume")
                    Trans.append("pc == " + elseEndNode.line + ", pc_ == " + gNode.line + ", " + elseEndNode.formula + unChanged([elseEndNode.changed, gNode.changed]))
                else:
                    g.edge(CompoundStmtNodes[-1].ID, gNode.ID, "to-assume")
                    Trans.append("pc == " + CompoundStmtNodes[-1].line + ", pc_ == " + gNode.line + ", " + CompoundStmtNodes[-1].formula + unChanged([CompoundStmtNodes[-1].changed, gNode.changed]))
                AssumeLoc = len(Trans)
                CompoundStmtNodes.append(gNode)

    pass

# 赋值
def parseEvaluationStmt(BinaryOperator):
    formula, line, changed = parseOperator2Formula(BinaryOperator)
    node = Node(name = line + ":" + formula, line = line, formula = formula, changed = changed)
    Nodes.append(copy.deepcopy(node))
    return node
    pass

# 声明
def parseDeclStmt(DeclStmt):
    Type, formula, line, changed = parseDecl2Formula(DeclStmt)
    node = Node(name = line + ":" + formula, line = line, formula = formula, changed = changed)
    Nodes.append(copy.deepcopy(node))
    return node
    pass

# IfStmt结点
def traversIfStmt(IfStmt):
    CompoundStmt = []
    conditionNode = None
    ifEndNode = None
    elseEndNode = None
    for node in IfStmt.get_children():
        if node.kind == CursorKind.BINARY_OPERATOR: # if condition
            conditionNode = parseCondtionStmt(node)
        if node.kind == CursorKind.COMPOUND_STMT:   # if body and else body
            CompoundStmt.append(node)
    if len(CompoundStmt) != 2:
        print("Error: Code not formalized! IF-Then-Else")
        return
    ifEndNode = traversIfCompound(CompoundStmt[0], conditionNode)
    conditionNode.formula = reveredFormula(conditionNode.formula)
    elseEndNode = traversElseCompound(CompoundStmt[1], conditionNode)
    return conditionNode, ifEndNode, elseEndNode
    pass

# IfStmt结点 IfBody块
def traversIfCompound(IfCompoundStmt, conditionNode):
    CompoundStmtNodes = []
    gNode = None
    ifEndNode = None
    elseEndNode = None
    for node in IfCompoundStmt.get_children():
        if node.kind == CursorKind.IF_STMT:
            gNode, ifEndNode, elseEndNode = traversIfStmt(node)
            g.node(name=gNode.ID, label=gNode.name)
            if len(CompoundStmtNodes) > 0:
                g.edge(CompoundStmtNodes[-1].ID, gNode.ID, label="to if condition")
                Trans.append("pc == " + CompoundStmtNodes[-1].line + ", pc_ == " + gNode.line + ", " + CompoundStmtNodes[-1].formula + unChanged([gNode.changed, CompoundStmtNodes[-1].changed]))
            else:
                g.edge(conditionNode.ID, gNode.ID, label="if-if")
                Trans.append("pc == " + conditionNode.line + ", pc_ == " + gNode.line + ", " + conditionNode.formula + unChanged([gNode.changed, conditionNode.changed]))
            CompoundStmtNodes.append(gNode)
        if node.kind == CursorKind.WHILE_STMT:
            gNode = traversWhileStmt(node)
            g.node(name=gNode.ID, label=gNode.name)
            if len(CompoundStmtNodes) > 0:
                g.edge(CompoundStmtNodes[-1].ID, gNode.ID, label="if-while")
                Trans.append("pc == " + CompoundStmtNodes[-1].line + ", pc_ == " + gNode.line + ", " + CompoundStmtNodes[-1].formula + unChanged([gNode.changed, CompoundStmtNodes[-1].changed]))
            else:
                g.edge(conditionNode.ID, gNode.ID, label="if-while")
                Trans.append("pc == " + conditionNode.line + ", pc_ == " + gNode.line + ", " + conditionNode.formula + unChanged([gNode.changed, conditionNode.changed]))
            CompoundStmtNodes.append(gNode)
        if node.kind == CursorKind.DECL_STMT:
            gNode = parseDeclStmt(node)
            g.node(name=gNode.ID, label=gNode.name)
            if len(CompoundStmtNodes) > 0:
                if ifEndNode is not None:
                    g.edge(ifEndNode.ID, gNode.ID, label="if-end")
                    Trans.append("pc == " + ifEndNode.line + ", pc_ == " + gNode.line + ", " + ifEndNode.formula + unChanged([gNode.changed, ifEndNode.changed]))
                    ifEndNode = None
                if elseEndNode is not None:
                    g.edge(elseEndNode.ID, gNode.ID, label="else-end")
                    Trans.append("pc == " + elseEndNode.line + ", pc_ == " + gNode.line + ", " + elseEndNode.formula + unChanged([gNode.changed, elseEndNode.changed]))
                    elseEndNode = None
                else:
                    g.edge(CompoundStmtNodes[-1].ID, gNode.ID)
                    Trans.append("pc == " + CompoundStmtNodes[-1].line + ", pc_ == " + gNode.line + ", " + CompoundStmtNodes[-1].formula + unChanged([gNode.changed, CompoundStmtNodes[-1].changed]))
            else:
                g.edge(conditionNode.ID, gNode.ID)
                Trans.append("pc == " + conditionNode.line + ", pc_ == " + gNode.line + ", " + conditionNode.formula + unChanged([gNode.changed, conditionNode.changed]))
            CompoundStmtNodes.append(gNode)
        if node.kind == CursorKind.BINARY_OPERATOR:
            gNode = parseEvaluationStmt(node)
            g.node(name=gNode.ID, label=gNode.name)
            if len(CompoundStmtNodes) > 0:
                if ifEndNode is not None:
                    g.edge(ifEndNode.ID, gNode.ID, label="if-end")
                    Trans.append("pc == " + ifEndNode.line + ", pc_ == " + gNode.line + ", " + ifEndNode.formula + unChanged([gNode.changed, ifEndNode.changed]))
                    ifEndNode = None
                if elseEndNode is not None:
                    g.edge(elseEndNode.ID, gNode.ID, label="else-end")
                    Trans.append("pc == " + elseEndNode.line + ", pc_ == " + gNode.line + ", " + elseEndNode.formula + unChanged([gNode.changed, elseEndNode.changed]))
                    elseEndNode = None
                else:
                    g.edge(CompoundStmtNodes[-1].ID, gNode.ID)
                    Trans.append("pc == " + CompoundStmtNodes[-1].line + ", pc_ == " + gNode.line + ", " + CompoundStmtNodes[-1].formula + unChanged([gNode.changed, CompoundStmtNodes[-1].changed]))
            else:
                g.edge(conditionNode.ID, gNode.ID)
                Trans.append("pc == " + conditionNode.line + ", pc_ == " + gNode.line + ", " + conditionNode.formula + unChanged([gNode.changed, conditionNode.changed]))
            CompoundStmtNodes.append(gNode)
        if node.kind == CursorKind.RETURN_STMT:
            gNode = getReturnNode()
            g.node(name=gNode.ID, label=gNode.name)
            if len(CompoundStmtNodes) > 0:
                g.edge(CompoundStmtNodes[-1].ID, gNode.ID, label="if-end")
                Trans.append("pc == " + CompoundStmtNodes[-1].line + ", pc_ == " + gNode.line + ", " + CompoundStmtNodes[-1].formula + unChanged([gNode.changed, CompoundStmtNodes[-1].changed]))
            else:
                g.edge(conditionNode.ID, gNode.ID, label="if-end")
                Trans.append("pc == " + conditionNode.line + ", pc_ == " + gNode.line + ", " + conditionNode.formula + unChanged([gNode.changed, conditionNode.changed]))
                return gNode
    return CompoundStmtNodes[-1]
    pass

# IfStmt结点 ElseBody块
def traversElseCompound(ElseCompoundStmt, conditionNode):
    CompoundStmtNodes = []
    gNode = None
    ifEndNode = None
    elseEndNode = None
    for node in ElseCompoundStmt.get_children():
        if node.kind == CursorKind.IF_STMT:
            gNode = traversIfStmt(node)
            g.node(name=gNode.ID, label=gNode.name)
            if len(CompoundStmtNodes) > 0:
                g.edge(CompoundStmtNodes[-1].ID, gNode.ID, label="else-if")
                Trans.append("pc == " + CompoundStmtNodes[-1].line + ", pc_ == " + gNode.line + ", " + CompoundStmtNodes[-1].formula + unChanged([gNode.changed, CompoundStmtNodes[-1].changed]))
            else:
                g.edge(conditionNode.ID, gNode.ID, label="else-if")
                Trans.append("pc == " + conditionNode.line + ", pc_ == " + gNode.line + ", " + conditionNode.formula + unChanged([gNode.changed, conditionNode.changed]))
            CompoundStmtNodes.append(gNode)                
        if node.kind == CursorKind.WHILE_STMT:
            gNode = traversWhileStmt(node)
            g.node(name=gNode.ID, label=gNode.name)
            if len(CompoundStmtNodes) > 0:
                g.edge(CompoundStmtNodes[-1].ID, gNode.ID, label="else-while")
                Trans.append("pc == " + CompoundStmtNodes[-1].line + ", pc_ == " + gNode.line + ", " + CompoundStmtNodes[-1].formula + unChanged([gNode.changed, CompoundStmtNodes[-1].changed]))
            else:
                g.edge(conditionNode.ID, gNode.ID, label="else-while")
                Trans.append("pc == " + conditionNode.line + ", pc_ == " + gNode.line + ", " + conditionNode.formula + unChanged([gNode.changed, conditionNode.changed]))
            CompoundStmtNodes.append(gNode)
        if node.kind == CursorKind.DECL_STMT:
            gNode = parseDeclStmt(node)
            g.node(name=gNode.ID, label=gNode.name)
            if len(CompoundStmtNodes) > 0:
                if ifEndNode is not None:
                    g.edge(ifEndNode.ID, gNode.ID, label="if-end")
                    Trans.append("pc == " + ifEndNode.line + ", pc_ == " + gNode.line + ", " + ifEndNode.formula + unChanged([gNode.changed, ifEndNode.changed]))
                    ifEndNode = None
                if elseEndNode is not None:
                    g.edge(elseEndNode.ID, gNode.ID, label="else-end")
                    Trans.append("pc == " + elseEndNode.line + ", pc_ == " + gNode.line + ", " + elseEndNode.formula + unChanged([gNode.changed, elseEndNode.changed]))
                    elseEndNode = None                    
                else:
                    g.edge(CompoundStmtNodes[-1].ID, gNode.ID)
                    Trans.append("pc == " + CompoundStmtNodes[-1].line + ", pc_ == " + gNode.line + ", " + CompoundStmtNodes[-1].formula + unChanged([gNode.changed, CompoundStmtNodes[-1].changed]))
            else:
                g.edge(conditionNode.ID, gNode.ID)
                Trans.append("pc == " + conditionNode.line + ", pc_ == " + gNode.line + ", " + conditionNode.formula + unChanged([gNode.changed, conditionNode.changed]))
            CompoundStmtNodes.append(gNode)
        if node.kind == CursorKind.BINARY_OPERATOR:
            gNode = parseEvaluationStmt(node)
            g.node(name=gNode.ID, label=gNode.name)
            if len(CompoundStmtNodes) > 0:
                if ifEndNode is not None:
                    g.edge(ifEndNode.ID, gNode.ID, label="if-end")
                    Trans.append("pc == " + ifEndNode.line + ", pc_ == " + gNode.line + ", " + ifEndNode.formula + unChanged([gNode.changed, ifEndNode.changed]))
                    ifEndNode = None
                if elseEndNode is not None:
                    g.edge(elseEndNode.ID, gNode.ID, label="else-end")
                    Trans.append("pc == " + elseEndNode.line + ", pc_ == " + gNode.line + ", " + elseEndNode.formula + unChanged([gNode.changed, elseEndNode.changed]))
                    elseEndNode = None 
                else:
                    g.edge(CompoundStmtNodes[-1].ID, gNode.ID)
                    Trans.append("pc == " + CompoundStmtNodes[-1].line + ", pc_ == " + gNode.line + ", " + CompoundStmtNodes[-1].formula + unChanged([gNode.changed, CompoundStmtNodes[-1].changed]))
            else:
                g.edge(conditionNode.ID, gNode.ID)
                Trans.append("pc == " + conditionNode.line + ", pc_ == " + gNode.line + ", " + conditionNode.formula + unChanged([gNode.changed, conditionNode.changed]))
            CompoundStmtNodes.append(gNode)
    if len(CompoundStmtNodes) == 0:
        return None
    else:
        return CompoundStmtNodes[-1]
    pass

# WhileStmt结点
def traversWhileStmt(WhileStmt):
    conditionNode = None
    for node in WhileStmt.get_children():
        if node.kind == CursorKind.BINARY_OPERATOR:
            conditionNode = parseCondtionStmt(node)
        if node.kind == CursorKind.COMPOUND_STMT:
            traversWhileBody(node, conditionNode)
    conditionNode.formula = reveredFormula(conditionNode.formula)
    return conditionNode

#WhileBody块
def traversWhileBody(CompoundStmt, conditionNode):
    CompoundStmtNodes = []
    gNode = None
    ifEndNode = None
    elseEndNode = None
    for node in CompoundStmt.get_children():
        if node.kind == CursorKind.IF_STMT:
            gNode, ifEndNode, elseEndNode = traversIfStmt(node)
            g.node(name=gNode.ID, label=gNode.name)
            if len(CompoundStmtNodes) > 0:
                g.edge(CompoundStmtNodes[-1].ID, gNode.ID, label="while-if")
                Trans.append("pc == " + CompoundStmtNodes[-1].line + ", pc_ == " + gNode.line + ", " + CompoundStmtNodes[-1].formula + unChanged([gNode.changed, CompoundStmtNodes[-1].changed]))
            else:
                g.edge(conditionNode.ID, gNode.ID, label="while-if")
                Trans.append("pc == " + conditionNode.line + ", pc_ == " + gNode.line + ", " + conditionNode.formula + unChanged([gNode.changed, conditionNode.changed]))
            CompoundStmtNodes.append(gNode)
        if node.kind == CursorKind.WHILE_STMT:
            gNode = traversWhileStmt(node)
            g.node(name=gNode.ID, label=gNode.name)
            if len(CompoundStmtNodes) > 0:
                g.edge(CompoundStmtNodes[-1].ID, gNode.ID, label="while-while")
                Trans.append("pc == " + CompoundStmtNodes[-1].line + ", pc_ == " + gNode.line + ", " + CompoundStmtNodes[-1].formula + unChanged([gNode.changed, CompoundStmtNodes[-1].changed]))
            else:
                g.edge(conditionNode.ID, gNode.ID, label="while-while")
                Trans.append("pc == " + conditionNode.line + ", pc_ == " + gNode.line + ", " + conditionNode.formula + unChanged([gNode.changed, conditionNode.changed]))
            CompoundStmtNodes.append(gNode)
        if node.kind == CursorKind.DECL_STMT:
            gNode = parseDeclStmt(node)
            g.node(name=gNode.ID, label=gNode.name)
            if len(CompoundStmtNodes) > 0:
                if ifEndNode is not None:
                    g.edge(ifEndNode.ID, gNode.ID, label="if-end")
                    Trans.append("pc == " + ifEndNode.line + ", pc_ == " + gNode.line + ", " + ifEndNode.formula + unChanged([gNode.changed, ifEndNode.changed]))
                    ifEndNode = None
                if elseEndNode is not None:
                    g.edge(elseEndNode.ID, gNode.ID, label="else-end")
                    Trans.append("pc == " + elseEndNode.line + ", pc_ == " + gNode.line + ", " + elseEndNode.formula + unChanged([gNode.changed, elseEndNode.changed]))
                    elseEndNode = None
                else:
                    g.edge(CompoundStmtNodes[-1].ID, gNode.ID)
                    Trans.append("pc == " + CompoundStmtNodes[-1].line + ", pc_ == " + gNode.line + ", " + CompoundStmtNodes[-1].formula + unChanged([gNode.changed, CompoundStmtNodes[-1].changed]))
            else:
                g.edge(conditionNode.ID, gNode.ID)
                Trans.append("pc == " + conditionNode.line + ", pc_ == " + gNode.line + ", " + conditionNode.formula + unChanged([gNode.changed, conditionNode.changed]))
            CompoundStmtNodes.append(gNode)
        if node.kind == CursorKind.BINARY_OPERATOR:
            gNode = parseEvaluationStmt(node)
            g.node(name=gNode.ID, label=gNode.name)
            if len(CompoundStmtNodes) > 0:
                if ifEndNode is not None:
                    g.edge(ifEndNode.ID, gNode.ID, label="if-end")
                    Trans.append("pc == " + ifEndNode.line + ", pc_ == " + gNode.line + ", " + ifEndNode.formula + unChanged([gNode.changed, ifEndNode.changed]))
                    ifEndNode = None
                if elseEndNode is not None:
                    g.edge(elseEndNode.ID, gNode.ID, label="else-end")
                    Trans.append("pc == " + elseEndNode.line + ", pc_ == " + gNode.line + ", " + elseEndNode.formula + unChanged([gNode.changed, elseEndNode.changed]))
                    elseEndNode = None
                else:
                    g.edge(CompoundStmtNodes[-1].ID, gNode.ID)
                    Trans.append("pc == " + CompoundStmtNodes[-1].line + ", pc_ == " + gNode.line + ", " + CompoundStmtNodes[-1].formula + unChanged([gNode.changed, CompoundStmtNodes[-1].changed]))
            else:
                g.edge(conditionNode.ID, gNode.ID)
                Trans.append("pc == " + conditionNode.line + ", pc_ == " + gNode.line + ", " + conditionNode.formula + unChanged([conditionNode.changed]))
            CompoundStmtNodes.append(gNode)
    if ifEndNode is not None:
        g.edge(ifEndNode.ID, conditionNode.ID, label="if-while")
        Trans.append("pc == " + ifEndNode.line + ", pc_ == " + conditionNode.line + ", " + ifEndNode.formula + unChanged([conditionNode.changed, ifEndNode.changed]))
    if elseEndNode is not None:
        g.edge(elseEndNode.ID, conditionNode.ID, label="else-while")
        Trans.append("pc == " + elseEndNode.line + " pc == " + conditionNode.line + ", " + elseEndNode.formula + unChanged([conditionNode.changed, elseEndNode.changed]))
    else:
        g.edge(CompoundStmtNodes[-1].ID, conditionNode.ID, label="while end")
        Trans.append("pc == " + CompoundStmtNodes[-1].line + ", pc_ == " + conditionNode.line + ", " + CompoundStmtNodes[-1].formula + unChanged([conditionNode.changed, CompoundStmtNodes[-1].changed]))
    pass

def parseCondtionStmt(BinaryOperator):
    formula, line, _t = parseOperator2Formula(BinaryOperator)
    node = Node(name = line + ":" + formula, line = line ,formula = formula, changed = None)
    Nodes.append(copy.deepcopy(node))
    return node
    pass

def parseOperator2Formula(BinaryOperator):
    tokens = []
    for tk in BinaryOperator.get_tokens():
        tokens.append(tk.spelling)
    if tokens[1] not in [">", ">=", "<", "<="]:
        if not tokens[0].isdigit():
            tokens[0] = tokens[0] + "_"
        tokens[1] = "=="
        formula = " ".join(tokens) # x = x + 1
        line = str(BinaryOperator.location.line)
        # return formula, line, None # 返回左值
        return formula, line, tokens[0] # 返回左值
    else:
        formula = " ".join(tokens) # x < y
        line = str(BinaryOperator.location.line)
        return formula, line, None # 无左值
    pass

def parseDecl2Formula(DeclStmt):
    tokens = []
    for tk in DeclStmt.get_tokens():
        tokens.append(tk.spelling)
    formula =tokens[1] + "_" + " == " + tokens[3] # int [x = 3] ; 不要int和;
    line = str(DeclStmt.location.line)

    # 声明语句 把新变量添加到变量池中
    if tokens[1] not in varsPool:
        varsPool.append(tokens[1])
    return tokens[0], formula, line, tokens[1]  # 返回左值
    pass

def getReturnNode(name = "End", line = 0):
    node = Node(name = name, line = line, formula = "End", changed = None)
    return node
    pass

def parseAssertStmt(AssertStmt):
    tokens = []
    for tk in AssertStmt.get_tokens():
        tokens.append(tk.spelling)
    formula = " ".join(tokens[2:-1])
    line = str(AssertStmt.location.line)
    node = Node(name = line + ":" + formula, line = line, formula = formula, changed = None)
    Nodes.append(node)
    return node
    pass

def parseAssumeStmt(AssumeStmt):
    tokens = []
    for tk in AssumeStmt.get_tokens():
        tokens.append(tk.spelling)
    formula = " ".join(tokens[2:-1])
    line = str(AssumeStmt.location.line)
    node = Node(name = line + ":" + formula, line = line, formula = formula, changed = None)
    Nodes.append(node)
    return node
    pass

def reveredFormula(formula):
    if "<" in formula:
        if "=" in formula:
            return formula.replace("<=", ">")   # <=   --- >
        else:
            return formula.replace("<", ">=")   # <    --- >=
    if ">" in formula:
        if "=" in formula:
            return formula.replace(">=", "<")   # >=   --- <
        else:
            return formula.replace(">", "<=")   # >    --- <=

def unChanged(changed):
    f = [""]
    for var in varsPool:
        if var in changed or var + "_" in changed:
            continue
        f.append("," + var + "_" + " == " + var)
    return " ".join(f)
    pass

# 自己定义了一个判断字符串是否为整型数字的方法；python自带的判断字符串是否为数字的方法isdigit()好像不能判断负数，
# 比如isdigit()认为“-11”不是数字。
def isDigit(x):
    x = x.strip()
    if len(x) > 0 and x[0] == "-":
        x = x[1:]
    return x.isdigit()

configLibClang(libclangPath)
AST_root_node = getRootNode(file_path)
preorder_travers_AST(AST_root_node)

# g.view()

# print(varsPool)


def InitializedCFG():
    # Vars and tmp predicate
    Z3AllVars = dict()
    VrasDict = dict()
    # assume
    AssumeList = []    
    # AssumePreds = []  # assume 似乎不需要谓词
    AssumeTrans = dict()
    # assert
    AssertList = []
    AssertPreds = []
    AssertTrans = dict()

    # Symbol 会调用符号管理
    # 生成所有变量的z3变量
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
    # 生成所有表达式的z3表达式
    for index, trans in enumerate(Trans):
        items = trans.split(",")
        tmpList = []
        for item in items:
            if "==" in item:
                tmpSplit = item.split("==")
                left = tmpSplit[0]
                right = tmpSplit[1]
                if isDigit(right):
                    right = "Int(" + right.strip() + ")" # Int(1)
                exec('tmpList.append(Equals({left}, {right}))'.format(left=left, right=right))
                if "pc " == left and index >= AssumeLoc:
                    exec('AssertPreds.append(Equals({left}, {right}))'.format(left=left, right=right))
            if "<=" in item:    # LE
                tmpSplit = item.split("<=")
                left = tmpSplit[0]
                right = tmpSplit[1]
                if utilities.isDigit(right):
                    right = "Int(" + right.strip() + ")" # Int(1)
                exec('tmpList.append(LE({left}, {right}))'.format(left=left, right=right))
            elif "<" in item: #   LT
                tmpSplit = item.split("<")
                left = tmpSplit[0]
                right = tmpSplit[1]
                if isDigit(right):
                    right = "Int(" + right.strip() + ")" # Int(1)
                exec('tmpList.append(LT({left}, {right}))'.format(left=left, right=right))
            if ">=" in item:    # GE
                tmpSplit = item.split(">=")
                left = tmpSplit[0]
                right = tmpSplit[1]
                if isDigit(right):
                    right = "Int(" + right.strip() + ")" # Int(1)
                exec('tmpList.append(GE({left}, {right}))'.format(left=left, right=right))
            elif ">" in item:     # GT
                tmpSplit = item.split(">")
                left = tmpSplit[0]
                right = tmpSplit[1]
                if isDigit(right):
                    right = "Int(" + right.strip() + ")" # Int(1)
                exec('tmpList.append(GT({left}, {right}))'.format(left=left, right=right))
        if index < AssumeLoc:
            AssumeList.append(tmpList)
            # AssumePreds.append(p)
            AssertList.append(tmpList)
        else:
            AssertList.append(tmpList)
    
    # AssumePreds = list(set(AssumePreds)) # 位置谓词去重
    AssertPreds = list(set(AssertPreds)) # 位置谓词去重
    AssertPreds = AssertPreds + [Equals(pc, Int(-1)), Equals(pc, Int(-2))] # 位置谓词还要添加UNSAT(-1)和SAT(-2)位置 
    # 使用zip函数转化成字典形式
    AssumeTrans = dict(zip(list(range(len(AssumeList))), AssumeList))
    AssertTrans = dict(zip(list(range(AssumeLoc, len(AssertList))), AssertList[AssumeLoc:]))
    # assume last phi
    First_trans = AssumeTrans[0]
    Assume_init = [First_trans[0], First_trans[2]]  # assume init
    First_trans = AssertTrans[len(AssumeTrans)]
    Assume_verify = [First_trans[0], First_trans[2]]    # assume verify
    # assert init phi and err phi
    Assert_init = [First_trans[0], First_trans[2]]      # assert init

    Last_trans = AssertTrans[len(AssertTrans) - 1 + len(AssumeTrans)]
    Assert_err = [Equals(pc, Int(-2)), Last_trans[2]]      # assert err

    print("Initialized CFG!")
    print("All Vars and Vars' dict form")
    print(Z3AllVars)
    print(VrasDict)
    print("Assume Trans")
    for t in AssumeTrans.items():
        print(t)
    print("Assert Trans")
    for t in AssertTrans.items():
        print(t)
    print("Assert Preds")
    print(AssertPreds)
    print("Assert_init")
    print(Assert_init)
    print("Assert_err")
    print(Assert_err)
    print("Assume_init")
    print(Assume_init)
    print("Assume_verify")
    print(Assume_verify)

    return VrasDict, Z3AllVars, AssertPreds, AssertTrans, Assert_init, Assert_err, AssumeTrans, Assume_init, Assume_verify

# VrasDict, Z3AllVars, AssertPreds, AssertTrans, Assert_init, Assert_err, AssumeTrans, Assume_init, Assume_verify= InitializedCFG()
# print(Vras)
# print(AssertPreds)
# print(AssertTrans)
# print(Phi_init)
# print(Phi_err)