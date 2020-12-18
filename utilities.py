# from z3 import *
# _x,x,x_,_y,y,y_,_z,z,z_,_pc,pc,pc_=Ints('_x x x_ _y y y_ _z z z_ _pc pc pc_')
from pysmt.shortcuts import *
from pysmt.operators import *

# P |= Q  ::=    P(X) <= Q(X)
def entailed(p,q):
    res = is_sat(And(p, Not(q)), solver_name="z3")
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
            if op == PLUS:
                op = MINUS
                VarInLLeft = True if var in lsub[0].get_free_variables() else False 
                if VarInLLeft:  # 确定在左子树的左树上
                    r1 = create_node(node_type=op, args=(rFormula, lsub[1]))
                    r2 = create_node(node_type=formula.node_type(), args=(lsub[0], r1))
                    return move_item(var, r2)
                else:           # 确定在左子树的右树上
                    r1 = create_node(node_type=op, args=(rFormula, lsub[0]))
                    r2 = create_node(node_type=formula.node_type(), args=(lsub[1], r1))
                    return move_item(var, r2)
            elif op == MINUS:
                VarInLLeft = True if var in lsub[0].get_free_variables() else False 
                if VarInLLeft:  # 确定在左子树的左树上
                    r1 = create_node(node_type=PLUS, args=(rFormula, lsub[1]))
                    r2 = create_node(node_type=formula.node_type(), args=(lsub[0], r1))
                    return move_item(var, r2)
                else:
                    r1 = create_node(node_type=PLUS, args=(rFormula, lsub[1]))
                    r2 = create_node(node_type=formula.node_type(), args=(lsub[0], r1))
                    return move_item(var, r2)
            elif op == TIMES:
                return formula
    else:           # 变量在右边怎么办
        rsub = rFormula.args()
        IsNull = True if len(rsub) == 0 else False
        if IsNull:   # 右子树没有叶子，只有这个变量
            if formula.node_type() == EQUALS:
                return create_node(node_type=EQUALS, args=(rFormula, lFormula))
            else:
                return formula
        else:
            op = rFormula.node_type()
            if op == PLUS:
                op = MINUS
                VARInRLeft = True if var in rsub[0].get_free_variables() else False
                if VARInRLeft:
                    r1 = create_node(node_type=op, args=(lFormula, rsub[1]))
                    r2 = create_node(node_type=formula.node_type(), args=(r1, rsub[0]))
                    return move_item(var, r2)
                else:
                    r1 = create_node(node_type=op, args=(lFormula, rsub[0]))
                    r2 = create_node(node_type=formula.node_type(), args=(r1, rsub[1]))
                    return move_item(var, r2)
            elif op == MINUS:
                VARInRLeft = True if var in rsub[0].get_free_variables() else False
                if VARInRLeft:
                    r1 = create_node(node_type=PLUS, args=(lFormula, rsub[1]))
                    r2 = create_node(node_type=formula.node_type(), args=(r1, rsub[1]))
                    return move_item(var, r2)
                else:
                    r1 = create_node(node_type=PLUS, args=(lFormula, rsub[1]))
                    r2 = create_node(node_type=formula.node_type(), args=(r1, rsub[0]))
                    return move_item(var, r2)
            elif op == TIMES:
                return formula

#eliminate a variables from a set of formulas
def eliminate_one(var, formulas):
    #search if ther is  anequation in expressions including var
    for formula in formulas:
        if formula.node_type() != EQUALS:   # 只要等式，非等式跳过
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

#eliminate_one(x,[x>y,x<z,x<pc])

# 返回替换对
def getSubtiPairList(VrasDict, New = "_var", Delete = "var"):
    # _x : New x : Delete x_ : 
    NewType = 9
    DeleteType = 9
    if "_" in New:
        if New[0] == "_":
            NewType = -1
        else:
            NewType = 1
        pass
    else:
        NewType = 0
    if "_" in Delete:
        if Delete[0] == "_":
            DeleteType = -1
        else:
            DeleteType = 1
        pass
    else:
        DeleteType = 0


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

def unchanged(Variables):
    result = []
    for var in Variables:
        result.append("%s==%s_" % (var, var))
    return result

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