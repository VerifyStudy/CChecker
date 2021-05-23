# Checking satisfiability of a formula.
#
# This example shows:
#  1. How to build a formula
#  2. How to perform substitution
#  3. Printing
#  4. Satisfiability checking
from pysmt.shortcuts import *
from pysmt.typing import REAL, INT
from pysmt.fnode import FNode
from pysmt.operators import *
import copy

x, y, z = Symbol("x", INT), Symbol("y", INT), Symbol("z", INT)
m, n = Symbol("n", INT), Symbol("n", INT)


create_node = get_env().formula_manager.create_node

def func(var, formula):
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
                    return func(var, r2)
                else:           # 确定在左子树的右树上
                    r1 = create_node(node_type=op, args=(rFormula, lsub[0]))
                    r2 = create_node(node_type=formula.node_type(), args=(lsub[1], r1))
                    return func(var, r2)
            elif op == MINUS:
                VarInLLeft = True if var in lsub[0].get_free_variables() else False 
                if VarInLLeft:  # 确定在左子树的左树上
                    r1 = create_node(node_type=PLUS, args=(rFormula, lsub[1]))
                    r2 = create_node(node_type=formula.node_type(), args=(lsub[0], r1))
                    return func(var, r2)
                else:
                    r1 = create_node(node_type=PLUS, args=(rFormula, lsub[1]))
                    r2 = create_node(node_type=formula.node_type(), args=(lsub[0], r1))
                    return func(var, r2)
                pass
    else:           # 变量在右边怎么办
        rsub = rFormula.args()
        IsNull = True if len(rsub) == 0 else False
        if IsNull:   # 右子树没有叶子，只有这个变量
            return formula
        else:
            op = rFormula.node_type()
            if op == PLUS:
                op = MINUS
                VARInRLeft = True if var in rsub[0].get_free_variables() else False
                if VARInRLeft:
                    r1 = create_node(node_type=op, args=(lFormula, rsub[1]))
                    r2 = create_node(node_type=formula.node_type(), args=(r1, rsub[0]))
                    return func(var, r2)
                else:
                    r1 = create_node(node_type=op, args=(lFormula, rsub[0]))
                    r2 = create_node(node_type=formula.node_type(), args=(r1, rsub[1]))
                    return func(var, r2)
            elif op == MINUS:
                VARInRLeft = True if var in rsub[0].get_free_variables() else False
                if VARInRLeft:
                    r1 = create_node(node_type=PLUS, args=(lFormula, rsub[1]))
                    r2 = create_node(node_type=formula.node_type(), args=(r1, rsub[1]))
                    return func(var, r2)
                else:
                    r1 = create_node(node_type=PLUS, args=(lFormula, rsub[1]))
                    r2 = create_node(node_type=formula.node_type(), args=(r1, rsub[0]))
                    return func(var, r2)

# print(func(x, Equals(x+y,z)))
# print(func(x, Equals(x-y,z)))
# print(func(y, Equals(x+y,z)))
# print(func(y, Equals(x-y,z)))
f1 = Equals(x,y)
f2 = copy.deepcopy(f1)
print(f2.substitute({y:z}))
print(f1.substitute({y:z}))
