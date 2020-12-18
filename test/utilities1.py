#!/usr/bin/env python2
# -*- coding: utf-8 -*-
"""
Created on Fri Nov  6 09:36:37 2020
some base functions for predicate abastract

@author: wendy
"""

from z3 import *
_x,x,x_,_y,y,y_,_z,z,z_,_pc,pc,pc_=Ints('_x x x_ _y y y_ _z z z_ _pc pc pc_')

#p->q true;else false
def entailed(p,q):
    s=z3.Solver()
    s.add(z3.Not(z3.Implies(p,q)))
    if s.check()==z3.unsat:
        return True
    else:
        return False

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
    Result = []
    p = str(var)
    Formula = str(formula).split(" ")
    Formula.insert(0, "+")
    op = ''    
    pOp = '' 
    pIndex = -1
    for index in range(len(Formula)):
        if Formula[index] in ["==", ">", ">=", "<", "<="]:
            op = Formula[index]
            pIndex = index
            break
 
    # == 符号后面可能是-1 也可能是+1 ，没有分开，需要写成["+", "1"]或者["-", "1"]
    if "+" in Formula[pIndex + 1]:
        tmpStr = Formula[pIndex + 1]
        Formula[pIndex + 1] = tmpStr[1:]
        Formula.insert(pIndex + 1, "+")
        Result = Formula[pIndex + 1:]
    elif "-" in Formula[pIndex + 1]:
        tmpStr = Formula[pIndex + 1]
        Formula[pIndex + 1] = tmpStr[1:]
        Formula.insert(pIndex + 1, "-")
        Result = Formula[pIndex + 1:]
    else:
        Result =["+"] + Formula[pIndex + 1:]


    for index in range(pIndex - 1, -1, -1):
        if Formula[index] == "+":
            Result.insert(0, "-")
        elif Formula[index] == "-":
            Result.insert(0, "+")
        else:
            Result.insert(0, Formula[index])
    Result.insert(0, op)

    for index in range(len(Result)):
        if Result[index] == p:
            pOp = Result[index-1]
            del Result[index]
            del Result[index-1]
            break

    Result.insert(0, p)
    if pOp == "+":
        Result.insert(0, "-")
    elif pOp == "-":
        Result.insert(0, "+")

    if Result[0] == "+":
        for index in range(len(Result)):
            if Result[index] in ["==", ">", ">=", "<", "<="]:
                if Result[index + 1] == "+":
                    del Result[index + 1]
                    break
        del Result[0]

    else:
        for index in range(len(Result)):
            if Result[index] in ["+", "-"]:
                if Result[index] == "+":
                    Result[index] = "-"
                else:
                    Result[index] = "+"
            if Result[index] in ["==", ">", ">=", "<", "<="]:
                if Result[index] == ">":
                    Result[index] = "<"
                elif Result[index] == ">=":
                    Result[index] = "<="
                elif Result[index] == "<":
                    Result[index] = ">"
                elif Result[index] == "<=":
                    Result[index] = ">="

        for index in range(len(Result)):
            if Result[index] in ["==", ">", ">=", "<", "<="]:
                if Result[index + 1] == "+":
                    del Result[index + 1]
                    break
        del Result[0]
    pass
    rFormula = eval(" ".join(Result))
    return(rFormula)

#eliminate a variables from a set of formulas
def eliminate_one(var, formulas):
    #search if ther is  anequation in expressions including var
    for k in formulas:
        if str(k.decl()) != "==":
            continue
        vs = get_vars(k)
        if var not in vs:
            continue
        #find the one
        formulas.remove(k)
        k=move_item(var,k)
        l=len(formulas)
        for j in range(l):
            vs=get_vars(formulas[j])
            if var not in vs:
                continue
            formulas[j]=z3poly.substitute(formulas[j],(var,k.arg(1)))
        return
    #not a equation including var
    choose=[]
    for k in formulas:
        vs=get_vars(k)
        if var not in vs:
            continue
        choose.append(k)
    l=len(choose)
    for j in range(l):
        formulas.remove(choose[j]) 
        choose[j]=move_item(var,choose[j])
    for j in range(l):             
        for i in range(j+1,l):
            if str(choose[j].decl()) in [">=",">"] and str(choose[i].decl()) in ["<=","<"]:
                if str(choose[j].decl())==">=" and str(choose[i].decl())=="<=":
                    formulas.append(choose[i].arg(1).__ge__(choose[j].arg(1)))
                else:
                    formulas.append(choose[i].arg(1).__gt__(choose[j].arg(1)))
            elif str(choose[i].decl()) in [">=",">"] and str(choose[j].decl()) in ["<=","<"]:
                if str(choose[i].decl())==">=" and str(choose[j].decl())=="<=":
                    formulas.append(choose[j].arg(1).__ge__(choose[i].arg(1)))
                else:
                    formulas.append(choose[j].arg(1).__gt__(choose[i].arg(1)))
    #print formulas

#eliminate_one(x,[x>y,x<z,x<pc])

#get all variables in p
def get_vars(p):
    r = []
    pChildren = p.children()
    if pChildren == []:
        if p.decl().kind() != z3.Z3_OP_ANUM:
            # print(p, p.sort())
            return [p]
    else:
        for child in pChildren:
            r= r + get_vars(child)
    return r

def str2Z3Expression(Vars, Formulas):
    pass