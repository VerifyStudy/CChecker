# -*- coding: utf-8 -*-
from z3 import *
import copy

import ParseAST

from utilities import *

# Preds 全局变量
VarsDict, ALL_VARS, Preds, Trans, Phi_init, Phi_err, AssumeTrans, Assume_init, Assume_verify= ParseAST.InitializedCFG()
TrueConstant = TRUE()
FalseConstant = FALSE()
# subtitute pairs
sub1 = getSubtiPairList(VarsDict, "var", "var_")    # [V'/V]    inter
sub2 = getSubtiPairList(VarsDict, "var_", "_var")   # [V"/V']   connect1
sub3 = getSubtiPairList(VarsDict, "var", "_var")    # [V"/V]    post1 connect2
sub4 = getSubtiPairList(VarsDict, "var_", "var")    # [V/V']    post2

print("Sub Pairs")
print("[V'/V]", end=" ")
print(sub1)      # [V'/V]
print("[V\"/V']", end=" ")
print(sub2)      # [V"/V']
print("[V\"/V]", end=" ")
print(sub3)      # [V"/V]
print("[V/V']", end=" ")
print(sub4)      # [V/V']

########################
##     Termination    ##
########################

# relational composition ρ o ρ
def connect_trans(rho1, rho2):
    if FalseConstant in rho1 + rho2:
        print("Error! False in formula rho1 or rho2")
        sys.exit(0)

    # rho如果不是连着的，就不能进行ρ连接，返回[False]
    pcSet = [p.arg(1) for p in rho1 + rho2 if p.arg(0) == ALL_VARS["pc"] or p.arg(0) == ALL_VARS["pc_"]]
    if len(list(set(pcSet))) != 3:
        print("Error linking problem in pc and pc_ of rho1 and rho2")
        print("rho1:", rho1)
        print("rho2:", rho2)
        sys.exit(0)

    # substitute variables
    rho1 = [substitute(p, sub2) for p in rho1]  # [V"/V']
    rho2 = [substitute(p, sub3) for p in rho2]  # [V"/V]
 
    rho1=list(set(rho1+rho2))
    for VName, VZ3 in ALL_VARS.items():
        if VName.startswith("_"):
            eliminate_one(VZ3, rho1)

    return rho1

########################
##       Safety       ##
########################

# post condition Function
def post(phi, rho):
    if phi is None:
        print("Error upon post's return is None")
        sys.exit(0)

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
    pcSet = [str(p.arg(1)) for p in phi + rho if p.arg(0) == ALL_VARS["pc"]]
    if len(list(set(pcSet))) > 1:
        return None
    phi = [substitute(p, sub3) for p in phi]    # [V"/V]
    rho = [substitute(p, sub3) for p in rho]    # [V"/V]
    rho = [substitute(p, sub4) for p in rho]    # [V/V']

    phi=list(set(phi + rho))
    for VName, VZ3 in ALL_VARS.items():
        if "_" in VName:
            eliminate_one(VZ3, phi)
    return phi

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
        return [False]
    return result

# post condition supset
def postSharp(phi, rho):
    return alpha(post(phi, rho))
# postSharp(phi3, rho4)

# AbstReach Function
def AbstReach():
    ReachStates = [alpha(Phi_init)]
    WorkList = [alpha(Phi_init)]
    Parent = []

    while len(WorkList) > 0:
        phi = WorkList[-1] # choose the last one from WorkList
        del WorkList[-1]
        for Id, rho in Trans.items():
            print("phi", phi, "rho", rho)
            phi_ = postSharp(phi, rho)
            if phi_ is None:
                continue
            print("phi_", phi_)
            flag = True
            for ReachState in ReachStates:
                if entailed(And(phi_), And(ReachState)):
                    flag = False
                    break
                
            if flag: # phi_ 对于ReachStates中所有的State 都不能蕴含
                ReachStates.append(phi_)
                Parent.append([phi, Id, phi_])
                WorkList.append(phi_)

    return ReachStates, Parent

def MakePath(Phi, Parent):
    Parent = copy.deepcopy(Parent)
    phi_ = copy.deepcopy(Phi)

    path = []
    findEnd = False # 表示没有找完，没有找到根结点

    # 没有找到就停止，每次找之前都假定已经找到了
    while not findEnd:
        findEnd = True
        for index, parent in enumerate(Parent):
            if str(phi_) == str(parent[-1]):
                path.insert(0, parent[1]) 
                del Parent[index]
                findEnd = False
                phi_ = parent[0]           
    return path
    pass

# Feasible Path Function
def FeasiblePath(Phi_init, counterExamplePath):
    tmpPhi = copy.copy(Phi_init)    #备份Phi_int
    for path in counterExamplePath:
        tmpPhi = post(tmpPhi,Trans[path])
    res = is_sat(And(tmpPhi + Phi_err), solver_name="z3")
    return res
    
# Refine Path Function
def RefinePath(counterExamplePath, phi_init, phi_err):
    Phi_err = [substitute(p, sub1) for p in phi_err]    # [V'/V]
    Result = []
    for i in range(len(counterExamplePath)):
        if i == 0:
            phi1 = copy.copy(phi_init)
        else:
            phi1 = post([inter], Trans[counterExamplePath[i - 1]])
        
        phi2 = copy.copy(Trans[counterExamplePath[i]])
        for j in range(1, len(counterExamplePath) - i):
            phi2 = connect_trans(phi2, Trans[counterExamplePath[j + i]])
        phi2 += Phi_err
        phi2 = list(set(phi2))
        for VName, VZ3 in ALL_VARS.items():
            if "_" in VName:
                eliminate_one(VZ3, phi2)
        inter = craigInterpolant(phi1, phi2)
        print(inter)
        if inter.is_true():
            pass
        else:
            Result.append(inter)
    return Result

# Computing Least Solution for refining predicates
def LeastSolution(phi_init, counterExamplePath):
    phiResult = []
    for path in counterExamplePath:
        tmp = post(phi_init, Trans[path])
        phiResult = phiResult + tmp
    return phiResult
    pass

def craigInterpolant(formulaA, formulaB):
    # 插值计算时候，去掉pc
    itp = Interpolator(name="msat")
    print("phi1 = ", end="")
    print(formulaA)
    print("phi2 = ", end="")
    print(formulaB)
    formulaANoPc = [formula for formula in formulaA if formula.arg(0) != ALL_VARS["pc"]]
    formulaBNoPc = [formula for formula in formulaB if formula.arg(0) != ALL_VARS["pc"]]
    inter = itp.binary_interpolant(And(formulaANoPc), And(formulaBNoPc))
    return inter

def assumeVerify(Phi_init = Assume_init, Trans = AssumeTrans, Phi_verify = Assume_verify):
    # Assume的简单验证，只要能post到达即可
    path = list(AssumeTrans.keys())
    tmpPhi = copy.copy(Phi_init)
    for i in range(len(path)):
        tmpPhi = post(tmpPhi, AssumeTrans[path[i]])
    res = is_sat(And(tmpPhi + Assume_verify), solver_name="z3")
    return res

# AbstRefindLoop Function
def AbstRefineLoop():
    if not assumeVerify():
        print("Error! assume not verified")
        sys.exit(0)
    print("assume is verified")

    while True:
        flag = False
        ReachStates, Parent = AbstReach()
        print("[ReachStates]", ReachStates)
        for Phi in ReachStates:
            res = is_sat(And(Phi + Phi_err), solver_name="z3")
            if not res:
                continue
            flag = True
            counterExamplePath = MakePath(Phi, Parent)

            # 如果反例路径得到结果和phi_err有交集，就输出反例路径
            if FeasiblePath(Phi_init, counterExamplePath):
                print("counter-example path:", counterExamplePath)
                return counterExamplePath
            else:
                print("counterExamplePath:", counterExamplePath)
                print("refining..")
                newPradicate = RefinePath(counterExamplePath, Phi_init, Phi_err)
                for np in newPradicate:
                    if np in Preds:
                        continue
                    else:
                        Preds.append(np)
                continue

        print("[Preds]", Preds)
        if not flag:
            return "program is correct"
    pass

print(AbstRefineLoop())
        

