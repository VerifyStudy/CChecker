# -*- coding: utf-8 -*-
import copy
import datetime
from z3 import *

import ParseAST

from utilities import *

# Preds 全局变量
VarsDict, ALL_VARS, Preds, Transitions, Nodes = ParseAST.InitializedCFG()
State_init = copy.copy(Nodes[0])
State_err = copy.copy(Nodes[-2])
TrueConstant = TRUE()
FalseConstant = FALSE()
starttime = None
endtime = None


# subtitute pairs
sub1 = getSubtiPairList(VarsDict, "var", "var_")    # [V'/V]    inter
sub2 = getSubtiPairList(VarsDict, "var_", "_var")   # [V"/V']   connect1
sub3 = getSubtiPairList(VarsDict, "var", "_var")    # [V"/V]    post1 connect2
sub4 = getSubtiPairList(VarsDict, "var_", "var")    # [V/V']    post2

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
    # rho1(z3formula) :-> rho1(Transition)
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
        print("Error upon post's return is None")
        sys.exit(0)
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
# postSharp(phi3, rho4)

# AbstReach Function
def AbstReach():
    ReachStatesIDs = []
    headART = copy.copy(State_init)
    headART.z3Formula = alpha(headART.z3Formula)
    
    ReachStatesIDs.append(headART.ID)
    WorkList = [headART.ID]
    ARTTransitions = []

    while len(WorkList) > 0:
        tempID = WorkList[-1] # choose the last one from WorkList
        del WorkList[-1]
        for transID, trans in Transitions.items():
            if tempID != trans.fromState.ID:    # 过滤phi和rho
                continue
            phi_ = postSharp(Nodes[tempID].z3Formula, trans.z3Formulas)
            print("phi_", phi_)
            flag = True

            for stateID in ReachStatesIDs:
                if entailed(And(phi_), And(Nodes[stateID].z3Formula)):
                    flag = False
                    break
                
            if flag: # phi_ 对于ReachStates中所有的State 都不能蕴含
                toID = trans.toState.ID
                Nodes[toID].z3Formula = phi_
                ReachStatesIDs.append(toID)  # 可达状态
                ARTTransitions.append(transID)  # 转移集
                WorkList.append(toID)    # 临时池
    print("[ReachStates]", end=" ")
    for stateID in ReachStatesIDs:
        print(Nodes[stateID].z3Formula, end=" ")
    print()
    return ReachStatesIDs, ARTTransitions

def MakePath(fromID, ReachStates, ARTTransitions):
    Result = []
    Find = True
    while Find :
        Find = False
        for transID in ARTTransitions:
            if Transitions[transID].toState.ID == fromID:
                Result.append(transID)
                Find = True
                fromID = Transitions[transID].fromState.ID
                break
    return list(reversed(Result))
    # visited = {ID:False for ID, State in ReachStates.items()}
    # CEP = []
    # CEPs = []
    # MakePath(State, ReachStates, visited, CEP, CEPs)
    # return CEPs

# def MakePath(State, ReachStates, visited, CEP, CEPs):
#     visited[State.ID] = True
#     CEP.append(State.ID)
#     if len(State.preID) == 0:
#         CEPs.append(copy.deepcopy(list(reversed(CEP))))
#     else:
#         for ID in State.preID:
#             if visited[ID] == False:
#                 MakePath(ReachStates[ID], ReachStates, visited, CEP, CEPs)
#             else:
#                 visited[State.ID] = True
    
#     CEP.pop()
#     visited[State.ID] = False

# Feasible Path Function
def FeasiblePath(CEP):
    tmpPhi = State_init.z3Formula    #备份Phi_int
    for path in CEP:
        tmpState = post(tmpPhi,Transitions[path].z3Formulas)
    res = is_sat(And(tmpPhi + State_err.z3Formula), solver_name="z3")
    return res
    
# Refine Path Function
def RefinePath(CEP, State_init, State_err):
    # 计算插值过程不需要进行过滤检查，因为状态和转移关系一定是正确的
    phi_err = [substitute(p, sub1) for p in State_err.z3Formula]    # [V'/V]
    Result = []
    for i in range(len(CEP)):
        if i == 0:
            phi1 = copy.copy(State_init.z3Formula)
        else:
            phi1 = post([inter], Transitions[CEP[i - 1]].z3Formulas)
        
        tmpTrans = Transitions[CEP[i]].z3Formulas
        for j in range(1, len(CEP) - i):
            tmpTrans = connect_trans(tmpTrans, Transitions[CEP[j + i]].z3Formulas)
        phi2 = list(set(phi_err + tmpTrans))
        
        for VName, VZ3 in ALL_VARS.items():
            if "_" in VName:
                eliminate_one(VZ3, phi2)
        
        inter = craigInterpolant(phi1, phi2)
        print(inter)

        if inter not in Result:
            Result.append(inter)
        # 过滤 True 我认为谓词中不应该出现True和False
    return [p for p in Result if p is not TrueConstant]

# Computing Least Solution for refining predicates
def LeastSolution(State_init, counterExamplePath):
    StateResult = []
    for path in counterExamplePath:
        tmpState = post(State_init, Transitions[path].z3Formula)
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
        ReachStatesIDs, ARTTransitions = AbstReach()

        for stateID in ReachStatesIDs:
            res = is_sat(And(Nodes[stateID].z3Formula + State_err.z3Formula), solver_name="z3")
            if not res:
                continue
            flag = True
            CEP = MakePath(stateID, ReachStatesIDs, ARTTransitions)
                # 如果反例路径得到结果和State_err有交集，就输出反例路径
            if FeasiblePath(CEP):
                print("counter-example path:", CEP)
                return CEP
            else:
                print("counterExamplePath:", CEP)
                print("refining..")
                newPradicate = RefinePath(CEP, State_init, State_err)
                for np in newPradicate:
                    if np in Preds:
                        continue
                    else:
                        Preds.append(np)                

        print("[Preds]", Preds)
        if not flag:
            print("Preds Count:", len(Preds))
            return "program is correct"
    pass

starttime = datetime.datetime.now()
print(AbstRefineLoop())
endtime = datetime.datetime.now()
print("VerifyT:\t",endtime - starttime)