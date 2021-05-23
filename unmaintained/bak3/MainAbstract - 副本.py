# -*- coding: utf-8 -*-
import copy
import datetime
from z3 import *

import ParseAST

from utilities import *

# Preds 全局变量
VarsDict, ALL_VARS, Preds, TransList, StateList = ParseAST.InitializedCFG()
State_init = copy.copy(StateList[0])
State_err = copy.copy(StateList[-2])
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
##       ARTNode      ##
########################
class ARTNode(object):
    id = 0
    def __init__(self, stateID, z3Formula):
        self.ID= ARTNode.id
        self.stateID = stateID
        self.z3Formula = z3Formula
        self.labelID = None
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
# postSharp(phi3, rho4)

# AbstractReach Function
def AbstractReach():
    artHead = ARTNode(State_init.ID, alpha(State_init.z3Formula))
    ArtList[artHead.ID] = artHead
    WorkList = [artHead.ID]

    while len(WorkList) > 0:
        ArtID = WorkList[-1] # choose the last one state id from WorkList
        del WorkList[0]
        for transID in StateList[ArtList[ArtID].stateID].relatedRhoIDs: #抽象状态->状态栈->相关转移
            phi_ = postSharp(ArtList[ArtID].z3Formula, TransList[transID].z3Formulas)
            print("phi_", phi_)
            flag = True

            for ArtID, artState in ArtList.items():
                if entailed(And(phi_), And(artState.z3Formula)):
                    flag = False

                    break
                
            if flag: # phi_ 对于ART中所有的ArtState 都不能蕴含
                tmpArtState = ARTNode(TransList[transID].toStateID, phi_)
                ArtList[tmpArtState.ID] = copy.deepcopy(tmpArtState)    #加入ART栈
                WorkList.append(tmpArtState.ID)    # 临时池

    print("Abstract Reachability Tree Stack")
    for ArtID, artState in ArtList.items():
        print("Id:",ArtID," formula:", artState.z3Formula," label:",artState.labelID)

def MakePath(fromID, ReachStates, ARTTransitions):
    Result = []
    Find = True
    while Find :
        Find = False
        for transID in ARTTransitions:
            if TransList[transID].toState.ID == fromID:
                Result.append(transID)
                Find = True
                fromID = TransList[transID].fromState.ID
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
    for rhoId in CEP:
        tmpState = post(tmpPhi,TransList[rhoId].z3Formulas)
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
    return [p for p in Result if p is not TrueConstant]

# Computing Least Solution for refining predicates
def LeastSolution(CEP):
    tmpPhi = State_init.z3Formula    #备份Phi_int
    StateResult = []
    for rhoId in CEP:
        tmpState = post(State_init, TransList[rhoId].z3Formula)
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

        # for ArtID, artState in ArtList.items():
        #     res = is_sat(And(artState.z3Formula + State_err.z3Formula), solver_name="z3")
        #     if not res:
        #         continue
        #     flag = True
        #     CEP = MakePath(stateID, ReachStatesIDs, ARTTransitions)
        #         # 如果反例路径得到结果和State_err有交集，就输出反例路径
        #     if FeasiblePath(CEP):
        #         print("counter-example path:", CEP)
        #         return CEP
        #     else:
        #         print("counterExamplePath:", CEP)
        #         print("refining..")
        #         newPradicate = RefinePath(CEP, State_init, State_err)
        #         for np in newPradicate:
        #             if np in Preds:
        #                 continue
        #             else:
        #                 Preds.append(np)                

        print("[Preds]", Preds)
        if not flag:
            print("Preds Count:", len(Preds))
            return "program is correct"
    pass

starttime = datetime.datetime.now()
print(AbstRefineLoop())
endtime = datetime.datetime.now()
print("VerifyT:\t",endtime - starttime)