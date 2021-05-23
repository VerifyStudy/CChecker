# -*- coding: utf-8 -*-
from z3 import *
import copy
from utilities1 import *
#variables
_x,x,x_,_y,y,y_,_z,z,z_,_pc,pc,pc_=Ints('_x x x_ _y y y_ _z z z_ _pc pc pc_')
V = [Ints('_x x x_ _y y y_ _z z z_ _pc pc pc_')]
#transaction
Trans = {1: [pc == 1, pc_ == 2, y >= z,     x == x_,     y == y_, z == z_],
         2: [pc == 2, pc_ == 3, x < y,      x == x_,     y == y_, z == z_],
         3: [pc == 3, pc_ == 2, x_ == x + 1,y == y_, z == z_],
         3: [pc == 2, pc_ == 4, x >= y,     x == x_,     y == y_, z == z_],
         4: [pc == 4, pc_ == 5, x >= z,     x == x_,     y == y_, z == z_],
         5: [pc == 4, pc_ == 6, x + 1 <= z, x == x_,     y == y_, z == z_]
        }
#predicates
Preds = [pc == 1, pc == 2, pc == 3, pc == 4, pc == 5, pc == 6]
#all variables
ALL_VARS=["_x","x","x_","y","_y","y_","z","z_","_z","pc","pc_","_pc"]
ERROR   = pc == 6
INIT    = [pc == 1]
Phi_init = [pc == 1]
Phi_err = [pc == 6, x < z]
sub1 = [(x,x_),(y,y_),(z,z_),(pc,pc_)]
sub2 = [(x_, _x), (y_, _y), (z_, _z),(pc_, _pc)]
sub3 = [(x, _x), (y, _y), (z, _z),(pc, _pc)]
sub4 = [(x_,x),(y_,y),(z_,z),(pc_,pc)]  # [V/V']
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
    s = Solver()
    s.add(And(phi1 + phi2))
    if s.check() == z3.sat:
        return True
    else:
        return False

########################
##     Termination    ##
########################

# relational composition ρ o ρ
def connect_trans(rho1, rho2):

    # rho如果不是连着的，就不能最ρ连接
    pcSet = [p.arg(1) for p in rho1 + rho2 if p.arg(0) == pc or p.arg(0) == pc_]
    if len(list(set(pcSet))) != 3:
        print("Error linking problem in pc and pc_ of rho1 and rho2")
        print("rho1:", rho1)
        print("rho2:", rho2)
        sys.exit(0)

    # substitute variables
    rho1 = [z3.substitute(p, sub2) for p in rho1]   # [V"/V']
    rho2 = [z3.substitute(p, sub3) for p in rho2]   # [V"/V]
 
    rho1=list(set(rho1+rho2))
    for VName in ALL_VARS:
        if VName.startswith("_"):
            eliminate_one(eval(VName), rho1)

    return rho1

########################
##       Safety       ##
########################

# post condition Function
def post(phi,rho):
    if phi is None:
        print("Error upon post's return is None")
        sys.exit(0)

    # phi只能沿着该状态的可能出发路线移动
    # 如果点和边不对应就返回None
    pcSet = [p.arg(1) for p in phi + rho if p.arg(0) == pc]
    if len(list(set(pcSet))) > 1:
        return None

    phi = [z3.substitute(p, sub3) for p in phi]    # [V"/V]
    rho = [z3.substitute(p, sub3) for p in rho]    # [V"/V]
    rho = [z3.substitute(p, sub4) for p in rho]    # [V/V']

    phi=list(set(phi + rho))
    for VName in ALL_VARS:
        if "_" in VName:
            eliminate_one(eval(VName), phi)

    return phi

# α function
def alpha(phi):
    if phi is None:
        return None
        
    result = []
    
    for p in Preds: # This is an error !!!
        if entailed(And(phi), p):
            result.append(p)
    if len(result) == 0:
        return [False]

    return result


# post# post condition supset
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
            phi_ = postSharp(phi, rho)
            if phi_ is None:
                continue
            print("phi_", phi_)
            flag = True
            for ReachState in ReachStates:
                if entailed(And(phi_), And(ReachState)):
                    flag = False
                    break
            
            if flag: # If phi' |!= V ReachStates is True
                ReachStates.append(phi_)
                Parent.append([phi, Id, phi_])
                WorkList.append(phi_)

    return ReachStates, Parent

# 从Root到Phi的路径
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
def FeasiblePath(counterExamplePath):
    tmpPhi = copy.copy(Phi_init)
    for path in counterExamplePath:
        tmpPhi = post(tmpPhi,Trans[path])
    return isIntersection(tmpPhi, Phi_err)
    
# Refine Path Function
def RefinePath(counterExamplePath,):
    return inter(len(counterExamplePath), counterExamplePath)
    # return LeastSolution(phi_init, counterExamplePath, Trans)

# Computing Least Solution for refining predicates
def LeastSolution(phi_init, counterExamplePath, Trans):
    phiResult = []
    for path in counterExamplePath:
        tmp = post(phi_init, Trans[path])
        phiResult = phiResult + tmp
    return phiResult
    pass

# inter Function for refining predicates
# return refined predicates [True, x > z, y > z, False]
def inter(cut, path, Result = []):
    if cut > len(path) or cut < 0:
        print("Error in inter")
        return
    if cut==len(path):
        phi2 = [z3.substitute(ERROR, sub1)]
    else:
        phi2 = Trans[path[cut]]
        for i in range(cut+1,len(path)):
            phi2=connect_trans(phi2, Trans[path[i]])
        if False in phi2:
            # Result.append(True)
            return [True]
        phi2.append(z3.substitute(ERROR, sub1))
    
    if cut==0:
        phi1=INIT
    else:
        phi1=post(inter(cut-1, path, Result),Trans[path[cut-1]])
        if False in phi1:
            Result.append(False)
            return Result
    phi1=list(set(phi1))
    phi2=list(set(phi2))
    for VName in ALL_VARS:
          if "_" in VName:
              eliminate_one(eval(VName), phi1)
              eliminate_one(eval(VName), phi2)

    v1 = [v for p in phi1 for v in get_vars(p)]
    v1=list(set(v1))
    v2 = [v for p in phi2 for v in get_vars(p)]
    v2=list(set(v2))
    for a in v1:
        if a not in v2:
            eliminate_one(a, phi1)
    s=z3.Solver()
    s.add(phi2)
    for a in phi1:
        if a in phi2:
            continue
        s.add(a)
        if s.check() == z3.unsat:
            Preds.append(a)
            s.reset()
            print(a)
            Result.append(a)
            return [a]
        s.pop()

    return Result

# AbstRefindLoop Function
def AbstRefineLoop():
    
    while True:
        flag = False
        ReachStates, Parent = AbstReach()
        print("[ReachStates]", ReachStates)
        for Phi in ReachStates:
            if not isIntersection(Phi, Phi_err):
                continue
            flag = True
            counterExamplePath = MakePath(Phi, Parent)

            # 如果反例路径得到结果和phi_err有交集，就输出反例路径
            if FeasiblePath(counterExamplePath):
                print("counter-example path:", counterExamplePath)
                return counterExamplePath
            else:
                print("counterExamplePath:", counterExamplePath)
                print("refining..")
                newPradicate = RefinePath(counterExamplePath)
                for np in newPradicate:
                    if np in Preds:
                        continue
                    else:
                        Preds.append(np)
                continue
            break

        print("[Preds]", Preds)
        if not flag:
            return "program is correct"
    pass

print(AbstRefineLoop())
        

