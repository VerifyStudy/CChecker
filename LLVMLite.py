from llvmlite import ir
from llvmlite import binding as llvm
import re
import copy
from z3 import *

ir = ""
with open('./test/whileifoutput.ll', 'r') as f:
# with open('output.ll', 'r') as f:
    ir = f.read()
    # mod = llvm.module.parse_assembly(f_read)

BlockInfoList = []
InstructionInfoList = []
BlockLabel = dict()

ConditionList = []
UpInstructions = []
PhiPool = {}    #["blockName":[{"phiID" : 1, "line" : 1}, {"PhiID" : 2, "line" : 2}]]

Trans = []
PhiPc = -1

class State(object):
    def __init__(self, block, block_, pred, formula, pc, pc_ = None):
        self.block = block
        self.block_ = block_
        self.pred = pred
        self.formula = formula
        self.pc = pc
        self.pc_ = pc_
        pass

class PhiState(object):
    def __init__(self, point):
        self.ID = 0
        self.point = point

def showBlocks():
    for Block in BlockInfoList:
        print("line ", Block.line, "\t\tlastLine ", Block.lastLine, "\tlabel ",Block.label, "\t\tpreds ", Block.preds)


def showInstructions():
    print(InstructionInfoList)

def printList(list):
    for x in list:
        print(x)

def findblock(valueRef, kFunction):
    for x in kFunction.blocks:
        if str(valueRef) == str(x.valuered):
            return x

def getListFromIter(iter):
    list = []
    for x in iter:
        list.append(x)
    return list

mod = llvm.module.parse_assembly(ir)

def TraversIR(ModuleRef):
    Functions = getListFromIter(ModuleRef.functions)
    for Function in Functions:
        if Function.name == "main":
            print("[TraversFunction]: main")
            TraversFunction(Function)
    pass

def TraversFunction(Function):
    Blocks = getListFromIter(Function.blocks)
    blockId = 0

    # 给所有Blocks添加label, preds 和 遍历标志isTrave
    for Block in Blocks:
        Block.label, Block.preds = getBlockLabelAndPreds(Block)
        BlockInfoList.append(Block)
        BlockLabel[Block.label] = str(blockId)
        blockId += 1

    for index in range(len(BlockInfoList)):
        BlockInfoList[index].line, BlockInfoList[index].lastLine = getBlockFirstAndLastLine(BlockInfoList, BlockInfoList[index])
        BlockInfoList[index].isTrave = False
    showBlocks()
    print("Initialized Finished")
    for index in range(len(BlockInfoList)):
        if not BlockInfoList[index].isTrave:
            BlockInfoList[index].isTrave = True
            TraversBlock(BlockInfoList, BlockInfoList[index])

    if len(UpInstructions) > 0:
        for i in range(len(UpInstructions)):
            Trans.append(copy.deepcopy(UpInstructions[i]))
    pass

def TraversBlock(Blocks, Block, Flag = True):
    # print(Block.label)
    global PhiPc
    global UpInstructions
    global ConditionList
    Instructions = getListFromIter(Block.instructions)

    for Instruction in Instructions:
        Opcode = Instruction.opcode
        OpcodeStr = str(Opcode)

        if OpcodeStr == "ret":
            line = getRetLine(ir, Instruction)
            if Flag:
                if len(UpInstructions) > 0:
                    for i in range(len(UpInstructions)):
                        UpInstructions[i].pc_ = line
                        UpInstructions[i].block_ = Block.label
                        Trans.append(copy.deepcopy(UpInstructions[i]))
                    UpInstructions = []
            else:
                ConditionList[-1].pc_ = line
                ConditionList[-1].block_ = Block.label
                Trans.append(copy.deepcopy(ConditionList[-1]))
                del ConditionList[-1]
                
        if OpcodeStr == "br":
            # print(OpcodeStr)
            label1, label2 = parseBrInstruction(Instruction)
            Block1 = findBlock(Blocks,label1)

            if not Block1.isTrave:
                Block1.isTrave = True
                TraversBlock(Blocks, Block1)
            else:   # 如果Block1已经遍历，只需要拿到Block1的首行
                line = getNextBlockLine(Blocks, label1)
                if Flag:
                    if len(UpInstructions) > 0:
                        for i in range(len(UpInstructions)):
                            UpInstructions[i].pc_ = line
                            UpInstructions[i].block_ = Block.label
                            Trans.append(copy.deepcopy(UpInstructions[i]))
                        UpInstructions = []
                else:
                    ConditionList[-1].pc_ = line
                    ConditionList[-1].block_ = Block.label
                    Trans.append(copy.deepcopy(ConditionList[-1]))
                    del ConditionList[-1]                    

            if label2 is not None: # Not Condition
                Block2 = findBlock(Blocks,label2)
                if not Block2.isTrave:
                    Block.isTrave = True
                    TraversBlock(Blocks, Block2, False)

        if OpcodeStr == "add":
            # print(OpcodeStr)
            result, op1, op2 = parseAddInstruction(Instruction)
            ParentBlock = findBlock(Blocks, Block.label)
            line = getAddLine(ir,Instruction)

            if Flag:
                if len(UpInstructions) > 0:
                    for i in range(len(UpInstructions)):
                        UpInstructions[i].pc_ = line
                        UpInstructions[i].block_ = Block.label
                        Trans.append(copy.deepcopy(UpInstructions[i]))
                    UpInstructions = []
                    pass
                tmpState = State(Block.label, None, Block.label, [result, "==", op1, "+", op2], pc = line)
                UpInstructions.append(tmpState)
            else:
                ConditionList[-1].pc_ = line
                ConditionList[-1].block_ = Block.label
                Trans.append(copy.deepcopy(ConditionList[-1]))
                del ConditionList[-1]
        
        if OpcodeStr == "phi":
            # print(OpcodeStr)
            result, ValLabel = parsePhiInstruction(Instruction)
            # print("phi ", AddResult, VarPreds)
            # print("phi From Block",Block.label, " To Block", ParentBlock.label)
            
            if Flag:
                if len(UpInstructions) > 0:
                    for i in range(len(UpInstructions)):
                        UpInstructions[i].pc_ =getPhiLine(Block.label, result)
                        UpInstructions[i].block_ = Block.label
                        Trans.append(copy.deepcopy(UpInstructions[i]))
                    UpInstructions = []       
                for varlabel in ValLabel:
                    tmpState = State(block = Block.label, block_ = None, pred = varlabel['label'], formula = [result, "==", varlabel['var']], pc = getPhiLine(Block.label, result))
                    UpInstructions.append(copy.deepcopy(tmpState))
            else:
                ConditionList[-1].pc_ = getPhiLine(Block.label, result)
                ConditionList[-1].block_ = Block.label
                Trans.append(copy.deepcopy(ConditionList[-1]))
                del ConditionList[-1]
        
        if OpcodeStr == "icmp":
            # print(OpcodeStr)
            cond, op1, op2 = parseIcmpInstruction(Instruction)
            ParentBlock = findBlock(Blocks, Block.label)
            line = getIcmpLine(ir, Instruction)
            
            if Flag:
                if len(UpInstructions) > 0:
                    for i in range(len(UpInstructions)):
                        UpInstructions[i].pc_ = line
                        UpInstructions[i].block_ = Block.label
                        Trans.append(copy.deepcopy(UpInstructions[i]))
                    UpInstructions = []
                tmpState1 = State(Block.label, None, Block.label, [op1, cond, op2], pc = line)
                tmpState2 = State(Block.label, None, Block.label, [op1, getReverseOpcode(cond), op2], pc = line)
                UpInstructions.append(tmpState1)
                ConditionList.append(tmpState2)
            else:
                ConditionList[-1].pc_ = line
                ConditionList[-1].block_ = Block.label
                Trans.append(copy.deepcopy(ConditionList[-1]))
                del ConditionList[-1]                

        Flag = True

# return Block.label Block.preds Block.line Block.lastLine
def getBlockLabelAndPreds(Block):
    global PhiPc
    label       = ""        # Block.label
    preds       = []        # Block.preds
    line        = -1        # Block.line
    lastLine    = -1        # Block.lastLine
    blockStr = str(Block)
    tmpSplit1 = blockStr.split("\n")
    tmpSplit2 = tmpSplit1[1].split(":")

    tmpStr1 = tmpSplit2[0]
    label = "%" + tmpStr1 
    tmpStr2 = tmpSplit2[1].strip()

    Instructions = getListFromIter(Block.instructions)
    # 给每个块添加一个行号和一个最后行号
    # 将来，如果有一个phi结点，他的前屈就是上一个块的最后行号。
    # 对于第一个块，他没有前驱，他的行号就是0
    # 给每个Phi结点添加一个行号，不适用自增对象动态添加。
    # 创建一个管理Phi结点的池子，这里保存每个Phi结点和他对应的行号
    # 否则就需要研究Block的构造，在迭代器中修改对象，添加行号
    for Instruction in Instructions:
        Opcode = Instruction.opcode
        OpcodeStr = str(Opcode)
        if OpcodeStr == "phi":
            result, ValLabel = parsePhiInstruction(Instruction)
            if label in PhiPool:
                PhiPool[label].append({"phiID" : result, "line" : PhiPc})
            else:
                PhiPool[label] = [{"phiID" : result, "line" : PhiPc}]
            PhiPc -= 1

    if tmpStr2 == '':
        return label, preds
    else:
        tmpSplit3 = tmpSplit2[1].split("=")
        preds = [pred.strip() for pred in tmpSplit3[1].split(",")]
        return label, preds
        pass

def getBlockFirstAndLastLine(Blocks, Block):
    Instructions = getListFromIter(Block.instructions)
    # 如果这个块只有1条指令，那一定是br，
    # 一个块一定有一个br指令，并且br在末尾
    # 这种情况我就把他看成无效块

    line = -10      # 块第一条指令位置
    lastLine = -10  # 块最后一条指令位置

    # 这是第一个块，没有preds， 默认为0
    if len(Block.preds) == 0:
        line = 0
        lastLine = 0
        return line, lastLine
    # 如果只有一条指令，那可以删去，使用-1表示
    if len(Instructions) == 1:
        if str(Instructions[0].opcode) == "br":
            return None, None
        else:
            return line, lastLine
    
    firstInstruction    = Instructions[0]
    lastInstruction     = Instructions[-2]
    
    firstInstrOpcodeStr = str(firstInstruction.opcode)
    lastInstrOpcodeStr  = str(lastInstruction.opcode)
    
    if firstInstrOpcodeStr == "add":
        line = getAddLine(ir, firstInstruction)
    elif firstInstrOpcodeStr == "icmp":
        line = getIcmpLine(ir, firstInstruction)   
    elif firstInstrOpcodeStr == "phi":
        line = PhiPool[Block.label][0]["line"]        

    if lastInstrOpcodeStr == "add":
        lastLine = getAddLine(ir, lastInstruction)
    elif lastInstrOpcodeStr == "icmp":
        lastLine = getIcmpLine(ir, lastInstruction)
    elif lastInstrOpcodeStr == "phi":
        lastLine = PhiPool[Block.label][-1]["line"] 
    
    return line, lastLine

def getNextBlockLine(Blocks, label):
    for Block in Blocks:
        if Block.label == label:
            return Block.line
    pass

# br instruction
def parseBrInstruction(Instruction):
    instructionStr = str(Instruction)
    label1 = ""
    label2 = ""
    tmpSplit1 = instructionStr.split(",")
    if len(tmpSplit1) == 4:  #br i1 <cond>, label <iftrue>, label <iffalse>
        tmpSplit2 = tmpSplit1[1].split(" ")
        tmpSplit3 = tmpSplit1[2].split(" ")
        label1 = tmpSplit2[-1]
        label2 = tmpSplit3[-1]
        return label1, label2
        pass
    elif len(tmpSplit1) == 3: # br label <dest>          ; Unconditional branch
        tmpSplit2 = tmpSplit1[0].split(" ")
        label1 = tmpSplit2[-1]
        return label1, None
    elif len(tmpSplit1) == 2: # br not llvm loop
        tmpSplit2 = tmpSplit1[0].split(" ")
        label1 = tmpSplit2[-1]
        return label1, None        
    elif len(tmpSplit1) == 1: # br label %if.end  No debg flag
        tmpSplit2 = tmpSplit1[0].split(" ")
        for index, word in enumerate(tmpSplit2):
            if word == "label":
                return tmpSplit2[index + 1], None
        pass
    else:
        print("Error Can't parse br instruction")
        return None, None
    pass

# add instruction
def parseAddInstruction(Instruction):
    instructionStr = str(Instruction)
    tmpSplit1 = instructionStr.split(",")
    tmpSplit2 = tmpSplit1[0].split(" ")
    tmpSplit3 = tmpSplit1[1].split(" ")

    result = tmpSplit2[2]
    op1 = tmpSplit2[-1]
    op2 = tmpSplit3[-1]
    # print(tmpSplit2[0], tmpSplit2[-1], tmpSplit3[-1])

    return lastFormat(result), lastFormat(op1), lastFormat(op2)
    pass

# phi instruction
def parsePhiInstruction(Instruction):
    instructionStr = str(Instruction)
    tmpSplit1 = instructionStr.split("=")
    result = tmpSplit1[0].strip()
    phiNodes = re.findall(r'\[.*?\]', tmpSplit1[1])
    VarLabels = []
    for phiNode in phiNodes:
        tmpSplit = phiNode.split(",")
        var = tmpSplit[0]
        label = tmpSplit[1]
        VarLabels.append({"var" : lastFormat(var[2:]), "label" : label[1:-2]})
    return lastFormat(result), VarLabels
    pass

# icmp instruction
def parseIcmpInstruction(Instruction):
    instructionStr = str(Instruction)
    tmpSplit1 = instructionStr.split(",")
    tmpSplit2 = tmpSplit1[0].split(" ")
    tmpSplit3 = tmpSplit1[1].split(" ")

    cond = tmpSplit2[5]
    op1 = tmpSplit2[-1]
    op2 = tmpSplit3[-1]
    # print(cond, op1, op2)

    return conditonCode2Char(cond), lastFormat(op1), lastFormat(op2)
    pass

def findBlock(Blocks, label):
    for index in range(len(Blocks)):
        if Blocks[index].label == label:
            # print("parent", label)
            return Blocks[index]

def getAddLine(ir, Instruction):
    instructionStr = str(Instruction)
    findAll = re.findall(r'!dbg .*', instructionStr)
    dbg = findAll[0]
    dbg = dbg[5:]
    # print(dbg)
    findAll = re.findall(dbg + ".*", ir)
    findAll = re.findall(r'line: .*?,',findAll[1])
    line = findAll[0]
    line = line[6:-1]
    # print("line", line)
    return line
    pass

def getIcmpLine(ir, Instruction):
    instructionStr = str(Instruction)
    findAll = re.findall(r'!dbg .*', instructionStr)
    dbg = findAll[0]
    dbg = dbg[5:]
    # print(dbg)
    findAll = re.findall(dbg + ".*", ir)
    findAll = re.findall(r'line: .*?,',findAll[1])
    line = findAll[0]
    line = line[6:-1]
    # print("line", line)
    return line

def getRetLine(ir, Instruction):
    instructionStr = str(Instruction)
    findAll = re.findall(r'!dbg.*', instructionStr)
    dbg = findAll[0]
    dbg = dbg[5:]
    findAll = re.findall(dbg + ".*", ir)
    findAll = re.findall(r'line: .*?,', findAll[1])
    line = findAll[0]
    line = line[6:]
    # print(line)
    return line
    pass

def conditonCode2Char(condCode):
    # 1 eq: equal
    # 2 ne: not equal
    # 3 ugt: unsigned greater than
    # 4 uge: unsigned greater or equal
    # 5 ult: unsigned less than
    # 6 ule: unsigned less or equal
    # 7 sgt: signed greater than
    # 8 sge: signed greater or equal
    # 9 slt: signed less than
    # 10sle: signed less or equal
    if condCode == "eq":    #1
        return "=="
    elif condCode == "ne":  #2
        return "!="
    elif condCode == "ugt": #3
        return ">"
    if condCode == "uge":   #4
        return ">="
    elif condCode == "ult": #5
        return "<"
    if condCode == "ule":   #6
        return "<="
    elif condCode == "sgt": #7
        return ">"
    if condCode == "sge":   #8
        return ">="
    elif condCode == "slt": #9
        return "<"
    elif condCode == "sle": #10
        return "<="
    else:
        print("Error: Can't parse condition code in function conditonCode2Char")
        return ""
    pass

def getReverseOpcode(Opcode):
	if Opcode == ">":
		return "<="
	elif Opcode == ">=":
		return "<"
	elif Opcode == "<":
		return ">="
	elif Opcode == "<=":
		return ">"
	elif Opcode == "==":
		return "=="
	else:
		return "Error"

def getPhiLine(BlockLabel, phiResult):
    for Phi in PhiPool[BlockLabel]:
        if phiResult == Phi["phiID"]:
            return Phi["line"]
    pass

# 删去前辈的%号，下划线代替小数点
def lastFormat(var):
    if var[0] == '%':
        var = var[1:]
    index = var.find('.')
    if index == -1:
        return var
    else:
        return var[:index] + "_" + var[index + 1:]
    pass

TraversIR(mod)

# 生成标签block,block_,pred,pc,pc_
block, block_, pred, pc, pc_ = Ints('block block_ pred pc pc_')
ALLVARS = []

Transitions = dict()
for index, item in enumerate(Trans):
    print("block=",item.block," block_=", item.block_," pc=", item.pc, " pc_=", item.pc_," pred=", item.pred," formula=", item.formula)
    Transitions[index] = []
    expr = "block == " + BlockLabel[item.block]
    Transitions[index].append(eval(expr))
    expr = "block_ == " + BlockLabel[item.block_]
    Transitions[index].append(eval(expr))
    expr = "pc == " + str(item.pc)
    Transitions[index].append(eval(expr))
    expr = "pc_ == " + str(item.pc_)
    Transitions[index].append(eval(expr))
    expr = "pred == " + BlockLabel[item.pred]
    Transitions[index].append(eval(expr))
    for char in item.formula:
        if char in ["==", "+", '<', '<=', '>', '>=']:
            continue
        if char.isnumeric():
            continue
        exec('{name} = Int("{name}")'.format(name = char))
        exec('ALLVARS.append({var})'.format(var = char))
    expr = " ".join(item.formula)
    Transitions[index].append(eval(expr))
print("AllVars")
print(ALLVARS)
# for
print("Transitions")
for Trans in Transitions.items():
    print(Trans)

