import sys

inputFile = open(sys.argv[2])
outputFile = open("CNF_satisfiability.txt", "w")

operators = ["not", "and", "or"]

def extractLiterals(clause):
	literalList = []
	if(not(isinstance(clause,list))):
		return clause
	else:
		if(clause[0] == 'not'):
			return clause[1]
		else:
			for i in range(1,len(clause)):
				literalList.append(extractLiterals(clause[i]))
	return literalList
	
def booleanStringClause(clause):
	if(not(isinstance(clause,list))):
		return "var["+str(symbols.index(clause))+"]"
	
	else:
		if(clause[0] == 'not'):
			return "not(var["+str(symbols.index(clause[1]))+"])"
		else:
			temp = "( "+booleanStringClause(clause[1]);
			for i in range (2,len(clause)):
				temp += " or " + booleanStringClause(clause[i])
			temp += " )"
			return temp
			

def getSymbols(model):
	global symbols

	for element in model:
		if(not(isinstance(element,list)) and element not in operators):
			if(element not in symbols):
				symbols += element
		elif (isinstance(element,list)):
			symbols = getSymbols(element)
	
	return symbols
	
def getClauses(model):
	clauses = []
	if(model[0] == 'and'):
		for i in range(1,len(model)):
			clauses.append(model[i])
	else:
		clauses.append(model)
		
	return clauses
	
def checkComplementarity(element):
	complemented = False
	variable = ""
	if(not(isinstance(element,list))):
		complemented = False
		variable = element
	
	else:
		if(element[0] == 'not'):
			complemented = True
			variable = element[1]

	#print "com,var", complemented,variable
	return complemented,variable
	
def updateValueList(complemented, value, index):
	#print "value[index]: ",value[index]
	if(complemented == False and value[index] == 0):
		return 1
	if(complemented == True and value[index] == 0):
		return 2
	if((complemented == False and value[index] == 2) or (complemented == True and value[index] == 1)):
		return 3
	return value[index]
	
		
def findPureSymbols(clauses,symbols):
	#print "pure"
	pureList = []
	value = []
	#print symbols
	for symbol in symbols:
		value.append(0)
	
	#print "clauses", clauses
	for clause in clauses:
		#print "inival", value
		if(not(isinstance(clause,list))):
			#print "literal"
			index = symbols.index(clause)
			#print index
			value[index] = updateValueList(False,value,index)
		
		else:
			if(clause[0] == 'not'):
				#print "com"
				index = symbols.index(clause[1])
				#print index
				value[index] = updateValueList(True,value,index)
			
			else:
				for element in clause[1:len(clause)]:
					#print "or"
					complemented, variable = checkComplementarity(element)
					index = symbols.index(variable)
					#print "index", index
					value[index] = updateValueList(complemented,value,index)
					#print "val[ind]",value[index]
					
	
	#print "value", value
	for i in range(len(symbols)):
		if(value[i] == 1):
			pureList.append([symbols[i],True])
		elif(value[i] == 2):
			pureList.append([symbols[i],False])
	
	#print pureList
	return pureList
	
def findUnitClause(clauses,var):
	#print "uni"
	returnList = []
	value = []
	for symbol in symbols:
		value.append(0)
	#print "clauses", clauses
	for clause in clauses:
		#print "inival", value
		if(not(isinstance(clause,list))):
			#print "literal"
			index = symbols.index(clause)
			#print index
			value[index] = updateValueList(False,value,index)
		
		else:
			if(clause[0] == 'not'):
				#print "com"
				index = symbols.index(clause[1])
				#print index
				value[index] = updateValueList(True,value,index)
			
			else:
				unityTest = True
				falseLiteral = []
				for element in clause[1:len(clause)]:
					#print "or"
					complemented, variable = checkComplementarity(element)
					index = symbols.index(variable)
					if(complemented == True):
						if(eval('not(var[index])') == False):
							unityTest == True
							break;
						else:
							falseLiteral.append(element)
					else:
						if(eval('var[index]') == True):
							unityTest == True
							break;
						else:
							falseLiteral.append(element)
					
				if((len(falseLiteral)+1) == len(clause)):
					#print "index", index
					value[index] = updateValueList(complemented,value,index)
					#print "val[ind]",value[index]
	
	for i in range(len(symbols)):
		if(value[i] == 1):
			returnList.append([symbols[i],True])
		elif(value[i] == 2):
			returnList.append([symbols[i],False])
	
	return returnList
					

		
def assignementEval(clauses,var):
	result = True
	trueClauses = []
	#print "Asdf", clauses,var
	for clause in clauses:
		boolExpr = booleanStringClause(clause);
		#print "expr", boolExpr
		boolVal = eval(boolExpr)
		 
		if(boolVal == False):
			result = False;
		
		elif(boolVal == True):
			trueClauses.append(clause)
			
	#print "ret:", result,trueClauses			
	return result,trueClauses
		
def DPLL(clauses,symbols,var):
	#print "ini", clauses, symbols, var
	result,trueClauses = assignementEval(clauses,var)
	if(result==True):
		return var
		
	pureList = findPureSymbols(clauses,symbols)
	#print "pure list",pureList
	if(len(pureList)>0):
		#ptrueSymbols = []	
		for i in range(len(pureList)):
			element = pureList[i]
			index = symbols.index(element[0]);
			#print "symbols", symbols
			#ptrueSymbols.append(symbols[index])
			#print index
			var[index] = element[1]
		#print "var", var
		presult, ptrueClauses = assignementEval(clauses,var)
		if(presult == False):
			#ptrueSymbols = ptrueSymbols[0]
			#print "c,s", ptrueClauses
			reqClauses = [x for x in clauses if not(x in ptrueClauses)]
			#reqSymbols = [x for x in symbols if not(x in ptrueSymbols)]
			#print "req",reqClauses
			return DPLL(reqClauses,symbols,var)
		
		else:
			return var
			
	unitClauseList = findUnitClause(clauses,symbols)
	#print "unit", unitClauseList
	if(len(unitClauseList)>0):
		#ptrueSymbols = []	
		for i in range(len(unitClauseList)):
			element = unitClauseList[i]
			index = symbols.index(element[0]);
			#print "symbols", symbols
			#ptrueSymbols.append(symbols[index])
			#print index
			var[index] = element[1]
		#print "var", var
		uresult, utrueClauses = assignementEval(clauses,var)
		if(uresult == False):
			#ptrueSymbols = ptrueSymbols[0]
			#print "c,s", ptrueClauses
			reqClauses = [x for x in clauses if not(x in utrueClauses)]
			#reqSymbols = [x for x in symbols if not(x in ptrueSymbols)]
			#print "req",reqClauses
			return DPLL(reqClauses,symbols,var)
		
		else:
			return var
			
		
		
class index(object):
	i=0

def SATAssignment(expr):
	#print "in sat"
	numOfBits = "{0:0"+str(len(symbols))+"b}"
	#print "numOfBits", numOfBits
	returnList = []
	for i in range(2**len(symbols) - 1, -1, -1):
		#print "hi"
		binString = numOfBits.format(i)
		variableList = []
		for bit in binString:
			if bit == '0' :
				variableList.append(False)
			else:
				variableList.append(True)
		#print "varlis", variableList
		if(eval(expr)):
			returnList = variableList
			break;
			
	#print returnList
	return returnList


def booleanStringSentence(sentence):
	if (sentence[0] not in operators):
		if(not(isinstance(sentence,list))):
			return "variableList["+str(symbols.index(sentence))+"]"
		
	else:
		if(sentence[0] == 'not'):
			return "not("+booleanStringSentence(sentence[1])+")"
		
		elif(sentence[0] == 'or'):
			temp = "( "+booleanStringSentence(sentence[1])
			for i in range(2,len(sentence)):
				temp += " or " + booleanStringSentence(sentence[i])
			temp += " )"
			return temp
				
		elif(sentence[0] == 'and'):
			temp = "( "+booleanStringSentence(sentence[1])
			for i in range(2,len(sentence)):
				temp += " and " + booleanStringSentence(sentence[i])
			temp += " )"
			return temp
			
def DPLL_Satisfiable(sentence):
	symbols = getSymbols(sentence)
	clauses = getClauses(sentence)
	var = []
	for symbol in symbols:
			var.append(True)
	var = DPLL(clauses,symbols,var)
	
	if(var == None):
		expr = booleanStringSentence(sentence)
		#print "expr", expr
		var = SATAssignment(expr)
		
	return var, symbols
	
	


linenum = 1
sentCount = -1
numSent = 0
for line in inputFile:
	if (sentCount == -1):
		numSent = eval(line)
	sentCount += 1
	
if(sentCount != numSent):
	print "The number of propositional sentence is not equal to the number of lines"

else:
	linenum = 1
	inputFile.seek(0,0)
	for line in inputFile:
		if(linenum == 1):
			linenum = 2
			continue
		sentence = eval(line)
		symbols = []
		var = []
		var, symbols = DPLL_Satisfiable(sentence)
		#print booleanStringSenstence(sentence)
		satList = []
		if(len(var)>0) :
			satList += ['true']
			for i in range(len(var)):
				satList += [symbols[i] + '=' + str(var[i]).lower()]
		else:
			satList += ['false']
			
		print satList
		
		outputFile.write(str(satList)+"\n")
'''		
ua = None
if(eval('ua or True')):
	print "a"
elif(eval('ua or ua')==False):
	print "b"
print not(None)'''