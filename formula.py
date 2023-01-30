import pdb
import re 
from lark import Lark, Transformer
from graphviz import Source



class SimpleTree:
	def __init__(self, label = "dummy"):	
		self.left = None
		self.right = None
		self.label = label
	
	def __hash__(self):
		# return hash((self.label, self.left, self.right))
		return hash(self.label) + id(self.left) + id(self.right)
	
	def __eq__(self, other):
		if other == None:
			return False
		else:
			return self.label == other.label and self.left == other.left and self.right == other.right
	
	def __ne__(self, other):
		return not self == other
	
	def _isLeaf(self):
		return self.right == None and self.left == None
	
	def _addLeftChild(self, child):
		if child == None:
			return
		if type(child) is str:
			child = SimpleTree(child)
		self.left = child
		
	def _addRightChild(self, child):
		if type(child) is str:
			child = SimpleTree(child)
		self.right = child
	
	def addChildren(self, leftChild = None, rightChild = None): 
		self._addLeftChild(leftChild)
		self._addRightChild(rightChild)
		
		
	def addChild(self, child):
		self._addLeftChild(child)
		
	def getAllNodes(self):
		leftNodes = []
		rightNodes = []
		
		if self.left != None:
			leftNodes = self.left.getAllNodes()
		if self.right != None:
			rightNodes = self.right.getAllNodes()
		return [self] + leftNodes + rightNodes

	def getAllLabels(self):
		if self.left != None:
			leftLabels = self.left.getAllLabels()
		else:
			leftLabels = []
			
		if self.right != None:
			rightLabels = self.right.getAllLabels()
		else:
			rightLabels = []
		return [self.label] + leftLabels + rightLabels

	def __repr__(self):
		if self.left == None and self.right == None:
			return self.label
		
		# the (not enforced assumption) is that if a node has only one child, that is the left one
		elif self.left != None and self.right == None:
			return self.label + '(' + self.left.__repr__() + ')'
		
		elif self.left != None and self.right != None:
			return self.label + '(' + self.left.__repr__() + ',' + self.right.__repr__() + ')'

'''
A class for encoding syntax Trees and syntax DAGs of LTL formulas
'''
class LTLFormula(SimpleTree):
	
	def __init__(self, formulaArg = "dummyF"):
		self.size = None
		if not isinstance(formulaArg, str):
			self.label = formulaArg[0]
			self.left = formulaArg[1]
			try:
				self.right = formulaArg[2]
			except:
				self.right = None

		else:
			super().__init__(formulaArg)

		# self.eval = [word][pos] = True / False

	def __lt__(self, other):

		if self.getDepth() < other.getDepth():
			return True
		elif self.getDepth() > other.getDepth():
			return False
		else:
			if self._isLeaf() and other._isLeaf():
				return self.label < other.label

			if self.left != other.left:
				return self.left < other.left

			if self.right is None:
				return False
			if other.right is None:
				return True
			if self.right != other.right:
				return self.right < other.right

			else:
				return self.label < other.label


	def prettyPrint(self, top=False):
		if top is True:
			lb = ""
			rb = ""
		else:
			lb = "("
			rb = ")"
		if self._isLeaf():
			return self.label
		if self.label in unary_operators:
			return lb + self.label +" "+ self.left.prettyPrint() + rb
		if self.label in binary_operators:
			return lb + self.left.prettyPrint() +" "+  self.label +" "+ self.right.prettyPrint() + rb

	
	def getAllVariables(self):
		allNodes = list(set(self.getAllNodes()))
		return [ node for node in allNodes if node._isLeaf() == True ]
	
	def getDepth(self):
		if self.left == None and self.right == None:
			return 0
		leftValue = -1
		rightValue = -1
		if self.left != None:
			leftValue = self.left.getDepth()
		if self.right != None:
			rightValue = self.right.getDepth()
		return 1 + max(leftValue, rightValue)
	
	def getNumberOfSubformulas(self):
		return len(self.getSetOfSubformulas())
	
	def getSetOfSubformulas(self):
		if self.left == None and self.right == None:
			return [repr(self)]
		leftValue = []
		rightValue = []
		if self.left != None:
			leftValue = self.left.getSetOfSubformulas()
		if self.right != None:
			rightValue = self.right.getSetOfSubformulas()
		return list(set([repr(self)] + leftValue + rightValue))

	
	def treeSize(self):
		if self.size == None:
			if self.left == None and self.right == None:
				if self.label == 'true' or self.label == 'false':
					self.size = 0
				else:
					self.size = 1
			leftSize=0
			rightSize=0
			if self.left != None:
				leftSize= self.left.treeSize()
			if self.right != None:
				rightSize= self.right.treeSize()
			self.size = 1+ leftSize + rightSize

		return self.size


	@classmethod
	def convertTextToFormula(cls, formulaText):
		
		f = Formula()
		try:
			formula_parser = Lark(r"""
				?formula: _binary_expression
						|_temporal_unary_expression
						|_temporal_binary_expression
						|_unary_expression
						| constant
						| variable
				!constant: "true"
						| "false"
				_unary_expression: unary_operator "(" formula ")"
				_binary_expression: binary_operator "(" formula "," formula ")"
				variable: /[a-z]/
				!binary_operator: "&" | "|" | "->" | "U"
				!unary_operator: "F" | "G" | "!" | "X"
				
				%import common.SIGNED_NUMBER
				%import common.WS
				%ignore WS 
			 """, start = 'formula')
		
			
			tree = formula_parser.parse(formulaText)
			
		except Exception as e:
			print("can't parse formula %s" %formulaText)
			print("error: %s" %e)
			
		
		f = LTLTreeToFormula().transform(tree)
		return f
			
class LTLTreeToFormula(Transformer):
	def formula(self, formulaArgs):
		
		return LTLFormula(formulaArgs)
	def variable(self, varName):
		return LTLFormula([str(varName[0]), None, None])
	def constant(self, arg):
		if str(arg[0]) == "true":
			connector = "|"
		elif str(arg[0]) == "false":
			connector = "&"
		return LTLFormula([connector, LTLFormula(["p", None, None]), LTLFormula(["!", Formula(["p", None, None] ), None])])
			
	def binary_operator(self, args):
		return str(args[0])
	def unary_operator(self, args):
		return str(args[0])


untimed_operators = ['!','&', '|', '->']
timed_operators = ['F','G', 'U']
binary_operators = ['&','|', '->', 'U']
unary_operators = ['F','G','!']

class STLFormula(SimpleTree):

	def __init__(self, label=None, right=None, left=None, time_interval=None):
		self.size = None
		self.label = label
		self.left = left
		self.right = right
		self.time_interval = time_interval

	'''
	def __init__(self, formulaArg):


		self.root = formulaArg[0]
		if self.root in timed_operators:	
			self.label = [self.root, [self.formulaArg[1],self.formulaArg]]

			self.left = formulaArg[1]
			try:
				self.right = formulaArg[2]
			except:
				self.right = None

		else:
			super().__init__(formulaArg)


	'''

	def treeSize(self):
		if self.size == None:
			if self.left == None and self.right == None:
				if self.label == 'true' or self.label == 'false':
					self.size = 0
				else:
					self.size = 1
			leftSize=0
			rightSize=0
			if self.left != None:
				leftSize = self.left.treeSize()
			if self.right != None:
				rightSize= self.right.treeSize()
			self.size = 1 + leftSize + rightSize

		return self.size
		
	def _isLeaf(self):

		return (self.right == None) and (self.left == None)



	def prettyPrint(self, top=False):
		if top is True:
			lb = ""
			rb = ""
		else:
			lb = "("
			rb = ")"

		if self._isLeaf():
			return self.label

		operator = self.label

		if operator in untimed_operators:
		
			if operator in unary_operators:
			
				return lb + operator + self.left.prettyPrint() + rb			

			else:

				return lb + self.left.prettyPrint() +" "+ operator +" "+ self.right.prettyPrint() + rb

		else:
			try:
				lb_frac = self.time_interval[0].as_fraction()
				ub_frac = self.time_interval[1].as_fraction()
				
				lower_bound = float(lb_frac.numerator)/float(lb_frac.denominator)
				upper_bound = float(ub_frac.numerator)/float(ub_frac.denominator)

			except:
				
				lower_bound = self.time_interval[0]
				upper_bound = self.time_interval[1]
			
			#lower_bound = self.label[1][0]
			#upper_bound = self.label[1][1]

			if operator in unary_operators:
				return lb + operator + '[' + str(lower_bound) + "," + str(upper_bound) + "]"+ self.left.prettyPrint() + rb
			else:
				return lb + self.left.prettyPrint() +" "+  operator + '[' + str(lower_bound) + "," + str(upper_bound) + "]"+ " " + self.right.prettyPrint() + rb
	

	def __str__(self):
		if self.left == None and self.right == None:
			return self.label
		
		# the (not enforced assumption) is that if a node has only one child, that is the left one
		elif self.left != None and self.right == None:
			if instance(self.label,list):
				return self.label[0] + self.label[1] + '(' + self.left.__repr__() + ')'
			else:
				return self.label + '(' + self.left.__repr__() + ')'

		elif self.left != None and self.right != None:
			return self.label + '(' + self.left.__repr__() + ',' + self.right.__repr__() + ')'


	@classmethod
	def convertTextToFormula(cls, formulaText):
		
		f = STLFormula()
		try:
			formula_parser = Lark(r"""
				?formula: _binary_expression
						|_temporal_unary_expression
						|_temporal_binary_expression
						|_unary_expression
						| constant
						| variable
				!constant: "true"
						| "false"
				_unary_expression: unary_operator "(" formula ")"
				_binary_expression: binary_operator "(" formula "," formula ")"
				_temporal_unary_expression: unary_operator interval "(" formula ")"
				_temporal_binary_expression: binary_operator interval "(" formula "," formula ")"
				variable: /[a-z]/
				bound : /([0-9]*[.])?[0-9]+/
				interval: "[" bound "," bound "]"
				!binary_operator: "&" | "|" | "->" | "U"
				!unary_operator: "F" | "G" | "!" | "X"
				
				%import common.SIGNED_NUMBER
				%import common.WS
				%ignore WS 
			 """, start = 'formula')
		
			
			tree = formula_parser.parse(formulaText)
			
		except Exception as e:
			print("can't parse formula %s" %formulaText)
			print("error: %s" %e)
			
		f = STLTreeToFormula().transform(tree)
		return f
			
class STLTreeToFormula(Transformer):
	def formula(self, formulaArgs):
		if formulaArgs[0] in timed_operators:
			try:
				return STLFormula(label=formulaArgs[0], left=formulaArgs[2], right=formulaArgs[3], time_interval=formulaArgs[1],)
			except:
				return STLFormula(label=formulaArgs[0], left=formulaArgs[2], right=None, time_interval=formulaArgs[1])
		else:
			try:
				return STLFormula(label=formulaArgs[0], left=formulaArgs[1], right=formulaArgs[2])
			except:
				return STLFormula(label=formulaArgs[0], left=formulaArgs[1], right=None)

	def variable(self, varName):
		#print(varName)
		return STLFormula(label=str(varName[0]), left=None, right=None)
	def constant(self, arg):
		if str(arg[0]) == "true":
			connector = "|"
		elif str(arg[0]) == "false":
			connector = "&"
		return STLFormula([connector, STLFormula(["p", None, None]), STLFormula(["!", STLFormula(["p", None, None] ), None])])
	def interval(self, args):
		return [args[0], args[1]]

	def bound(self, args):
		return float(args[0])

	def binary_operator(self, args):
		#print(args)
		return str(args[0])
	def unary_operator(self, args):
		#print(args)
		return str(args[0])


s = STLFormula.convertTextToFormula('F[0.1,10.3](G[2.5,8.2](!(q)))')