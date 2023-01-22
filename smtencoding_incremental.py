from z3 import *
from formula import STLFormula
from semantics import *



class SMTEncoding_incr:

	def __init__(self, sample, prop, max_prop_intervals, prop_itvs, end_time): 
		
		unary = ['F', '!']
		binary = ['&', '|']
		defaultOperators = unary + binary
		
		self.unaryOperators = unary
		self.binaryOperators = binary
		self.listOfOperators = self.unaryOperators + self.binaryOperators

		#self.noneOperator = 'none' # a none operator is not needed in this encoding
		
		self.solver = Optimize()
		#self.solver = Solver()
		self.sample = sample
		self.listOfPropositions = prop
		self.num_sampled_points = len(self.sample.positive[0].sequence)
		#self.max_prop_intervals=max_prop_intervals
		self.max_intervals = 6
		self.prop_itvs = prop_itvs
		self.end_time = end_time
		


		self.operatorsAndPropositions = self.listOfOperators + self.listOfPropositions

		# initializing the variables
		self.x = {}
		self.r = {}
		self.l = {}
		self.a = {}
		self.b = {}
		self.fr = {}
		self.itvs = {}
		self.num_itvs = {}

	"""	
	the working variables are 
		- x[i][o]: i is a subformula (row) identifier, o is an operator or a propositional variable. Meaning is "subformula i is an operator (variable) o"
		- l[i][j]:  "left operand of subformula i is subformula j"
		- r[i][j]: "right operand of subformula i is subformula j"
		- y[i][tr][t]: semantics of formula i in time point t of trace tr
	"""
	def encodeFormula(self, formula_size, fr_bound):
		
		self.x.update({ (formula_size-1, o) : Bool('x_%d_%s'%((formula_size-1),o)) for o in self.operatorsAndPropositions})

		self.l.update({(formula_size-1, childOperator) : Bool('l_%d_%d'%(formula_size-1,childOperator))\
												 for childOperator in range(formula_size-1)})
		
		self.r.update({(formula_size-1, childOperator) : Bool('r_%d_%d'%(formula_size-1,childOperator))\
												 for childOperator in range(formula_size-1)})
		
		self.a.update({(formula_size-1): Real('a_%d'%(formula_size-1))})
	
		self.b.update({(formula_size-1): Real('b_%d'%(formula_size-1))})

		self.fr.update({(formula_size-1): Real('fr_%d'%(formula_size-1))})

		self.itvs.update({ (formula_size-1, signal_id): \
			{t:(Real('itv_%d_%d_%d_%d'%(formula_size-1,signal_id,t,0)), \
				Real('itv_%d_%d_%d_%d'%(formula_size-1,signal_id,t,1)))\
				  for t in range(self.max_intervals)}\
				  for signal_id, signal in enumerate(self.sample.positive + self.sample.negative)})

		self.num_itvs.update({(formula_size-1, signal_id): Int('num_itv_%d_%d'%(formula_size-1,signal_id))\
						for signal_id, signal in enumerate(self.sample.positive + self.sample.negative)})

		self.solver.set()

		# Structural Constraints
		self.exactlyOneOperator(formula_size)	   
		self.firstOperatorProposition(formula_size)	
		self.ensureProperIntervals(formula_size)
		self.temporalBoundsRelation(formula_size) 
		
		# Semantic Constraints
		self.propositionsSemantics(formula_size)
		self.operatorsSemantics(formula_size) #<---

		# Future Reach constraints
		self.future_reach_encoding(formula_size)
		

		self.solver.push()
		#for formulas with G
		root_G = True
		if root_G:

			for signal_id in range(len(self.sample.positive)):
				self.solver.assert_and_track(And(self.itvs[(formula_size - 1, signal_id)][0][0]==0,\
												self.itvs[(formula_size - 1, signal_id)][0][1]==self.end_time), \
											"Positive signal %d should hold for formula size %d"%(signal_id,formula_size))
						
			for signal_id in range(len(self.sample.positive), len(self.sample.positive+self.sample.negative)):
				self.solver.assert_and_track(Or(self.itvs[(formula_size - 1, signal_id)][0][0]>0, \
												self.itvs[(formula_size - 1, signal_id)][0][1]<self.end_time), \
											"Negative signal %d should not hold for formula size %d"%(signal_id,formula_size))		
		else:
			
			for signal_id in range(len(self.sample.positive)):
				self.solver.assert_and_track(And(self.itvs[(formula_size - 1, signal_id)][0][0]==0), \
											"Positive signal %d should hold for formula size %d"%(signal_id,formula_size))
			
			for signal_id in range(len(self.sample.positive), len(self.sample.positive+self.sample.negative)):
				self.solver.assert_and_track(self.itvs[(formula_size - 1, signal_id)][0][0]>0, \
											"Negative signal %d should not hold for formula size %d"%(signal_id,formula_size))

		
		self.noDanglingPropositions(formula_size)
		self.solver.assert_and_track(self.fr[formula_size-1]<fr_bound, \
								'future reach bound for formula size %d'%formula_size)
		
		self.solver.minimize(self.fr[formula_size-1])


	def future_reach_encoding(self, formula_size):

		i = formula_size-1

		for p in self.listOfPropositions:
			self.solver.assert_and_track(Implies(self.x[(i, p)],self.fr[i]==0),\
													'future reach of proposition %s for node %d'%(p,i))

		if 'F' in self.listOfOperators:				  
			#finally				
			self.solver.assert_and_track(Implies(self.x[(i, 'F')],\
												   And([\
													   Implies(\
																 self.l[(i,onlyArg)],\
																 self.fr[i] == self.fr[onlyArg] + self.b[i]
																 )\
													   for onlyArg in range(i)\
													   ])\
												   ),\
										   'future reach of finally operator node %d'%i)
		if 'G' in self.listOfOperators:				  
				#finally				
			self.solver.assert_and_track(Implies(self.x[(i, 'G')],\
												   And([\
													   Implies(\
																 self.l[(i,onlyArg)],\
																 self.fr[i] == self.fr[onlyArg] + self.b[i]
																 )\
													   for onlyArg in range(i)\
													   ])\
												   ),\
										   'future reach of globally operator node %d'%i)
			
		if '&' in self.listOfOperators:
			#conjunction
			self.solver.assert_and_track(Implies(self.x[(i, '&')],\
												And([ Implies(\
															   And(\
																   [self.l[i, leftArg], self.r[i, rightArg]]\
																   ),\
															   		self.fr[i] == \
															   		If(self.fr[leftArg]>self.fr[rightArg], self.fr[leftArg], self.fr[rightArg])\
															   )\
															  for leftArg in range(i) for rightArg in range(i) ])),\
												 'future reach of conjunction for node %d'%i)

		if '!' in self.listOfOperators:
			#negation
			self.solver.assert_and_track(Implies(self.x[(i, '!')],\
												   And([\
													   Implies(\
																 self.l[(i,onlyArg)],\
																 self.fr[i]==self.fr[onlyArg]
																  )\
													   for onlyArg in range(i)\
													   ])\
												   ),\
										   'future reach of negation for node %d'%i)

		
		if '|' in self.listOfOperators:
			#disjunction
			self.solver.assert_and_track(Implies(self.x[(i, '|')],\
													And([ Implies(\
																   And(\
																	   [self.l[i, leftArg], self.r[i, rightArg]]\
																	   ),\
																   	self.fr[i] == \
																   		If(self.fr[leftArg]>self.fr[rightArg], self.fr[leftArg], self.fr[rightArg])\
																   )\
																  for leftArg in range(i) for rightArg in range(i) ])),\
													 'future reach of disjunction for node %d'%i)
		
	
		



	def ensureProperIntervals(self, formula_size):

		i = formula_size - 1
		for signal_id, signal in enumerate(self.sample.positive+self.sample.negative):
			
			self.solver.assert_and_track(And(0<=self.num_itvs[(i,signal_id)], self.num_itvs[(i,signal_id)]<=self.max_intervals),\
								"Number of intervals well defined for formula size %d on signal %d"%(i,signal_id))
			for t in range(self.max_intervals):
				
				self.solver.assert_and_track(self.itvs[(i, signal_id)][t][0]<=self.itvs[(i, signal_id)][t][1],
								"Proper intervals for formula size %d on signal %d at time %d"%(i,signal_id,t))

				self.solver.assert_and_track(Implies(t>=self.num_itvs[(i,signal_id)], 
											And(self.itvs[(i, signal_id)][t][0]==self.end_time,\
												self.itvs[(i, signal_id)][t][1]==self.end_time)),
									'End time intervals for formula size %d on signal %d at time %d'%(i,signal_id,t))
			
				if t<self.max_intervals-1:					
					self.solver.assert_and_track(self.itvs[(i, signal_id)][t][1]<=self.itvs[(i, signal_id)][t+1][0],
									'Proper next intervals for formula size %d on signal %d at time %d'%(i,signal_id,t))
					   
					  
	def temporalBoundsRelation(self, formula_size):

		i = formula_size-1

		if 'G' in self.listOfOperators:
			#globally				
			self.solver.assert_and_track(Implies(self.x[(i, 'G')], And(self.a[i]>=0,self.a[i] <= self.b[i])),\
										'temporal bounds of globally operator for node %d'%i)
	
		if 'F' in self.listOfOperators:				  
			#finally				
			self.solver.assert_and_track(Implies(self.x[(i, 'F')], And(And(self.a[i]>=0,self.a[i] <= self.b[i]))),\
										   'temporal bounds of finally operator for node %d'%i)
			

	def firstOperatorProposition(self, formula_size):
		
		if formula_size==1:
			self.solver.assert_and_track(Or([self.x[k] for k in self.x if k[0] == 0 and k[1] in self.listOfPropositions]),\
										 'first operator a variable')

	def noDanglingPropositions(self, formula_size):
		
		if formula_size > 0:
			self.solver.assert_and_track(
				And([
					Or(
						AtLeast([self.l[(rowId, i)] for rowId in range(i+1, formula_size)] + [1]),
						AtLeast([self.r[(rowId, i)] for rowId in range(i+1, formula_size)] + [1])
					)
					for i in range(formula_size - 1)]
				),
				"no dangling variables"
			)

	def propositionsSemantics(self, formula_size):

		i = formula_size-1

		for p in self.listOfPropositions:
			for signal_id in range(len(self.sample.positive + self.sample.negative)):
				self.solver.assert_and_track(Implies(self.x[(i, p)],\
														And([And([self.itvs[(i, signal_id)][t][k] == self.prop_itvs[signal_id][p][t][k]  \
														 for t in range(len(self.prop_itvs[signal_id][p])) for k in range(2)]), And([self.itvs[(i, signal_id)][t][k] == self.end_time\
														 for t in range(len(self.prop_itvs[signal_id][p]),self.max_intervals) for k in range(2)]),\
														 self.num_itvs[(i,signal_id)] == len(self.prop_itvs[signal_id][p])])),\
														 'Intervals for propositional variable node_'+ str(i)+ 'var _'+str(p)+'_signal_'+ str(signal_id))
			
		
	def exactlyOneOperator(self, formula_size):
		
		i = formula_size-1
		
		self.solver.assert_and_track(AtMost([self.x[k] for k in self.x if k[0] == i] +[1]),\
										  "at most one operator per subformula for formula size %d"%i)
		
		self.solver.assert_and_track(AtLeast( [self.x[k] for k in self.x if k[0] == i] +[1]),\
										  "at least one operator per subformula for formula size %d"%i)
		
		if i > 0:
			self.solver.assert_and_track(Implies(Or([self.x[(i, op)] for op in self.binaryOperators+self.unaryOperators]),\
												AtMost( [self.l[k] for k in self.l if k[0] == i] +[1])),\
										  "at most one left operator for binary and unary operators for formula size %d"%i)
		
		
			self.solver.assert_and_track(Implies(
												Or(
													[self.x[(i, op)] for op in
													 self.binaryOperators + self.unaryOperators]
												),
												AtLeast( [self.l[k] for k in self.l if k[0] == i]+[1])),\
										  "at least one left operator for binary and unary operators for formula size %d"%i)

		
			self.solver.assert_and_track(Implies(Or([self.x[(i, op)] for op in self.binaryOperators]),\
												AtMost([self.r[k] for k in self.r if k[0] == i] + [1])),\
											"at most one right operator for binary for formula size %d"%i)

		
			self.solver.assert_and_track(Implies(Or([self.x[(i, op)] for op in self.binaryOperators]),\
												AtLeast([self.r[k] for k in self.r if k[0] == i] + [1])),\
											"at least one right operator for binary for formula size %d"%i)

		
			self.solver.assert_and_track(Implies(Or([self.x[(i, op)] for op in self.unaryOperators]),\
										Not(Or([self.r[k] for k in self.r if k[0] == i]))),\
										"no right operators for unary for formula size %d"%i)

		
			self.solver.assert_and_track(Implies(Or([self.x[(i, op)] for op in self.listOfPropositions]),\
					Not(Or(Or([self.r[k] for k in self.r if k[0] == i]), Or([self.l[k] for k in self.l if k[0] == i])))),\
										"no left or right children for variables for formula size %d"%i)
	

	def operatorsSemantics(self, formula_size):

		i = formula_size-1

		for signal_id, signal in enumerate(self.sample.positive + self.sample.negative):

			if '!' in self.listOfOperators:
				#negation
				self.solver.assert_and_track(Implies(self.x[(i, '!')],\
													   And([\
														   Implies(\
																	 self.l[(i,onlyArg)],\
																	 not_itv(self.itvs[(onlyArg,signal_id)], \
																	 	self.itvs[(i,signal_id)], self.num_itvs[(onlyArg,signal_id)],\
																	 	self.num_itvs[(i, signal_id)], self.end_time)
																	  )\
														   for onlyArg in range(i)\
														   ])\
													   ),\
											   'semantics of negation for signal %d and node %d' % (signal_id, i))

			
			if '|' in self.listOfOperators:
				#disjunction
				#print(signal_id, i)
				self.solver.assert_and_track(Implies(self.x[(i, '|')],\
														And([ Implies(\
																	   And(\
																		   [self.l[i, leftArg], self.r[i, rightArg]]\
																		   ),\
																	   	or_itv(self.itvs[(leftArg,signal_id)], self.itvs[(rightArg,signal_id)],\
																	   			 self.itvs[(i,signal_id)], i, signal_id,self.num_itvs[(leftArg,signal_id)],\
																	   			 self.num_itvs[(rightArg,signal_id)], self.num_itvs[(i,signal_id)],self.end_time)
																	   )\
																	  for leftArg in range(i) for rightArg in range(i) ])),\
														 'semantics of disjunction for signal %d and node %d'%(signal_id, i))

			if 'F' in self.listOfOperators:				  
				#finally				
				self.solver.assert_and_track(Implies(self.x[(i, 'F')],\
													   And([\
														   Implies(\
																	 self.l[(i,onlyArg)],\
																	 F_itv(self.itvs[(onlyArg, signal_id)], self.itvs[(i, signal_id)],\
																	 		 self.a[i], self.b[i], i, signal_id, self.num_itvs[(onlyArg, signal_id)],\
																	 		 self.num_itvs[(i,signal_id)], self.end_time)
																	 )\
														   for onlyArg in range(i)\
														   ])\
													   ),\
											   'semantics of finally operator for signal %d and node %d' % (signal_id, i)\
			  									)

			
			if '&' in self.listOfOperators:
				#conjunction
				#print(i,signal_id)
				self.solver.assert_and_track(Implies(self.x[(i, '&')],\
														And([ Implies(\
																	   And(\
																		   [self.l[i, leftArg], self.r[i, rightArg]]\
																		   ),\
																	   	and_itv(self.itvs[(leftArg,signal_id)], self.itvs[(rightArg,signal_id)],\
																	   			 self.itvs[(i,signal_id)], i, signal_id,\
																	   			 self.num_itvs[(leftArg,signal_id)],self.num_itvs[(rightArg,signal_id)],\
																	   			  self.num_itvs[(i,signal_id)],self.end_time)\
																	   )\
																	  for leftArg in range(i) for rightArg in range(i) ])),\
														 'semantics of conjunction for signal %d and node %d'%(signal_id, i))
				'''	 
				if '->' in self.listOfOperators:
					   
					#implication
					self.solver.assert_and_track(Implies(self.x[(i, '->')],\
															And([ Implies(\
																		   And(\
																			   [self.l[i, leftArg], self.r[i, rightArg]]\
																			   ),\
																		   And(\
																			   [ self.y[(i, traceIdx, tp)]\
																				==\
																				Implies(\
																				  self.y[(leftArg, traceIdx, tp)],\
																				  self.y[(rightArg, traceIdx, tp)]\
																				   )\
																				 for tp in range(T)]\
																			   )\
																		   )\
																		  for leftArg in range(i) for rightArg in range(i) ])),\
															 'semantics of implication for trace %d and node %d'%(traceIdx, i))

				
				
				if 'G' in self.listOfOperators:
					#globally				
					self.solver.assert_and_track(Implies(self.x[(i, 'G')],\
														   And([\
															   Implies(\
																		 self.l[(i,j)],\
																		 And([\
																			  self.y[(i, traceIdx, tp)] ==\
																			  And(\
																			  	[Implies(And((self.utp[tp]+self.a[i]<=self.utp[tp1]),\
																			  		(self.utp[tp1]<=self.utp[tp]+self.b[i])), self.y[j, traceIdx, tp1]) \
																			  	for tp1 in range(tp,T)])\
																			  for tp in range(T)]))\
															   for j in range(i)\
															   ])\
														   ),\
												   'semantics of globally operator for trace %d and node %d' % (traceIdx, i)\
												   )

				if 'F' in self.listOfOperators:				  
					#finally				
					self.solver.assert_and_track(Implies(self.x[(i, 'F')],\
														   And([\
															   Implies(\
																		 self.l[(i,j)],\
																		 And([\
																			  self.y[(i, traceIdx, tp)] ==\
																			  Or(\
																			  	[And([(self.utp[tp]+self.a[i]<=self.utp[tp1]),\
																			  		(self.utp[tp1]<=self.utp[tp]+self.b[i]), self.y[j, traceIdx, tp1]]) \
																			  	for tp1 in range(tp,T)])\
																		  for tp in range(T)]))\
															   for j in range(i)\
															   ])\
														   ),\
												   'semantics of finally operator for trace %d and node %d' % (traceIdx, i)\
				  									)
				'''			
		
	def reconstructWholeFormula(self, model, formula_size):

		return self.reconstructFormula(formula_size-1, model)

		
	def reconstructFormula(self, rowId, model):
		

		def getValue(row, vars):
			tt = [k[1] for k in vars if k[0] == row and model[vars[k]] == True]
			if len(tt) > 1:
				raise Exception("more than one true value")
			else:
				return tt[0]
		operator = getValue(rowId, self.x)
		#print(operator)
		if operator in self.listOfPropositions:
		
			#print(str(self.alphabet[operator]))
			return STLFormula(label=operator)
		
		elif operator in self.unaryOperators:
		
			leftChild = getValue(rowId, self.l)
			if operator in ['F', 'G']:
				
				lower_bound = model[self.a[rowId]]
				upper_bound = model[self.b[rowId]]
				#print([operator,(lower_bound, upper_bound)])
				return STLFormula(label=[operator,(lower_bound, upper_bound)], left=self.reconstructFormula(leftChild, model)) 
		
			else:
				#print(operator)
				return STLFormula(label=operator, left=self.reconstructFormula(leftChild, model))
		
		elif operator in self.binaryOperators:
			#print(operator)
			leftChild = getValue(rowId, self.l)
			rightChild = getValue(rowId, self.r)

			return STLFormula(label=operator, left=self.reconstructFormula(leftChild, model), right=self.reconstructFormula(rightChild, model))

	'''
	def futureReachBound(self):	

		for i in range(self.formula_size):	
				
			for p in self.listOfPropositions:

				self.solver.assert_and_track(Implies(self.x[(i, p)], self.f[i] == 0.0),\
														 'future reach of proposition %s for node %d'%(p,i))

			if '|' in self.listOfOperators:
				
				#disjunction
				self.solver.assert_and_track(Implies(self.x[(i, '|')],\
														And([ Implies(\
																	   And(\
																		   [self.l[i, leftArg], self.r[i, rightArg]]\
																		   ),\
																	   self.f[i] = max(self.f[leftArg], self.f[rightArg])
																	   )\
																	  for leftArg in range(i) for rightArg in range(i) ])),\
														 'future reach of disjunction for node %d'%i)
			if '&' in self.listOfOperators:
				
				#conjunction
				self.solver.assert_and_track(Implies(self.x[(i, '&')],\
														And([ Implies(\
																	   And(\
																		   [self.l[i, leftArg], self.r[i, rightArg]]\
																		   ),\
																	   self.f[i] = max(self.f[leftArg], self.f[rightArg])
																	   )\
																	  for leftArg in range(i) for rightArg in range(i) ])),\
														 'future reach of conjunction for node %d'%(traceIdx, i))
				 
			if '->' in self.listOfOperators:
				   
				#implication
				self.solver.assert_and_track(Implies(self.x[(i, '->')],\
														And([ Implies(\
																	   And(\
																		   [self.l[i, leftArg], self.r[i, rightArg]]\
																		   ),\
																	   self.f[i] = max(self.f[leftArg], self.f[rightArg])
																	   )\
																	  for leftArg in range(i) for rightArg in range(i) ])),\
														 'future reach of implication for node %d'%(traceIdx, i))
			if '!' in self.listOfOperators:
				  #negation
				self.solver.assert_and_track(Implies(self.x[(i, '!')],\
													   And([\
														   Implies(\
																	 self.l[(i,onlyArg)],\
																	 self.f[i] = self.f[onlyArg]
																	  )\
														   for onlyArg in range(i)\
														   ])\
													   ),\
											   'future reach of negation for node %d' % (traceIdx, i)\
											   )
			if 'G' in self.listOfOperators:
				  #globally				
				self.solver.assert_and_track(Implies(self.x[(i, 'G')],\
													   And([\
														   Implies(\
																	 self.l[(i,onlyArg)],\
																	 self.f[i] = sum([If(self.b[i] == j, self.interestingTP[j], 0) for j in self.numTP]) + self.f[onlyArg]
																	  )\
														   for onlyArg in range(i)\
														   ])\
													   ),\
											   'future reach of globally operator for node %d' % (traceIdx, i)\
											   )

			if 'F' in self.listOfOperators:				  
				#finally				
				self.solver.assert_and_track(Implies(self.x[(i, 'F')],\
													   And([\
														   Implies(\
																	 self.l[(i,onlyArg)],\
																	self.f[i] = sum([If(self.b[i] == j, self.interestingTP[j], 0) for j in self.numTP]) + self.f[onlyArg]
																	  )\
														   for onlyArg in range(i)\
														   ])\
													   ),\
										   'future reach of finally operator for node %d'%i)
	'''	  