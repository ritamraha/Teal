from z3 import *
from formula import STLFormula
from semantics import *







class SMTEncoding:

	def __init__(self, sample, formula_size, prop, max_prop_intervals, prop_itvs, end_time): 
		
		unary = ['F', '!']
		binary = ['&', '|']
		defaultOperators = unary + binary
		
		#except for the operators, the nodes of the "syntaxDAG" are additionally the propositional variables 
		
		'''
		if testTraces.operators == None:
			self.listOfOperators = defaultOperators
		else:
			self.listOfOperators = testTraces.operators
		
		if 'prop' in self.listOfOperators:
			self.listOfOperators.remove('prop')
		'''
		self.unaryOperators = unary
		self.binaryOperators = binary
		self.listOfOperators = self.unaryOperators + self.binaryOperators

		#self.noneOperator = 'none' # a none operator is not needed in this encoding
		
		self.solver = Solver()
		self.formula_size = formula_size
		self.sample = sample
		self.listOfPropositions = prop
		self.num_sampled_points = len(self.sample.positive[0].sequence)
		self.max_prop_intervals=max_prop_intervals
		self.max_intervals={}
		for i in range(self.formula_size):
			#self.max_intervals[i]= (i+1)* self.max_prop_intervals
			self.max_intervals[i]=3 
		print(self.max_intervals)
		#self.max_intervals = self.formula_size*self.num_sampled_points
		#self.max_intervals = 3
		self.prop_itvs = prop_itvs
		self.end_time = end_time

		#self.listOfPropositions = [i for i in range(self.traces.numPropositions)]
		
	   
	"""	
	the working variables are 
		- x[i][o]: i is a subformula (row) identifier, o is an operator or a propositional variable. Meaning is "subformula i is an operator (variable) o"
		- l[i][j]:  "left operand of subformula i is subformula j"
		- r[i][j]: "right operand of subformula i is subformula j"
		- y[i][tr][t]: semantics of formula i in time point t of trace tr
	"""
	def encodeFormula(self, unsatCore=True):
		

		self.operatorsAndPropositions = self.listOfOperators + self.listOfPropositions
		print(self.operatorsAndPropositions)
		
		self.x = { (i, o) : Bool('x_%d_%s'%(i,o)) for i in range(self.formula_size) for o in self.operatorsAndPropositions}
		
		self.a = {i: Real('a_%d'%i) for i in range(self.formula_size)}
	
		self.b = {i: Real('b_%d'%i) for i in range(self.formula_size)}

		self.fr = {i: Real('fr_%d'%i) for i in range(self.formula_size)}

		self.l = {(parentOperator, childOperator) : Bool('l_%d_%d'%(parentOperator,childOperator))\
												 for parentOperator in range(1,self.formula_size)\
												 for childOperator in range(parentOperator)} 
		
		self.r = {(parentOperator, childOperator) : Bool('r_%d_%d'%(parentOperator,childOperator))\
												 for parentOperator in range(1,self.formula_size)\
												 for childOperator in range(parentOperator)}

		self.itvs = { (i, signal_id): {t:(Real('itv_%d_%d_%d_%d'%(i,signal_id,t,0)), Real('itv_%d_%d_%d_%d'%(i,signal_id,t,1))) for t in range(self.max_intervals[i])}\
				  for i in range(self.formula_size)\
				  for signal_id, signal in enumerate(self.sample.positive + self.sample.negative)\
				   }

		self.num_itvs = {(i, signal_id): Int('num_itv_%d_%d'%(i,signal_id))\
						for i in range(self.formula_size)\
						for signal_id, signal in enumerate(self.sample.positive + self.sample.negative)}

		
		#print('x-vars:',self.x)
		#print('y-vars',self.y)
		#print('l-vars:',self.l)
		self.solver.set()

		# Structural Constraints
		self.exactlyOneOperator()	   
		self.firstOperatorProposition()
		self.noDanglingPropositions()
		self.ensureProperIntervals()
		self.temporalBoundsRelation() #<---
		
		# Semantic Constraints
		self.propositionsSemantics()
		self.operatorsSemantics() #<---

		#self.futureReachBound() #<---
		root_G = True

		#for formulas with G
		if root_G:
			for signal_id in range(len(self.sample.positive)):
				self.solver.assert_and_track(And(self.itvs[(self.formula_size - 1, signal_id)][0][0]==0,\
												self.itvs[(self.formula_size - 1, signal_id)][0][1]==self.end_time), \
											"Positive signal %d should hold"%signal_id)
						
			for signal_id in range(len(self.sample.positive), len(self.sample.positive+self.sample.negative)):
				self.solver.assert_and_track(Or(self.itvs[(self.formula_size - 1, signal_id)][0][0]>0, \
												self.itvs[(self.formula_size - 1, signal_id)][0][1]<self.end_time), \
											"Negative signal %d should not hold"%signal_id)		
		else:

			
			for signal_id in range(len(self.sample.positive)):
				self.solver.assert_and_track(And(self.itvs[(self.formula_size - 1, signal_id)][0][0]==0), \
											"Positive signal %d should hold"%signal_id)
						
			for signal_id in range(len(self.sample.positive), len(self.sample.positive+self.sample.negative)):
				self.solver.assert_and_track(self.itvs[(self.formula_size - 1, signal_id)][0][0]>0, \
											"Negative signal %d should not hold"%signal_id)
	
	def future_reach_encoding():

		for i in range(self.formula_size):

			if 'F' in self.listOfOperators or 'G' in self.listOfOperators:

				self.assert_and_track(Implies(Or(self.x[(i,'F')],x[(i,'G')]),\
										self.fr[i]= self.fr[j]+self.b[i]),\
										'Future reach computation for formula size %d'%i)

			if '&' in self.listOfOperators or '|' in self.listOfOperators:
			
				pass

			if '!' in self.listOfOperators:

			if 



	def ensureProperIntervals(self):

		for i in range(1, self.formula_size):
			for signal_id, signal in enumerate(self.sample.positive+self.sample.negative):
				
				self.solver.assert_and_track(And(0<=self.num_itvs[(i,signal_id)], self.num_itvs[(i,signal_id)]<=self.max_intervals[i]),\
											"Number of intervals well defined for formula size %d on signal %d"%(i,signal_id))
				for t in range(self.max_intervals[i]):
					
					self.solver.assert_and_track(self.itvs[(i, signal_id)][t][0]<=self.itvs[(i, signal_id)][t][1],
									'Proper intervals for formula size %d on signal %d at time %d'%(i,signal_id,t))

					self.solver.assert_and_track(Implies(t>=self.num_itvs[(i,signal_id)], 
												And(self.itvs[(i, signal_id)][t][0]==self.end_time,\
													self.itvs[(i, signal_id)][t][1]==self.end_time)),
										'End time intervals for formula size %d on signal %d at time %d'%(i,signal_id,t))
				
					if t<self.max_intervals[i]-1:					
						self.solver.assert_and_track(self.itvs[(i, signal_id)][t][1]<=self.itvs[(i, signal_id)][t+1][0],
										'Proper next intervals for formula size %d on signal %d at time %d'%(i,signal_id,t))
						   
					  
	def temporalBoundsRelation(self):

		for i in range(self.formula_size):

			if 'G' in self.listOfOperators:
				#globally				
				self.solver.assert_and_track(Implies(self.x[(i, 'G')], And(self.a[i]>=0,self.a[i] <= self.b[i])),\
											'temporal bounds of globally operator for node %d'%i)

				#self.solver.assert_and_track(Implies(self.x[(i, 'G')], Or([self.a[i] == self.utp[tp] for tp in range(len(self.utp))])),\
				#							'temporal lower bounds values of globally operator for node %d'%i)
 
				#self.solver.assert_and_track(Implies(self.x[(i, 'G')], Or([self.b[i] == self.utp[tp] for tp in range(len(self.utp))])),\
				#							'temporal upper bounds values of globally operator for node %d'%i)
				#self.solver.assert_and_track(Implies(self.x[(i, 'G')], Or([self.b[i] == 3])),\
				#							'temporal upper bounds values of globally operator for node %d'%i)
 
			if 'F' in self.listOfOperators:				  
				#finally				
				self.solver.assert_and_track(Implies(self.x[(i, 'F')], And(And(self.a[i]>=0,self.a[i] <= self.b[i]))),\
											   'temporal bounds of finally operator for node %d'%i)
				
				#self.solver.assert_and_track(Implies(self.x[(i, 'F')], Or([self.a[i] == self.utp[tp] for tp in range(len(self.utp))])),\
				#							'temporal lower bounds values of finally operator for node %d'%i)
 
				#self.solver.assert_and_track(Implies(self.x[(i, 'F')], Or([self.b[i] == self.utp[tp] for tp in range(len(self.utp))])),\
				#							'temporal upper bounds values of finally operator for node %d'%i)						 


	def firstOperatorProposition(self):
		
		self.solver.assert_and_track(Or([self.x[k] for k in self.x if k[0] == 0 and k[1] in self.listOfPropositions]),\
									 'first operator a variable')

	def noDanglingPropositions(self):
		
		if self.formula_size > 0:
			self.solver.assert_and_track(
				And([
					Or(
						AtLeast([self.l[(rowId, i)] for rowId in range(i+1, self.formula_size)] + [1]),
						AtLeast([self.r[(rowId, i)] for rowId in range(i+1, self.formula_size)] + [1])
					)
					for i in range(self.formula_size - 1)]
				),
				"no dangling variables"
			)

	def propositionsSemantics(self):

		for p in self.listOfPropositions:
			for i in range(self.formula_size):
				for signal_id, signal in enumerate(self.sample.positive + self.sample.negative):
					
					self.solver.assert_and_track(Implies(self.x[(i, p)],\
															And([And([self.itvs[(i, signal_id)][t][k] == self.prop_itvs[signal_id][p][t][k]  \
															 for t in range(len(self.prop_itvs[signal_id][p])) for k in range(2)]), And([self.itvs[(i, signal_id)][t][k] == self.end_time\
															 for t in range(len(self.prop_itvs[signal_id][p]),self.max_intervals[i]) for k in range(2)]),\
															 self.num_itvs[(i,signal_id)] == len(self.prop_itvs[signal_id][p])])),\
															 'Intervals for propositional variable node_'+ str(i)+ 'var _'+str(p)+'_signal_'+ str(signal_id))
				
		
	def exactlyOneOperator(self):
				
		self.solver.assert_and_track(And([\
										  AtMost( [self.x[k] for k in self.x if k[0] == i] +[1])\
										  for i in range(self.formula_size)\
										  ]),\
										  "at most one operator per subformula"\
		)
		
		self.solver.assert_and_track(And([\
										  AtLeast( [self.x[k] for k in self.x if k[0] == i] +[1])\
										  for i in range(self.formula_size)\
										  ]),\
										  "at least one operator per subformula"\
		)
		
		if (self.formula_size > 0):
			self.solver.assert_and_track(And([\
											Implies(
												Or(
													[self.x[(i, op)] for op in self.binaryOperators+self.unaryOperators]
												),
												AtMost( [self.l[k] for k in self.l if k[0] == i] +[1])\
				)
										  for i in range(1,self.formula_size)\
										  ]),\
										  "at most one left operator for binary and unary operators"\
		)
		
		if (self.formula_size > 0):
			self.solver.assert_and_track(And([\
											Implies(
												Or(
													[self.x[(i, op)] for op in
													 self.binaryOperators + self.unaryOperators]
												),
												AtLeast( [self.l[k] for k in self.l if k[0] == i] +[1])\
												)
										  for i in range(1,self.formula_size)\
										  ]),\
										  "at least one left operator for binary and unary operators"\
		)

		if (self.formula_size > 0):
			self.solver.assert_and_track(And([ \
				Implies(
					Or(
						[self.x[(i, op)] for op in self.binaryOperators]
					),
					AtMost([self.r[k] for k in self.r if k[0] == i] + [1]) \
					)
				for i in range(1, self.formula_size) \
				]), \
				"at most one right operator for binary" \
				)

		if (self.formula_size > 0):
			self.solver.assert_and_track(And([ \
				Implies(
					Or(
						[self.x[(i, op)] for op in
						 self.binaryOperators]
					),
					AtLeast([self.r[k] for k in self.r if k[0] == i] + [1]) \
					)
				for i in range(1, self.formula_size) \
				]), \
				"at least one right operator for binary" \
				)

		if (self.formula_size > 0):
			self.solver.assert_and_track(And([ \
				Implies(	
					Or(
						[self.x[(i, op)] for op in
						 self.unaryOperators]
					),
					Not(
						Or([self.r[k] for k in self.r if k[0] == i]) \
					)
				)
				for i in range(1, self.formula_size) \
				]), \
				"no right operators for unary" \
				)

		if (self.formula_size > 0):
			self.solver.assert_and_track(And([ \
				Implies(
					Or(
						[self.x[(i, op)] for op in
						 self.listOfPropositions]
					),
					Not(
						Or(
							Or([self.r[k] for k in self.r if k[0] == i]), \
							Or([self.l[k] for k in self.l if k[0] == i])
						)

					)
				)
				for i in range(1, self.formula_size) \
				]), \
				"no left or right children for variables" \
				)
	

	def operatorsSemantics(self):

		for signal_id, signal in enumerate(self.sample.positive + self.sample.negative):
			
			for i in range(1, self.formula_size):

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
					print(signal_id, i)
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
					print(i,signal_id)
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
		
	def reconstructWholeFormula(self, model):

		
		return self.reconstructFormula(self.formula_size-1, model)
		
	def reconstructFormula(self, rowId, model):
		

		def getValue(row, vars):
			tt = [k[1] for k in vars if k[0] == row and model[vars[k]] == True]
			if len(tt) > 1:
				raise Exception("more than one true value")
			else:
				return tt[0]
		operator = getValue(rowId, self.x)
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
			return STLFormula(label=operator, left=self.reconstructFormula(leftChild,model), right=self.reconstructFormula(rightChild, model))

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