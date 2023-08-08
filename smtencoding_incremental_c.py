from z3 import *
from formula import STLFormula
from semantics import *



class SMTEncoding_incr:

	def __init__(self, sample, prop, max_prop_intervals, prop_itvs, end_time, monitoring): 
		
		unary = ['!', 'F', 'G']
		binary = ['&', '|', 'U']
		defaultOperators = unary + binary
		
		self.unaryOperators = unary
		self.binaryOperators = binary
		self.listOfOperators = self.unaryOperators + self.binaryOperators

		#self.noneOperator = 'none' # a none operator is not needed in this encoding
		
		#self.solver = Optimize()
		self.solver = Solver()
		self.sample = sample
		self.listOfPropositions = prop
		self.num_sampled_points = len(self.sample.positive[0].sequence)
		#self.max_prop_intervals=max_prop_intervals
		self.max_intervals = max_prop_intervals+2
		self.prop_itvs = prop_itvs
		self.end_time = end_time
		self.monitoring= monitoring
		
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
		#root_G = True
		if self.monitoring==1:

			for signal_id in range(len(self.sample.positive)):
				self.solver.add(And(self.itvs[(formula_size - 1, signal_id)][0][0]==0,\
												self.itvs[(formula_size - 1, signal_id)][0][1]==self.end_time))
						
			for signal_id in range(len(self.sample.positive), len(self.sample.positive+self.sample.negative)):
				self.solver.add(Or(self.itvs[(formula_size - 1, signal_id)][0][0]>0, \
												self.itvs[(formula_size - 1, signal_id)][0][1]<self.end_time))		
		else:
			
			for signal_id in range(len(self.sample.positive)):
				self.solver.add(self.itvs[(formula_size - 1, signal_id)][0][0]==0)
			
			for signal_id in range(len(self.sample.positive), len(self.sample.positive+self.sample.negative)):
				self.solver.add(self.itvs[(formula_size - 1, signal_id)][0][0]>0)

		
		self.noDanglingPropositions(formula_size)
		self.solver.add(self.fr[formula_size-1]<=fr_bound)
		
		#self.solver.minimize(self.fr[formula_size-1])

	
	def future_reach_encoding(self, formula_size):

		i = formula_size-1

		for p in self.listOfPropositions:
			self.solver.add(Implies(self.x[(i, p)],self.fr[i]==0))

		if 'F' in self.listOfOperators:				  
			#finally				
			self.solver.add(Implies(self.x[(i, 'F')],\
												   And([\
													   Implies(\
																 self.l[(i,onlyArg)],\
																 self.fr[i] == self.fr[onlyArg] + self.b[i]
																 )\
													   for onlyArg in range(i)\
													   ])\
												   ))
		if 'G' in self.listOfOperators:				  
			#globally				
			self.solver.add(Implies(self.x[(i, 'G')],\
												   And([\
													   Implies(\
																 self.l[(i,onlyArg)],\
																 self.fr[i] == self.fr[onlyArg] + self.b[i]
																 )\
													   for onlyArg in range(i)\
													   ])\
												   ))
		
		if 'U' in self.listOfOperators:
			#conjunction
			self.solver.add(Implies(self.x[(i, 'U')],\
												And([ Implies(\
															   And(\
																   [self.l[i, leftArg], self.r[i, rightArg]]\
																   ),\
															   		self.fr[i] == \
															   		If(self.fr[leftArg]>self.fr[rightArg], self.fr[leftArg]+self.b[i], self.fr[rightArg]+self.b[i])\
															   )\
															  for leftArg in range(i) for rightArg in range(i) ])))

		if '&' in self.listOfOperators:
			#conjunction
			self.solver.add(Implies(self.x[(i, '&')],\
												And([ Implies(\
															   And(\
																   [self.l[i, leftArg], self.r[i, rightArg]]\
																   ),\
															   		self.fr[i] == \
															   		If(self.fr[leftArg]>self.fr[rightArg], self.fr[leftArg], self.fr[rightArg])\
															   )\
															  for leftArg in range(i) for rightArg in range(i) ])))

		if '!' in self.listOfOperators:
			#negation
			self.solver.add(Implies(self.x[(i, '!')],\
												   And([\
													   Implies(\
																 self.l[(i,onlyArg)],\
																 self.fr[i]==self.fr[onlyArg]
																  )\
													   for onlyArg in range(i)\
													   ])\
												   ))

		
		if '|' in self.listOfOperators:
			#disjunction
			self.solver.add(Implies(self.x[(i, '|')],\
													And([ Implies(\
																   And(\
																	   [self.l[i, leftArg], self.r[i, rightArg]]\
																	   ),\
																   	self.fr[i] == \
																   		If(self.fr[leftArg]>self.fr[rightArg], self.fr[leftArg], self.fr[rightArg])\
																   )\
																  for leftArg in range(i) for rightArg in range(i) ])))
	
		



	def ensureProperIntervals(self, formula_size):

		i = formula_size - 1
		for signal_id, signal in enumerate(self.sample.positive+self.sample.negative):
			
			self.solver.add(And([0<=self.num_itvs[(i,signal_id)], self.num_itvs[(i,signal_id)]<=self.max_intervals,\
										self.itvs[(i,signal_id)][0][0]>=0]))
			for t in range(self.max_intervals):
				
				self.solver.add(Implies(t<self.num_itvs[(i,signal_id)],self.itvs[(i, signal_id)][t][0]<self.itvs[(i, signal_id)][t][1]))

				self.solver.add(Implies(t>=self.num_itvs[(i,signal_id)], 
											And(self.itvs[(i, signal_id)][t][0]==self.end_time,\
												self.itvs[(i, signal_id)][t][1]==self.end_time)))
			
				if t<self.max_intervals-1:					
					self.solver.add(self.itvs[(i, signal_id)][t][1]<=self.itvs[(i, signal_id)][t+1][0])

			#self.solver.add(self.itvs[(i, signal_id)][self.max_intervals-1][0]==5)
			#self.solver.add(self.itvs[(i, signal_id)][self.max_intervals-1][1]==5)
					   
					  
	def temporalBoundsRelation(self, formula_size):

		i = formula_size-1
		#self.solver.add(And(self.a[i]==1, self.b[i]==2))

		if 'G' in self.listOfOperators:
			#globally				
			self.solver.add(Implies(self.x[(i, 'G')], And(self.a[i]>=0,self.a[i] <= self.b[i])))
			

		if 'F' in self.listOfOperators:				  
			#finally				
			self.solver.add(Implies(self.x[(i, 'F')], And(And(self.a[i]>=0,self.a[i] <= self.b[i]))))

		if 'U' in self.listOfOperators:				  
			#until				
			self.solver.add(Implies(self.x[(i, 'U')], And(And(self.a[i]>=0,self.a[i] <= self.b[i]))))
			
			#self.solver.add(Implies(self.x[(i, 'F')], And(And(self.a[i]==0,3 == self.b[i]))))


	def firstOperatorProposition(self, formula_size):
		
		if formula_size==1:
			self.solver.add(Or([self.x[k] for k in self.x if k[0] == 0 and k[1] in self.listOfPropositions]))

	def noDanglingPropositions(self, formula_size):
		
		if formula_size > 0:
			self.solver.add(
				And([
					Or(
						Or([self.l[(rowId, i)] for rowId in range(i+1, formula_size)]),
						Or([self.r[(rowId, i)] for rowId in range(i+1, formula_size)])
					)
					for i in range(formula_size - 1)]
				)
			)




		'''
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
		'''

	def propositionsSemantics(self, formula_size):

		i = formula_size-1

		for p in self.listOfPropositions:
			for signal_id in range(len(self.sample.positive + self.sample.negative)):
				self.solver.add(Implies(self.x[(i, p)],\
														And([And([self.itvs[(i, signal_id)][t][k] == self.prop_itvs[signal_id][p][t][k]  \
														 for t in range(len(self.prop_itvs[signal_id][p])) for k in range(2)]), And([self.itvs[(i, signal_id)][t][k] == self.end_time\
														 for t in range(len(self.prop_itvs[signal_id][p]),self.max_intervals) for k in range(2)]),\
														 self.num_itvs[(i,signal_id)] == len(self.prop_itvs[signal_id][p])])),\
														 )
			
		
	def exactlyOneOperator(self, formula_size):
		
		i = formula_size-1
		
		#self.solver.assert_and_track(AtMost([self.x[k] for k in self.x if k[0] == i] +[1]),\
		#								  "at most one operator per subformula for formula size %d"%i)
		
		#self.solver.assert_and_track(AtLeast( [self.x[k] for k in self.x if k[0] == i] +[1]),\
		#								  "at least one operator per subformula for formula size %d"%i)

		self.solver.add(And([Not(And(self.x[k],self.x[m]))\
												for k in self.x for m in self.x if k!=m and k[0] == i and m[0]==i]))
		
		self.solver.add(Or( [self.x[k] for k in self.x if k[0] == i]))
		if i > 0:
			#self.solver.assert_and_track(Implies(Or([self.x[(i, op)] for op in self.binaryOperators+self.unaryOperators]),\
			#									AtMost( [self.l[k] for k in self.l if k[0] == i] +[1])),\
			#							  "at most one left operator for binary and unary operators for formula size %d"%i)
		
		
			#self.solver.assert_and_track(Implies(
			#									Or(
			#										[self.x[(i, op)] for op in
			#										 self.binaryOperators + self.unaryOperators]
			#									),
			#									AtLeast( [self.l[k] for k in self.l if k[0] == i]+[1])),\
			#							  "at least one left operator for binary and unary operators for formula size %d"%i)
			

			self.solver.add(Implies(Or([self.x[(i, op)] for op in self.binaryOperators+self.unaryOperators]),\
												And([Not(And(self.l[k], self.l[m]))\
													for m in self.l for k in self.l if k!=m and k[0] == i and m[0]==i]))										  )
		
			self.solver.add(Implies(
												Or(
													[self.x[(i, op)] for op in
													 self.binaryOperators + self.unaryOperators]
												),
												Or( [self.l[k] for k in self.l if k[0] == i]))\
										 )

		
			#self.solver.assert_and_track(Implies(Or([self.x[(i, op)] for op in self.binaryOperators]),\
			#									AtMost([self.r[k] for k in self.r if k[0] == i] + [1])),\
			#								"at most one right operator for binary for formula size %d"%i)

		
			#self.solver.assert_and_track(Implies(Or([self.x[(i, op)] for op in self.binaryOperators]),\
			#									AtLeast([self.r[k] for k in self.r if k[0] == i] + [1])),\
			#								"at least one right operator for binary for formula size %d"%i)


			self.solver.add(Implies(Or([self.x[(i, op)] for op in self.binaryOperators]),\
												And([Not(And(self.r[k],self.r[m])) for m in self.r for k in self.r\
												if k[0] == i and m[0]==i and k!=m])))



			self.solver.add(Implies(Or([self.x[(i, op)] for op in self.binaryOperators]),\
												Or([self.r[k] for k in self.r if k[0] == i])))

		
			self.solver.add(Implies(Or([self.x[(i, op)] for op in self.unaryOperators]),\
										Not(Or([self.r[k] for k in self.r if k[0] == i]))))

		
			self.solver.add(Implies(Or([self.x[(i, op)] for op in self.listOfPropositions]),\
					Not(Or(Or([self.r[k] for k in self.r if k[0] == i]), Or([self.l[k] for k in self.l if k[0] == i])))))
	

	def operatorsSemantics(self, formula_size):

		i = formula_size-1

		for signal_id, signal in enumerate(self.sample.positive + self.sample.negative):

			if '!' in self.listOfOperators:
				#negation
				self.solver.add(Implies(self.x[(i, '!')],\
													   And([\
														   Implies(\
																	 self.l[(i,onlyArg)],\
																	 not_itv(self.itvs[(onlyArg,signal_id)], \
																	 	self.itvs[(i,signal_id)], self.num_itvs[(onlyArg,signal_id)],\
																	 	self.num_itvs[(i, signal_id)], self.end_time)
																	  )\
														   for onlyArg in range(i)\
														   ])\
													   ))

			
			if '|' in self.listOfOperators:
				#disjunction
				#print(signal_id, i)
				self.solver.add(Implies(self.x[(i, '|')],\
														And([ Implies(\
																	   And(\
																		   [self.l[i, leftArg], self.r[i, rightArg]]\
																		   ),\
																	   	or_itv(self.itvs[(leftArg,signal_id)], self.itvs[(rightArg,signal_id)],\
																	   			 self.itvs[(i,signal_id)], i, signal_id,self.num_itvs[(leftArg,signal_id)],\
																	   			 self.num_itvs[(rightArg,signal_id)], self.num_itvs[(i,signal_id)],self.end_time)
																	   )\
																	  for leftArg in range(i) for rightArg in range(i) ])))

			if 'F' in self.listOfOperators:				  
				#finally				
				self.solver.add(Implies(self.x[(i, 'F')],\
													   And([\
														   Implies(\
																	 self.l[(i,onlyArg)],\
																	 F_itv(self.itvs[(onlyArg, signal_id)], self.itvs[(i, signal_id)],\
																	 		 self.a[i], self.b[i], i, signal_id, self.num_itvs[(onlyArg, signal_id)],\
																	 		 self.num_itvs[(i,signal_id)], self.end_time)
																	 )\
														   for onlyArg in range(i)\
														   ])\
													   ))

			if 'G' in self.listOfOperators:				  
				#globally				
				self.solver.add(Implies(self.x[(i, 'G')],\
													   And([\
														   Implies(\
																	 self.l[(i,onlyArg)],\
																	 G_itv(self.itvs[(onlyArg, signal_id)], self.itvs[(i, signal_id)],\
																	 		 self.a[i], self.b[i], i, signal_id, self.num_itvs[(onlyArg, signal_id)],\
																	 		 self.num_itvs[(i,signal_id)], self.end_time)
																	 )\
														   for onlyArg in range(i)\
														   ])\
													   ))

			
			if '&' in self.listOfOperators:
				#conjunction
				#print(i,signal_id)
				self.solver.add(Implies(self.x[(i, '&')],\
														And([ Implies(\
																	   And(\
																		   [self.l[i, leftArg], self.r[i, rightArg]]\
																		   ),\
																	   	and_itv(self.itvs[(leftArg,signal_id)], self.itvs[(rightArg,signal_id)],\
																	   			 self.itvs[(i,signal_id)], i, signal_id,\
																	   			 self.num_itvs[(leftArg,signal_id)],self.num_itvs[(rightArg,signal_id)],\
																	   			  self.num_itvs[(i,signal_id)],self.end_time)\
																	   )\
																	  for leftArg in range(i) for rightArg in range(i) ])))
				

			if 'U' in self.listOfOperators:
				#conjunction
				#print(i,signal_id)
				self.solver.add(Implies(self.x[(i, 'U')],\
														And([ Implies(\
																	   And(\
																		   [self.l[i, leftArg], self.r[i, rightArg]]\
																		   ),\
																	   	U_itv(self.itvs[(leftArg,signal_id)], self.itvs[(rightArg,signal_id)],\
																	   			 self.itvs[(i,signal_id)], i, signal_id,\
																	   			 self.num_itvs[(leftArg,signal_id)],self.num_itvs[(rightArg,signal_id)],\
																	   			  self.num_itvs[(i,signal_id)],self.end_time)\
																	   )\
																	  for leftArg in range(i) for rightArg in range(i) ])))
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
			#print('reconstruct prop from ', self.listOfPropositions, operator)
			return STLFormula(label=operator)
		
		elif operator in self.unaryOperators:
		
			leftChild = getValue(rowId, self.l)
			if operator in ['F', 'G']:
				
				time_interval = [model[self.a[rowId]],model[self.b[rowId]]]
				
				return STLFormula(label=operator, time_interval=time_interval, left=self.reconstructFormula(leftChild, model), right=None) 
		
			else:
				#print(operator)
				return STLFormula(label=operator, time_interval=None, left=self.reconstructFormula(leftChild, model), right=None)
		
		elif operator in self.binaryOperators:
			#print(operator)
			leftChild = getValue(rowId, self.l)
			rightChild = getValue(rowId, self.r)
			if operator in ['U']:
				
				time_interval = [model[self.a[rowId]],model[self.b[rowId]]]
				
				return STLFormula(label=operator, time_interval=time_interval, left=self.reconstructFormula(leftChild, model), right=self.reconstructFormula(rightChild, model))
			else:

				return STLFormula(label=operator, time_interval=None, left=self.reconstructFormula(leftChild, model), right=self.reconstructFormula(rightChild, model))

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