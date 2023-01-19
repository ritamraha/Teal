import time
import logging
import os,csv, shutil
import argparse
from smtencoding import SMTEncoding
from signaltraces import Sample, Trace, Signal
from formula import STLFormula
from z3 import *

class learnMTL:

	def __init__(self, signalfile):


		self.signalfile = signalfile
		self.signal_sample = Sample()
		self.signal_sample.readSample(self.signalfile)
		self.size_bound = 5
		self.props = self.signal_sample.vars
		self.prop2num = {self.props[i]:i for i in range(len(self.props))}
		self.end_time = self.signal_sample.end_time
		#print(self.signal_sample.positive[0])
		self.compute_prop_intervals()
		
		
		#self.fr_bound = 4
		#self.search_order = [(i,j) for i in range(1, self.fr_bound+1,5) for j in range(1, self.size_bound+1)] #can try out other search orders
		

	def compute_prop_intervals(self):

		timepoints = [sp.time for sp in self.signal_sample.positive[0].sequence]
		self.prop_itvs = {}
		self.max_prop_intervals=0
		for p in self.props:
			for signal_id, signal in enumerate(self.signal_sample.positive+self.signal_sample.negative):
				
				parity = 0
				itvs = []
				for sp in signal.sequence:
					if parity == 0 and sp.vector[self.prop2num[p]] == 1:
						parity = 1
						itv = (sp.time,)
						continue

					if parity == 1 and sp.vector[self.prop2num[p]] == 0:
						parity = 0
						itv += (sp.time,)
						itvs.append(itv)
						itv = ()
						continue

				if len(itv) == 1:
					itv += (self.end_time,)
					itvs.append(itv)
				self.prop_itvs[(p,signal_id)] = itvs
				self.max_prop_intervals = max(self.max_prop_intervals, len(itvs))




	def interesting_pred(self):
	
		pass
		#current assumption predicates are given

	#return #the predicates



	def truncate_sample(self, fr_score):
		'''
		Truncates the signals based on the future reach score
		'''

		#Possible optimization: Always no need to compute from scratch
		new_sample = Sample(positive=[], negative=[])
		new_sample.vars = self.signal_sample.vars
		new_sample.operators = self.signal_sample.operators
		new_sample.predicates = self.signal_sample.predicates

		for pos in self.signal_sample.positive:
			new_signal = Signal(sequence=[])
			for sp in pos.sequence:
				#print(sp.time)
				if sp.time <= fr_score:
					new_signal.addPoint(sp)
				else:
					break
			new_sample.positive.append(new_signal)


		for neg in self.signal_sample.negative:
			new_signal = Signal(sequence=[])
			for sp in neg.sequence:
				if sp.time <= fr_score:
					new_signal.addPoint(sp)
				else:
					break
			new_sample.negative.append(new_signal)

		return new_sample


	def search_only_size(self):
		
		for formula_size in range(1,4):
			#for formula_size in range(1,self.size_bound+1): 
				print('---------------Searching for formula size %d---------------'%formula_size)
				encoding = SMTEncoding(self.signal_sample, formula_size, self.props, self.max_prop_intervals, self.prop_itvs, self.end_time)
				encoding.encodeFormula()
				
				print('Constraint creation done, now solving')
				solverRes = encoding.solver.check()
				#t_solve=time.time()-t_solve

				checking= encoding.solver.unsat_core()
				#print(checking)

				#Print this to see constraint creation time and constraint solving time separately
				#print(depth, regexDepth)
				#print((i,j), "Creating time:", t_create, "Solving time:", t_solve)
				print('The solver found', solverRes)

				if solverRes == sat:
					solverModel = encoding.solver.model()	
					#for i in range(formula_size):
						#print('Node', i,':',[k[1] for k in encoding.x if k[0] == i and solverModel[encoding.x[k]] == True][0]) 
						#for signal_id, signal in enumerate(self.signal_sample.positive+self.signal_sample.negative):
							#print('Signal', signal_id)
							#for t in range(encoding.max_intervals):
								#print(t, (solverModel[encoding.itvs[(i,signal_id)][t][0]],solverModel[encoding.itvs[(i,signal_id)][t][1]]))
							#print(solverModel[encoding.num_itvs[(i,signal_id)]])
					#for i in range(encoding.max_intervals):
					#	print(i, (solverModel[encoding.itv_new[i][0]],solverModel[itv_new[i][1]]))

					formula = encoding.reconstructWholeFormula(solverModel)
					#formula_list.append(formula)
					found_formula_size = formula.treeSize()
					print('Found formula %s of size %d'%(formula.prettyPrint(), formula.treeSize()))
					#break

		#for formula in formula_list:
		#	print(formula.prettyPrint())
		#	self.check_consistency(formula)


	def check_consistency(self, formula):

		formula_str = formula.prettyPrint()

		#convert F, G, ! to <>, [], -
		formula_str = formula_str.replace('U', 'until')
		formula_str = formula_str.replace('F', 'eventually')
		formula_str = formula_str.replace('G', 'always')
		formula_str = formula_str.replace('!', 'not')
		
		spec = rtamt.STLDenseTimeSpecification()
		spec.name = 'offline monitor'
		spec.spec = formula_str
		for var in self.signal_sample.vars: 
			spec.declare_var(var, 'float')
		spec.parse()

		for i,signal in enumerate(self.signal_sample.positive):
			var_vals = {}
			for v in range(len(self.signal_sample.vars)):
				var_vals[v] = [[t.time, t.vector[v]] for t in signal.sequence]

			tuple_arg = [[self.signal_sample.vars[v], var_vals[v]] for v in range(len(self.signal_sample.vars))]

			rob = spec.evaluate(*tuple_arg)
			print(rob)
		
		for i,signal in enumerate(self.signal_sample.negative):
			var_vals = {}
			for v in range(len(self.signal_sample.vars)):
				var_vals[v] = [[t.time, t.vector[v]] for t in signal.sequence]

			tuple_arg = [[self.signal_sample.vars[v], var_vals[v]] for v in range(len(self.signal_sample.vars))]

			rob = spec.evaluate(*tuple_arg)
			print(rob)
			



def main():

	parser = argparse.ArgumentParser()

	parser.add_argument('--input_file', '-i', dest='input_file', default = './robot_signal_mtl.signal')
	parser.add_argument('--timeout', '-t', dest='timeout', default=900, type=int)
	parser.add_argument('--outputcsv', '-o', dest='csvname', default= './result.csv')
	parser.add_argument('--verbose', '-v', dest='verbose', default=3, action='count')
	args,unknown = parser.parse_known_args()
	
	input_file = args.input_file
	timeout = float(args.timeout)

	learner = learnMTL(signalfile=input_file)
	learner.search_only_size()


main()

