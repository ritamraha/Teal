
import time
import logging
import os,csv, shutil
import argparse
from smtencoding import SMTEncoding
from signaltraces import Sample, Trace, Signal
from formula import STLFormula
from z3 import *
from monitoring import *
from smtencoding_incremental_c import *
import multiprocessing
#from pysmt.shortcuts import is_sat, get_model, Solver
#from six.moves import cStringIO
#from pysmt.smtlib.parser import SmtLibParser

class learnMTL:

	def __init__(self, signalfile, monitoring, fr_bound, outputcsv='./results.csv', timeout=900):


		self.signalfile = signalfile
		self.signal_sample = Sample(positive=[], negative=[], \
									propositions=[], operators=[],end_time=None)
		self.signal_sample.readSample(self.signalfile)
		self.size_bound = 6
		self.props = self.signal_sample.propositions
		#print('props', self.props)
		self.prop2num = {self.props[i]:i for i in range(len(self.props))}
		self.end_time = self.signal_sample.end_time
		self.monitoring = monitoring
		self.fr_bound = fr_bound
		#print(self.signal_sample.positive[0])
		self.compute_prop_intervals()
		self.sample_number = (len(self.signal_sample.positive)+len(self.signal_sample.negative))
		self.sample_lengths =  len(self.signal_sample.positive[0])
		self.timeout = timeout
		self.info_dict = {'file_name': self.signalfile, 'Fr bound': self.fr_bound,\
							 'Number of examples': self.sample_number, \
							 'Example length': self.sample_lengths,
							 'Formula': None, 'Formula Size': None, 'Correct?': None, \
							'Total Time': None, 'Timeout':self.timeout}
		
		self.outputcsv = outputcsv

		self.header = list(self.info_dict.keys())

		with open(self.outputcsv, 'w') as f:
			writer = csv.DictWriter(f, fieldnames = self.header)
			writer.writeheader()
			writer.writerow(self.info_dict)

		#formula = STLFormula.convertTextToFormula('|(p,G[0,3](q))')
		#print(check_consistency_G(formula, self.signal_sample, 1))

		#print(self.prop_itvs)
		#self.fr_bound = 4
		#self.search_order = [(i,j) for i in range(1, self.fr_bound+1,5) for j in range(1, self.size_bound+1)] #can try out other search orders
		

	def compute_prop_intervals(self):

		timepoints = [sp.time for sp in self.signal_sample.positive[0].sequence]
		self.prop_itvs = {}
		self.max_prop_intervals=0
		itv = ()

		for signal_id, signal in enumerate(self.signal_sample.positive+self.signal_sample.negative):
			self.prop_itvs[signal_id] = {}
			for p in self.props:	
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
				self.prop_itvs[signal_id][p] = itvs
				self.max_prop_intervals = max(self.max_prop_intervals, len(itvs))



	def search_only_size(self):
		
		t0 = time.time()
		for formula_size in range(1,5):
			#for formula_size in range(1,self.size_bound+1): 
			print('---------------Searching for formula size %d---------------'%formula_size)
			encoding = SMTEncoding(self.signal_sample, formula_size, self.props, self.max_prop_intervals,\
												 self.prop_itvs, self.end_time)
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

				formula = encoding.reconstructWholeFormula(solverModel)
				
				found_formula_size = formula.treeSize()
				
				print('Found formula %s of size %d'%(formula.prettyPrint(), formula.treeSize()))
				#break
				self.check_consistency_G(formula)
	   
		t1 = time.time()-t0
		print('Total time', t1)

	
	def search_incremental(self):
		
		encoding = SMTEncoding_incr(self.signal_sample, self.props, self.max_prop_intervals,\
													 self.prop_itvs, self.end_time, self.monitoring)
		
		total_solving_time = 0
		total_running_time = 0
		
		for formula_size in range(1,self.size_bound):
			
			t0 = time.time()

			print('---------------Searching for formula size %d---------------'%formula_size)
			
			ct0 = time.time()
			encoding.encodeFormula(formula_size, self.fr_bound)
			ct1 = time.time() - ct0
			
			print('Constraint Creation Done, took %.3f secs'%ct1)
			
			solving_time = time.time()
			solverRes = encoding.solver.check()
			print('The solver found', solverRes)
			solving_time = time.time() - solving_time
			total_solving_time += solving_time

			if solverRes == sat:
				
				solverModel = encoding.solver.model()
				
				formula = encoding.reconstructWholeFormula(solverModel, formula_size)
				found_formula_size = formula.treeSize()
				precision = max(1,formula.calc_precision())


				if self.monitoring:
					formula_str = 'G'+formula.prettyPrint()
				else:
					formula_str = formula.prettyPrint()


				#for i in range(formula_size):
				# 	print('Node', i,':',[k[1] for k in encoding.x if k[0] == i and solverModel[encoding.x[k]] == True][0]) 
					
				 	#for signal_id, signal in enumerate(self.signal_sample.positive+self.signal_sample.negative):
				 	#	print('Signal', signal_id)
				 	#	for t in range(encoding.max_intervals):
				 	#		print(t, (solverModel[encoding.itvs[(i,signal_id)][t][0]],solverModel[encoding.itvs[(i,signal_id)][t][1]]))
				 	#	print(solverModel[encoding.num_itvs[(i,signal_id)]])
				
				#for i in range(encoding.max_intervals):
				#	print(i, (solverModel[encoding.itv_new[i][0]],solverModel[itv_new[i][1]]))

				
				#fr_bound = solverModel[encoding.fr[formula_size-1]]
				
				
					
				#print('Found formula %s of size %d'%(formula.prettyPrint(), formula.treeSize()))
				print('Found formula %s'%(formula_str))
				#break


				if self.monitoring==1:
					ver = self.check_consistency_G(formula, precision)
				else:
					ver = self.check_consistency(formula, precision)

				t1 = time.time()-t0
				total_running_time += t1
				print('Total time', round(t1,3), '; Solving Time', round(solving_time,3))
				self.info_dict.update({'Formula': formula_str, 'Formula Size': formula_size, 'Correct?': ver, \
							'Total Time': total_running_time})
				break
			
			else:
				encoding.solver.pop()
				t1 = time.time()-t0
				total_running_time += t1
				print('Total time', round(t1,3), '; Solving Time', round(solving_time,3))
			
			
	
		with open(self.outputcsv, 'w') as f:
			writer = csv.DictWriter(f, fieldnames = self.header)
			writer.writeheader()
			writer.writerow(self.info_dict)

		return self.info_dict


	def check_consistency(self, formula, precision):

		self.info_dict.update({'Wrong': ''})
		for signal_id in range(len(self.signal_sample.positive)):
			
			if not sat_check(self.prop_itvs[signal_id], formula, self.end_time, precision):
				self.info_dict.update({'Wrong': signal_id})
				print('Formula is wrong!!!')
				return False

		for signal_id in range(len(self.signal_sample.positive), len(self.signal_sample.positive+self.signal_sample.negative)):
			if sat_check(self.prop_itvs[signal_id], formula, self.end_time, precision):
				self.info_dict.update({'Wrong': signal_id})
				print('Formula is wrong!!!')
				return False
		
		print('Formula is correct')
		return True

	def check_consistency_G(self, formula, precision):

		for signal_id in range(len(self.signal_sample.positive)):
			if not sat_check_G(self.prop_itvs[signal_id], formula, self.end_time, precision):
				print(signal_id)
				print('Formula is wrong!!!')
				return False

		for signal_id in range(len(self.signal_sample.positive), len(self.signal_sample.positive+self.signal_sample.negative)):
			if sat_check_G(self.prop_itvs[signal_id], formula, self.end_time, precision):
				print(signal_id)
				print('Formula is wrong!!!')
				return False
		
		print('Formula is correct')
		return True


def main():

	parser = argparse.ArgumentParser()

	parser.add_argument('--input_file', '-i', dest='input_file', default = 'example.signal')
	parser.add_argument('--fr_bound', '-f', dest='fr_bound', default=2, type=int)
	parser.add_argument('--monitoring', '-m', dest= 'monitoring', default=True, action='store_true')
	parser.add_argument('--timeout', '-t', dest='timeout', default=5400, type=int)
	parser.add_argument('--outputcsv', '-o', dest='csvname', default= '')
	

	args,unknown = parser.parse_known_args()
	
	input_file = args.input_file
	outputcsv = args.csvname
	timeout = float(args.timeout)
	monitoring = int(args.monitoring)
	fr_bound = int(args.fr_bound)

	if outputcsv=='':
		outputcsv = input_file.split('.signal')[0]+'-'+str(fr_bound)+'.csv'


	learner = learnMTL(signalfile=input_file, monitoring = monitoring, 
						fr_bound=fr_bound, outputcsv=outputcsv, timeout=timeout)
	

	#print('Running file %s'%input_file)
	#learner.search_incremental()
	
	manager = multiprocessing.Manager()
	return_dict = manager.dict()
	jobs = []
		
	p = multiprocessing.Process(target=learner.search_incremental, args=())
		
	jobs.append(p)
	p.start()

	p.join(timeout)
	if p.is_alive():
		print("Timeout reached, check your output in result file")
		p.terminate()
		p.join()

	for proc in jobs:
		proc.join()
		
	return (return_dict.values())
	

def run_test(file_name, timeout=5400, fr_bound=3):

	
	csvname = file_name.split('.signal')[0]+'-'+str(fr_bound)+'.csv'
	learner = learnMTL(signalfile=file_name, monitoring=True, fr_bound=fr_bound,\
							 outputcsv = csvname, timeout=timeout)

	manager = multiprocessing.Manager()
	return_dict = manager.dict()
	jobs = []
		
	p = multiprocessing.Process(target=learner.search_incremental, args=())
		
	jobs.append(p)
	p.start()

	p.join(timeout)
	if p.is_alive():
		print("Timeout reached, check your output in result file")
		p.terminate()
		p.join()

	for proc in jobs:
		proc.join()

	# info_dict = learner.info_dict
	# #info_dict.update({'Timeout': timeout})

	# header = list(info_dict.keys())
	
	# with open(csvname, 'w') as f:
	# 	writer = csv.DictWriter(f, fieldnames = header)
	# 	writer.writeheader()
	# 	writer.writerow(info_dict)


#main()
#run_test('dummy.signal', 900, 3)

'''
#return #the predicates

def truncate_sample(self, fr_score):

Truncates the signals based on the future reach score

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

'''


