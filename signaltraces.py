import random
from monitoring import *
from formula import *



def convertTextToSignal(text):

	sequence = []
	split1 = text.split(';')
	for value in split1:
		time, vector = value.split(':')
		vector = [bool(int(i)) for i in vector.split(',')]
		sp = samplePoint(float(time), vector)
		sequence.append(sp)

	return Signal(sequence)


default_operators = ['&', '|', '!', 'F', 'G', 'U']


class samplePoint:
	
	def __init__(self, time, vector):

		self.time = time
		self.vector = vector
		self.size = len(vector)

	def __str__(self):

		text = str(self.time) + ':' 
		text += ','.join([str(int(i)) for i in self.vector])
		return text

class Signal:
	'''
	signals are finite piece-wise linear continuous functions
	'''
	def __init__(self, sequence=[]):

		if sequence==[] or isinstance(sequence[0], samplePoint):
			self.sequence = sequence
		else:
			raise Exception("Invalid signals")

	def addPoint(self, samplePoint):

		self.sequence.append(samplePoint)

	def calculateInfo(self):

		self.domain = [i.time for i in self.sequence]

	def __str__(self):

		text = ';'.join([str(value) for value in self.sequence])
		return text

	def __eq__(self, other):

		return str(self)==str(other)


	def __len__(self):

		return len(self.sequence)

class binarySignal:
	'''
	binarySignals are finite piece-wise linear (possibly discontinuous) functions
	'''
	def __init__(self, sequence):

		if sequence==[] or isinstance(sequence[0], samplePoint):
			self.sequence = sequence
		else:
			raise Exception("Invalid signals")

	def addPoint(self, samplePoint):

		self.sequence.append(samplePoint)

	def calculateInfo(self):

		self.domain = [i.time for i in self.sequence]

	def __str__(self):

		text = ';'.join([str(value) for value in self.sequence])
		return text

class Trace:
	'''
	defines a sequences of letters, which could be a subset of propositions or symbol from an alphabet
	'''
	def __init__(self, vector, lasso_start=None):
			
		self.vector = vector
		self.length = len(vector)
		self.lasso_start = lasso_start
		if self.lasso_start == None:
			self.is_finite = True
	
		self.vector_str = str(self)

		if lasso_start != None:
			self.is_finite = False
			self.lasso_start = int(lasso_start)
			if self.lasso_start >= self.length:
				raise Exception(
					"lasso start = %s is greater than any value in trace (trace length = %s) -- must be smaller" % (
					self.lasso_start, self.length))

			self.lasso_length = self.length - self.lasso_start
			self.prefix_length = self.length - self.lasso_length

			self.lasso = self.vector[self.lasso_start:self.length]
			self.prefix = self.vector[:self.lasso_start]

	def __str__(self):
		vector_str = [list(map(lambda x: str(int(x)), letter)) for letter in self.vector]
		return str(';'.join([','.join(letter) for letter in vector_str]))


class Sample:

	def __init__(self, positive=[], negative=[], propositions=[], operators=[], end_time=10):

		self.positive = positive
		self.negative = negative
		self.propositions = propositions
		if operators==[]:
			self.operators = default_operators
		else:
			self.operators = operators
		self.end_time = end_time

	def readSample(self, signalfile):
		
		with open(signalfile, 'r') as file:
			mode = 0
			count=0
			while True:
				count
				line=file.readline()
				if line=='':
					break

				if line == '---\n':
					mode+=1
					continue

				if mode==0:	
		
					signal = convertTextToSignal(line)	 	
					self.numProps = signal.sequence[0].size
					self.positive.append(signal)


				if mode==1:
					
					signal = convertTextToSignal(line)
					self.negative.append(signal)
				
				if mode==2:

					self.end_time = int(line.strip())

				if mode==3:
				
					self.operators = list(line.strip().split(','))
				
				if mode==4:

					self.propositions = list(line.strip().split(','))
					
				#if mode==4:

			if self.propositions == []:
				self.propositions = ['p'+str(i) for i in range(self.numVars)]
	
	
	def writeSample(self, signalfile):

		with open(signalfile, 'w') as file:
			
			for signal in self.positive:
				file.write(str(signal)+'\n')

			file.write('---\n')
			for signal in self.negative:
				file.write(str(signal)+'\n')

			file.write('---\n')

			file.write(str(self.end_time)+'\n')

			file.write('---\n')

			file.write(','.join(self.operators)+'\n')

			file.write('---\n')

			file.write(','.join(self.propositions))

			#file.write('---\n')

			#pred_list = []
			
			#file.write(';'.join(pred_list))

	def random_signal_uniform(self,
		propositions = ['p','q','r'], 
		length = 5,
		is_words = True):

		signal_sequence = [ samplePoint(t,[random.randint(0,1) for _ in range(len(propositions))]) for t in range(length)]
		return Signal(signal_sequence)

	def random_signal_nonuniform(self,
		propositions = ['p','q','r'], 
		length = 5,
		is_words = True):
		
		random_times = [0]
		round_upto = 1
		
		for i in range(length-1):
			random_times.append(round(random.uniform(0,length),round_upto))

		random_times.sort()

		signal_sequence = [ samplePoint(t,[random.randint(0,1) for _ in range(len(propositions))]) for t in random_times]
		
		return Signal(signal_sequence)



	def generator(self,
		formula = None, 
		filename = 'generated.signal',
		end_time=10, 
		num_signals = (5,5), 
		length_signals = None,
		propositions = ['p','q','r'], 
		length_range = (5,15), 
		operators=['G', 'F', '!', 'U', '&','|', 'X']):

		num_positives = 0
		total_num_positives = num_signals[0]
		num_negatives = 0
		total_num_negatives = num_signals[1]
		ver = True
		prop2num = {propositions[i]:i for i in range(len(propositions))}

		num_iterations = 0
		iteration_bound = (10**6)
		#false_count = 0
		total_false_count = 0
		signal_list = []

		while (num_positives < total_num_positives or num_negatives < total_num_negatives) and num_iterations < iteration_bound:

			num_iterations += 1
			length = random.randint(length_range[0], length_range[1])
			final_signal = self.random_signal_nonuniform(propositions, length)

			#check
			if num_iterations % 10000 == 0:
				print('Number of iterations', num_iterations)
				print('Currently found:', num_positives, num_negatives)
			if formula != None:

				prop_itvs = compute_prop_intervals(signal=final_signal, props=propositions, prop2num=prop2num, end_time=end_time)
				ver = sat_check_G(prop_itvs=prop_itvs, formula=formula, end_time=end_time)

			if num_positives < total_num_positives:
				if ver == True or formula == None:
					if final_signal not in self.positive:
						self.positive.append(final_signal)
						num_positives += 1
					continue

			if num_negatives < total_num_negatives:
				if ver == False or formula == None:
					if final_signal not in self.negative:
						self.negative.append(final_signal) 
						num_negatives += 1
					continue
			# sys.stdout.write("\rGenerating sample: created %d positives, %d negatives "%(num_positives, num_negatives))
			# sys.stdout.flush()
		self.operators = operators
		self.propositions = propositions
		self.end_time = end_time
		self.writeSample(filename)

class WordSample:
	'''
	contains the sample of postive and negative examples
	'''
	def __init__(self, positive=[], negative=[], alphabet=[], operators=['G', 'F', '!', 'U', '&','|', 'X']):

		self.positive = positive
		self.negative = negative
		self.alphabet = alphabet
		self.num_positives = len(self.positive)
		self.num_negatives = len(self.negative)
		self.operators = operators

	
	def extract_alphabet(self):
		'''
		extracts alphabet from the words/signals provided in the data
		'''
		alphabet = set()
		
		self.alphabet = [chr(ord('p')+i) for i in range(len(self.positive[0].vector[0]))] 

	def word2trace(self, word):
		one_hot_alphabet={}
		for i in range(len(self.alphabet)):
			one_hot_letter = [0]*len(self.alphabet)
			letter = self.alphabet[i]
			one_hot_letter[i] = 1
			one_hot_alphabet[letter] = tuple(one_hot_letter)
		trace_list=[]
		for letter in word:
			trace_list.append(one_hot_alphabet[letter])

		return trace_list



	def readFromFile(self, filename):
		'''
		reads .trace/.word files to extract sample from it
		'''
		
		with open(filename, 'r') as file:
			mode = 0
			count=0
			while True:
				count
				line=file.readline()
				if line=='':
					break

				if line == '---\n':
					mode+=1
					continue

				if mode==0:	
					
					trace_vector, lasso_start = lineToTrace(line)
					trace = Trace(vector=trace_vector, lasso_start=lasso_start, is_word=False)	 	
					self.positive.append(trace)

				if mode==1:
					
					trace_vector, lasso_start = lineToTrace(line)
					trace = Trace(vector=trace_vector, lasso_start=lasso_start, is_word=False)	 	
					self.negative.append(trace)

				if mode==2:
					self.operators = list(line.strip().split(','))
				if mode==3:
					self.alphabet = list(line.split(','))


		if mode != 3:		
				self.extract_alphabet(self.is_words)
		
		self.letter2pos={}
		for i in range(len(self.alphabet)):
			self.letter2pos[self.alphabet[i]]=i
		
		
		self.writeToFile('small-example')

	def writeToFile(self, filename):

		with open(filename, 'w') as file:
			for trace in self.positive:

				file.write(str(trace)+'\n')
			file.write('---\n')

			for trace in self.negative:
				file.write(str(trace)+'\n')


			if self.operators!=[]:
				file.write('---\n')
				file.write(','.join(self.operators)+'\n')

			if self.alphabet != []:
				file.write('---\n')
				file.write(','.join(self.alphabet))


'''
f = STLFormula.convertTextToFormula('|(!(p),F[0.0625,1.9375](p))')
print('HEre',f.prettyPrint())
s = Sample()
s.readSample('./dummy.signal')
#prop_itvs = compute_prop_intervals(s, ['p'], {'p':0}, 5.0)
print(check_consistency_G(f, s))
'''
#[(0,4),(7,8),(9,10)]
#[(2,6.9),(6,8.9),(9.9,10)]