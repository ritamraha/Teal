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
		text += ','.join([str(i) for i in self.vector])
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

	def __init__(self, positive=[], negative=[], vars=[], operators=[]):

		self.positive = positive
		self.negative = negative
		self.vars = []
		if operators==[]:
			self.operators = default_operators
		else:
			self.operators = operators

		self.predicates = {}
		self.end_time = None

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
					self.numVars = signal.sequence[0].size
					self.positive.append(signal)


				if mode==1:
					
					signal = convertTextToSignal(line)
					self.negative.append(signal)
				
				if mode==2:
					self.end_time = float(line.strip())

				if mode==3:
				
					self.operators = list(line.strip().split(','))
				
				if mode==4:

					self.vars = list(line.strip().split(','))
					print(self.vars)
					
				#if mode==4:

			if self.vars == []:
				self.vars = ['p'+str(i) for i in range(self.numVars)]
	
	
	def writeSample(self, signalfile):

		with open(signalfile, 'w') as file:
			
			for signal in self.positive:
				file.write(str(signal)+'\n')

			file.write('---\n')
			for signal in self.negative:
				file.write(str(signal)+'\n')

			file.write('---\n')

			file.write(','.join(self.operators)+'\n')

			file.write('---\n')

			file.write(','.join(self.vars)+'\n')

			file.write('---\n')

			pred_list = []
			for var in self.vars:
				pred_list.append(','.join([str(i) for i in self.predicates[var]]))
			
			file.write(';'.join(pred_list))



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
		extracts alphabet from the words/traces provided in the data
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