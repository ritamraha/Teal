import argparse
import os, shutil
import datetime
from signaltraces import Sample, Signal
from formula import STLFormula
from monitoring import *

class SampleGenerator:
	'''
	sample generator class
	'''
	def __init__(self,
				formula_file = './formulas.txt',
				sample_sizes = [(10,10),(50,50)],
				signal_lengths = [(6,6)],
				output_folder = './' + datetime.datetime.now().strftime('%Y-%m-%d_%H-%M-%S'),
				total_num = 1,
				precision=1):

		self.formula_file = formula_file
		self.sample_sizes = sample_sizes
		self.signal_lengths = signal_lengths
		self.output_folder = output_folder
		self.total_num = total_num
		self.operators = ['U', 'F', 'G', 'X', '!', '&', '|']
		self.precision = precision

		if os.path.exists(self.output_folder):
			shutil.rmtree(self.output_folder)

		os.makedirs(output_folder)
		formula_file_name = self.formula_file.split('/')[-1]

		shutil.copyfile(self.formula_file, output_folder+'/'+formula_file_name)
		self.sample_sizes.sort()
		self.max_size = sample_sizes[-1]
		

	def generateFromLargeSample(self, precision=1):
		
		generated_files = self.generate(gen_from_large_sample=True, precision=precision)
		#generating small benchmarks from large ones
		self.generateSmallBenchmarks(generated_files, self.sample_sizes[:-1])



	def generate(self, gen_from_large_sample=False, precision=1):
		if gen_from_large_sample:
			sample_sizes = [self.max_size]
		else:	
			sample_sizes = self.sample_sizes

		signals_folder = self.output_folder+'/signalsFiles/' 
		os.makedirs(signals_folder)

		#if signal_type == 'words':
		#	words_folder = output_folder+'/signalsFiles/'
		#	os.makedirs(words_folder)

		generated_files = []
		with open(self.formula_file, 'r') as file:

			formula_num=0
			for line in file:
				
				formula_text, propositions = line.split(';')
				propositions = propositions.strip().split(',')

				
				#signal_lengths = lengths.split(',')
				#signal_lengths = [(int(i),int(i)) for i in signal_lengths]

				formula = STLFormula.convertTextToFormula(formula_text)
				print(formula)
				formula_num+=1
				print('---------------Generating Benchmarks for formula G%s---------------'%formula.prettyPrint())
				
				for size in sample_sizes:
					for length_range in self.signal_lengths:
						end_time = length_range[1]
						print(end_time)
						for num in range(self.total_num):
							length_mean = (length_range[0]+length_range[1])//2
							sample=Sample(positive=[], negative=[])


							signal_file = signals_folder+'f:'+str(formula_num).zfill(2)+'-'+'nw:'+str((size[0]+size[1])//2).zfill(3)+'-'+'ml:'+str(length_mean).zfill(2)+'-'+str(num)+'.signal'
							generated_files.append(signal_file)
							
							sample.generator(formula=formula, length_range=length_range, end_time=end_time, num_signals=size, propositions=propositions, 
													filename=signal_file, operators=self.operators, precision=precision)
							

							#convertFileType(wordfile=word_file, signalfile=signal_file, operators=operators)
						# else:

						# 	if gen_method=='dfa_method':
						# 		sample.generator_dfa_in_batch_advanced(formula=formula, length_range=length_range, num_signals=size, alphabet=alphabet, filename=signal_file, is_words=(signal_type=='words'), operators=operators)
						# 	elif gen_method=='random':
						# 		sample.generator(formula=formula, length_range=length_range, num_signals=size, alphabet=alphabet, filename=signal_file, is_words=(signal_type=='words'), operators=operators)
						# 	elif gen_method=='random_walk':
						# 		sample.generator_random_walk(formula=formula, length_range=length_range, num_signals=size, alphabet=alphabet, filename=signal_file, is_words=(signal_type=='words'), operators=operators)
							

						# sample.generator(formula=formula, length_range=length_range, num_signals=size, filename=signal_file, is_words=(signal_type=='words'), operators=operators)


							if check_consistency_G(formula, sample, precision):
								print("Formula is consistent with sample")

		return generated_files


	def generateSmallBenchmarks(self, generated_files, sizes):
		
		for filename in generated_files:
			
			s = Sample(positive=[],negative=[])
			s.readSample(filename)
			
			for (i,j) in sizes:
				
				new_filename = filename.replace("nw:"+str((self.max_size[0]+self.max_size[1])//2).zfill(3), "nw:"+str(i).zfill(3))
				new_positive = s.positive[:i]
				new_negative = s.negative[:j]
				new_s = Sample(positive=new_positive, negative=new_negative, propositions=s.propositions, end_time=s.end_time)
				new_s.writeSample(new_filename)


#Data type for parser
def tupleList(s):
	try:
		return tuple(map(int , s.split(',')))
	except:
		print("Wrong format; provide comma separated values")



def main():

	parser = argparse.ArgumentParser()
	parser.add_argument('--formula_file', dest='formula_file', default = './formulas-AV.txt')
	parser.add_argument('--signal_type', dest='signal_type', default = 'signal')
	parser.add_argument('--size', dest='sample_sizes', default=[(4,4),(8,8),(12,12),(16,16),(32,32)], nargs='+', type=tupleList)
	parser.add_argument('--precision', dest='precision', default=1, type=int)
	#parser.add_argument('--end_time', dest='end_time', default=10.0, type=float)
	parser.add_argument('--lengths', dest='signal_lengths', default=[(4,4),(6,6),(8,8),(10,10),(12,12),(14,14),(16,16)], nargs='+', type=tupleList)
	parser.add_argument('--total_num', dest='total_num', default=1, type=int)
	parser.add_argument('--output_folder', dest='output_folder', default = './' + datetime.datetime.now().strftime('%Y-%m-%d_%H-%M-%S'))

	args,unknown = parser.parse_known_args()
	formula_file = args.formula_file
	signal_type = args.signal_type
	sample_sizes = list(args.sample_sizes)
	signal_lengths = list(args.signal_lengths)
	precision = int(args.precision)
	output_folder = args.output_folder
	total_num = int(args.total_num)
	#end_time = float(args.end_time)
	operators = ['U', 'F', 'G', '!', '&', '|']

	generator = SampleGenerator(formula_file=formula_file,
				sample_sizes=sample_sizes,
				signal_lengths=signal_lengths,
				output_folder=output_folder,
				total_num=total_num,
				precision=precision)

	generator.generateFromLargeSample()

if __name__=='__main__':
	main() 
