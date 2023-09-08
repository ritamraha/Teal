from rq import Queue, Worker, Connection
from redis import Redis
from random import seed
from random import random
import csv
import os
import glob
import argparse
from learn_mtl import run_test
import datetime

class multiprocess:

	def __init__(self, benchmark_folder, timeout):
		
		self.benchmark_folder = benchmark_folder
		self.timeout = timeout
		self.signal_list = []
		

		for f in glob.glob(self.benchmark_folder + '/**/*.signal', recursive=True):
			self.signal_list.append(f)

		self.compiled_filename = 'all-results'+self.benchmark_folder
		

	def populate_queue(self):
		
		redis_conn= Redis()
		q = Queue('runMTL', connection=redis_conn)
		q.empty()

		for file in self.signal_list:
			for fr_bound in [1,2,3]:
				q.enqueue(run_test, args=(file,self.timeout, fr_bound),\
									job_timeout=self.timeout)
				

		print('Length of queue', len(q))

	
	def compile_results(self):

		header = ['file_name','Fr bound','Number of examples','Example length','Formula','Formula Size','Correct?','Total Time','Solving Time','Timeout']
		
		csvfile = open(self.compiled_filename+'.csv', 'w')
		
		result_files = []
		for f in glob.glob(self.benchmark_folder + '/**/*.csv', recursive=True):
			result_files.append(f)
		
		# with open(result_files[0], 'r') as f:
		# 	data = list(csv.DictReader(f))[0]
		# 	header = list(data.keys())
		
		# print(header)
		writer = csv.DictWriter(csvfile, fieldnames = header)
		writer.writeheader()

		for file in result_files:
				
			with open(file, 'r') as f:
				data = csv.DictReader(f)
				for row in data:
					
					writer.writerow(row)
					
		csvfile.close()


	def clean_files(self):

		results_list = []

		for f in glob.glob(self.benchmark_folder + '/**/*.csv', recursive=True):
			results_list.append(f)

		for file in results_list:
			os.remove(file)


def main():
	parser = argparse.ArgumentParser()
	parser.add_argument('--benchmark_folder', '-b', dest='benchmark_folder', default="small_benchmarks")
	parser.add_argument('--compile', '-c', dest='compile_results', action='store_true', default=True)
	parser.add_argument('--timeout', dest='timeout', default=7200)

	args,unknown = parser.parse_known_args()

	benchmark_folder = args.benchmark_folder
	timeout = int(args.timeout)
	compile_results = bool(args.compile_results)

	m = multiprocess(benchmark_folder, timeout)

	if compile_results:
		
		m.compile_results()
		#m.clean_files()
		
	else:
		m.populate_queue()


if __name__ == '__main__':
    main() 
 
