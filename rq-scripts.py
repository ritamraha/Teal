'''
Convinience script for running on benchmarks
'''
from learn_mtl import run_test
import glob,csv,shutil,multiprocessing
import argparse

def find_signalfiles(folder):

	signalfiles = []
	
	for f in glob.glob(folder + '/**/*.signal', recursive=True):
			signalfiles.append(f)

	return signalfiles

def compile_results(folder, outputcsv):

	header = ['file_name','Fr bound','Number of examples',\
				'Example length','Formula','Formula Size',\
				'Correct?','Total Time','Solving Time','Timeout']
	
	csvfile = open(outputcsv+'.csv', 'w')
	
	result_files = []
	for f in glob.glob(folder + '/**/*.csv', recursive=True):
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

def main():
	parser = argparse.ArgumentParser()

	parser.add_argument('--rq', '-r', dest='rq_num', default=1, type=int)
	parser.add_argument('--all', '-a', dest='all_files', default=False, action='store_true')
	parser.add_argument('--timeout', '-t', dest='timeout', default=600, type=int)

	args,unknown = parser.parse_known_args()
		
	all_files = args.all_files 
	rq_num = int(args.rq_num)
	timeout = int(args.timeout)

	if rq_num == 1:
		if all_files:
			folder = 'RQ1'
		else:
			folder = 'RQ1-subset'

		for file in find_signalfiles(folder):
			if 'bound-1' in file:
				fr_bound = 1
			elif 'bound-2' in file:
				fr_bound = 2
			elif 'bound-3' in file:
				fr_bound = 3

			print('############ Running %s with fr-bound %d ############'%(file, fr_bound))
			run_test(file_name=file, timeout=timeout, fr_bound=fr_bound)

		compile_results(folder=folder, outputcsv='RQ1-results')

	if rq_num == 2:
		if all_files:
			folder = 'RQ2'
		else:
			folder = 'RQ2-subset'

		for file in find_signalfiles(folder):
			for fr_bound in [1,2,3]:
				print('############ Running %s with fr-bound %d ############'%(file, fr_bound))
				run_test(file_name=file, timeout=timeout, fr_bound=fr_bound)


		compile_results(folder=folder, outputcsv='RQ2-results')

	if rq_num == 3:
		if all_files:
			folder = 'RQ3'
		else:
			folder = 'RQ3-subset'
		
		fr_bound = 2

		for file in find_signalfiles(folder):	
			print('############ Running %s with fr-bound %d ############'%(file, fr_bound))
			run_test(file_name=file, timeout=timeout, fr_bound=fr_bound)

		compile_results(folder=folder, outputcsv='RQ3-results')

if __name__ == '__main__':
    multiprocessing.freeze_support()  # Add this line to ensure multiprocessing works on macOS
    main()