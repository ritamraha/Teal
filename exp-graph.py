'''
Convenience script for generating experimental results of the paper
'''
import pandas as pd
import argparse
import matplotlib.pyplot as plt

og_formula_pattern = {'f:01': 'Bounded Recurrence', 'f:02': 'Bounded Response', 'f:03': 'Bounded Invariance', 'f:04': 'Bounded Until'}

def extract_formula(file_name):
	return og_formula_pattern[list(file_name.split('/'))[-1][:4]]

def main():

	parser = argparse.ArgumentParser()

	parser.add_argument('--graph', '-g', dest='graph', default='tbl3', choices=['tbl3', 'fig2'], type=str)
	parser.add_argument('--all', '-a', dest='all_files', default=False, action='store_true')

	args,unknown = parser.parse_known_args()
		
	graph = args.graph
	all_files = args.all_files

	if graph == 'tbl3':

		if all_files:
			df = pd.read_csv('RQ-1-2-all-results.csv')
			filename_suffix = 'original'
		else:
			df = pd.read_csv('RQ1-results.csv')
			filename_suffix = 'subset'
		
		timeout = df['Timeout'].iloc[0]
		df['Original Formula'] = df['file_name'].apply(extract_formula)



		timeouts_count = df[df['Total Time'] == timeout].groupby('Original Formula').size()
		timeouts_count = timeouts_count.rename('Timeouts Count')
		non_timeouts_data = df[df['Total Time'] < timeout]

		average_times = non_timeouts_data.groupby('Original Formula')['Total Time'].mean()
		average_size = df.groupby('Original Formula')['Formula Size'].mean()
		
		merged_series = pd.merge(average_size, average_times, on='Original Formula')
		merged_series = pd.merge(merged_series, timeouts_count, on='Original Formula', how='left')
		merged_series['Timeouts Count'] = merged_series['Timeouts Count'].fillna(0).astype(int)
		merged_series = merged_series.rename(columns={'Total Time': 'Average Time', 'Formula Size': 'Average Size'})

		merged_series = merged_series[['Timeouts Count', 'Average Size', 'Average Time']]

		print(merged_series)

		merged_series.to_csv('Table3-'+filename_suffix+'.csv')

	elif graph == 'fig2':
		
		if all_files:
			df = pd.read_csv('RQ3-all-results.csv')
			filename_suffix = 'original'
		else:
			df = pd.read_csv('RQ3-results.csv')
			filename_suffix = 'subset'
		
		timeout = df['Timeout'].iloc[0]
		timeout_buffer = 1000
		figure_dim = (10,5)
		timeout_len, timeout_size = 12, 80

		df['Original Formula'] = df['file_name'].apply(extract_formula)

		plt.figure(figsize=figure_dim)
		plt.subplot(1, 2, 1)
		for f in og_formula_pattern:
			formula = og_formula_pattern[f]
			timeout_cond = (df['Original Formula'] == formula) & (df['Example length']<timeout_len)
			grouped_data = df[timeout_cond].groupby('Number of examples')['Total Time'].mean()
			plt.yscale('log')
			plt.ylim(1, timeout+timeout_buffer)
			plt.plot(grouped_data.index, grouped_data.values, marker='o', linestyle='-', label=formula)
			plt.xlabel('Number of prefixes')
			plt.ylabel('Running time (in sec)')
			plt.title('Runtime increase with number of prefixes')

		plt.subplot(1, 2, 2)
		for f in og_formula_pattern:
			formula = og_formula_pattern[f]
			timeout_cond = (df['Original Formula'] == formula) & (df['Number of examples']<timeout_size)
			grouped_data = df[timeout_cond].groupby('Example length')['Total Time'].mean()
			plt.yscale('log')
			plt.ylim(1, timeout+timeout_buffer)
			plt.plot(grouped_data.index, grouped_data.values, marker='o', linestyle='-', label=formula)
			plt.xlabel('Length of prefixes')
			plt.ylabel('Running time (in sec)')
			plt.title('Runtime increase with length of prefixes')


		plt.legend()
		plt.tight_layout()
		#plt.show()
		plt.savefig('Figure2-' + filename_suffix)


if __name__ == '__main__':
	main()
