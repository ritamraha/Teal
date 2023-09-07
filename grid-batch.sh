#!/bin/bash
#
#SBATCH -w spyder2[0-3]        # Use spyder
#SBATCH -c 1                   # Number of cores
#SBATCH -N 1                    # Ensure that all cores are on one machine
#SBATCH -t 0-02:00              # Maximum run-time in D-HH:MM
#SBATCH --mem=100G               # Memory pool for all cores (see also --mem-per-cpu)
#SBATCH -o hostname_%A_%a.out   # File to which STDOUT will be written
#SBATCH -e hostname_%A_%a.err   # File to which STDERR will be written
#SBATCH --array=1-$(find "$folder" -type f -name "*.signal" | wc -l) # Number of tasks in the array

folder="scalability-benchmarks/signalsFiles" # specify the folder on which to run on

# Get the list of signal files
signal_files=($(find "$folder" -type f -name "*.signal"))

# Get the current signal_file for this task
current_signal_file=${signal_files[$SLURM_ARRAY_TASK_ID - 1]}

python learn_mtl.py -i "$current_signal_file" -f 2
