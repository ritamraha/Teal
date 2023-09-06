#!/bin/bash
#
#SBATCH --partition=a100        # Use GPU partition "a100"
#SBATCH --gres gpu:2            # set 2 GPUs per job
#SBATCH -c 15                   # Number of cores
#SBATCH -N 1                    # Ensure that all cores are on one machine
#SBATCH -t 0-00:20              # Maximum run-time in D-HH:MM
#SBATCH --mem=10G               # Memory pool for all cores (see also --mem-per-cpu)
#SBATCH -o hostname_%j.out      # File to which STDOUT will be written
#SBATCH -e hostname_%j.err      # File to which STDERR will be written

folder="AV-benchmarks/signalsFiles" #specify the folder on which to run on
num_workers=48 #specify the number of cores to be used
time_out=7200


for signal_file in $(find "$folder" -type f -name "*.signal"); do

    python learn_mtl.py -i $signal_file