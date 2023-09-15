# TEAL: synThesizing Efficiently monitorAble mtL
*TEAL* is a Python-based tool for synthesizing formulas in Metric Temporal Logic for efficient Runtime monitoring.
It relies on solving constraint satisfaction problem using the SMT solver Z3.


### Installation

Clone the repository and switch to the root directory using the following:
```
git clone https://github.com/ritamraha/Teal.git
cd TEAL/
```

Now, set up a python virtual environment for running *TEAL*: 
```
virutalenv -p python3 venv
source venv/bin/activate
```
Finally, install the required python packages using the following:
```
pip install -r requirements.txt
```
*TEAL* is now ready to use.


### Running
One can run *TEAL* by simply running `python3 main.py`.
By default, this will run *TEAL* on `example.signal` with a future-reach bound of 2.  


#### Parameters
There are a variety of arguments that one can use to run *TEAL*, as listed below:

|Argument        |Meaning
|----------------|------------------------------
|-i <input_sample>| For specifying the input sample; default is `example.signal`.
|-f <fr_bound>| For specifying the future-reach bound of the prospective formula; default is 2
|-t <timeout>| For specifying the timeout; default is 600 sec
|-o <outputcsv>| For specifying the csv file with the output results; default is `results.csv`
|-m | For specifying whether the prospective formula should be *globally* separating or only separating; default is globally separating


#### Input sample format:
The input sample file consists of three parts separated using `---`.
The first part contains the list of positive signals, the second part the negative signals and the third part the end time point of the signals.
The signals in the sample file are piecewise-constant signals.
Each signal is represented as a sequence, separated using `;`, of a timepoint and a letter that holds at that timepoint, separated using `:`. 
Each letter represents the truth value of atomic propositions.
An example of a trace is `0.0:1,0;1.2:1,1` which consists of two timepoints 0.0 and 1.2. In the first timepoint only `p` holds,
while in the second timepoint both `p,q` hold.
```
0.0:1,1;1.0:0,1;2.5:1,1;2.8:1,1
0.0:0,0;0.2:0,0;1.7:0,1;2.0:1,1
0.0:0,1;2.0:1,0;2.8:0,1;2.9:0,0
0.0:1,0;2.8:1,1;3.0:0,0;3.6:1,0
0.0:1,0;2.1:1,0;3.4:0,0;3.5:0,0
---
0.0:0,0;1.9:0,1;2.3:0,1;3.9:0,0
0.0:0,0;1.2:1,1;1.4:0,0;1.8:0,1
0.0:0,0;2.6:0,0;2.9:0,1;3.7:0,0
0.0:0,1;0.4:0,1;2.9:1,0;3.3:0,1
0.0:1,1;0.1:0,1;2.5:0,0;3.1:1,0
---
4
```
The input file must use the extension `.signal`.


### Running using script (on benchmarks)
One can run *TEAL* on the benchmarks used for the research questions in the paper using a convenience script.
For this, run the following command `python3 rq-scripts.py` which allows the following parameters:
|Argument        |Meaning
|----------------|------------------------------
|-r <rq_num>| For specifying experiments from which research question should be run; default is 1.
|-a | For specifying whether all benchmarks from the research question should be run; by default, it only runs on a subset.
|-t <timeout> | For specifying the timeout for each run of the experiment; default is 600 secs

The above script produces a csv file with the results of the experiments for the specified reserach question.

While it is possible to run all the benchmarks using the provided script, please be aware that this task demands a substantial amount of resources both in terms of hardware and time. The benchmark suite contains 144 samples for each of the research questions, and it was executed in parallel (20 runs in each iteration) with a timeout set to 5400 seconds. The computations were performed on a Computer Grid within cluster machines equipped with the following hardware configuration:

- **CPU:** 2x AMD EPYC 7702 64-Core Processor
  - **Number of CPU Cores:** 2x 64
  - **Clock Speed:** 2.0 GHz
  - **Max Turbo Frequency:** 3.35 GHz
  - **L3 Cache:** 256 MB
  - **Lithography:** 7 nm
  - **Max TDP:** 200 W
  - **Hyper-Threading Technology:** Yes
  - **Virtualization Technology (VT-x):** Yes

- **Memory:** 2 Terabytes
  - **Type:** DDR4
  - **Speed:** 3200 MHz
  - **ECC:** Enabled

- **Disk:** 2x 240GB SSD

Running the complete benchmark suite involves executing the TEAL tool 720 times (once for RQ1 and RQ3, and twice for RQ2 for each sample). When run sequentially, this comprehensive set of benchmarks can potentially consume more than 150 CPU hours.

To expedite the benchmarking process, we recommend running the tool on a provided benchmark subset. This subset comprises samples of the smallest size for each formula, configured to run with three different future-reach bounds. These results are representative of the outcomes obtained from the full benchmark suite, making them a more efficient choice for most use cases.
