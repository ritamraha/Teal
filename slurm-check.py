import time
import argparse

# Example usage:
parser = argparse.ArgumentParser()
parser.add_argument('-i', dest='i', default = '2')
args,unknown = parser.parse_known_args()

i = int(args.i)

time.sleep(5)
    
# Open a text file in write mode and write the integer
with open('output-%d.txt'%i, 'w') as file:
	file.write(str(i))


