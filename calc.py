import pandas as pd

# Read the CSV file into a pandas DataFrame
df = pd.read_csv('all-results-form-1.csv')

# Group the data by 'Number of examples' and calculate the average of 'Solving Time'
average_times = df.groupby('Example length')['Total Time'].mean()

# Display the average times for each 'Number of examples'
print(average_times)

