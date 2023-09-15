import os

folder_path = 'scalable-max/signalsFiles/'  # Replace with the path to your folder


# Get a list of all files in the folder
file_list = os.listdir(folder_path)


# Iterate through the files and rename them
for old_name in file_list:
    # Construct the new name using the pattern
    new_name = old_name.replace('f:02', 'f:04')
    
    # Build the full paths to the old and new names
    old_path = os.path.join(folder_path, old_name)
    new_path = os.path.join(folder_path, new_name)
    
    # Rename the file
    os.rename(old_path, new_path)
    
    
print("Files have been renamed.") 
