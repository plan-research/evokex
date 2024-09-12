import os
import shutil
from pathlib import Path
import sys

def copy_files_with_specific_name(src_dir, dest_dir, file_name):
    # Ensure the destination directory exists
    os.makedirs(dest_dir, exist_ok=True)

    # Walk through the source directory
    for root, dirs, files in os.walk(src_dir):
        for file in files:
            if file == file_name:
                # Calculate the relative path of the file
                rel_path = os.path.relpath(root, src_dir)
                # Construct the destination path
                dest_path = os.path.join(dest_dir, rel_path)
                os.makedirs(dest_path, exist_ok=True)
                # Copy the file to the destination path
                shutil.copy(os.path.join(root, file), os.path.join(dest_path, file))
                print(f"Copied: {os.path.join(root, file)} to {os.path.join(dest_path, file)}")

# Example usage
src_directory = sys.argv[1]
dest_directory = sys.argv[2]
a = ['work-stat.log', 'coverage-info.log']

for f in a:
    copy_files_with_specific_name(src_directory, dest_directory, f)
