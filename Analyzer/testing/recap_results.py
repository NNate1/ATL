import os
import glob
import re
import argparse
from collections import defaultdict

def parse_files(input_pattern, output_file):
    # Dictionary to count occurrences of true/false for each expression
    evaluation_counts = defaultdict(lambda: {'true': 0, 'false': 0, 'No' : 0})
    false_files = defaultdict(list)
    
    # Regular expression to match evaluation lines
    # evaluation_regex = re.compile(r"^(\w+):\s+(true|false)\s+([\d\.]+)s$")

    evaluation_regex = re.compile(r"^(\w+):\s+(true|false|No)\s+(.*)s$")
    
    # Process each matching file
    for file_path in glob.glob(input_pattern):
        print(f"Processing file: {file_path}")
        with open(file_path, 'r') as file:
            for line in file:
                match = evaluation_regex.match(line.strip())
                if match:
                    expression, result, _ = match.groups()
                    assert result in ['true', 'false', 'No']
                    evaluation_counts[expression][result] += 1
                    if result == 'false':
                        false_files[expression].append(file_path)
    
    # Write output report
    with open(output_file, 'w') as out:
        for expression, counts in evaluation_counts.items():
            out.write(f"{expression}: true={counts['true']}, false={counts['false']}, not applicable={counts['No']}\n")

        for expression, files in false_files.items():
            if len(false_files) > 0:
                out.write(f"\nFalse results for {expression}:\n " + '\n '.join(files) + "\n")

    print(f"Report saved to {output_file}")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Process evaluation result files.")
    parser.add_argument("-d", type=str, required=True, help="Directory with results")
    parser.add_argument("-o", type=str, required=True, help="Output report file")
    args = parser.parse_args()

    pattern = os.path.join(args.d, "*/*run*.txt")
    print(f"Analyzing files matching pattern: {pattern}")
    parse_files(pattern, args.o)
