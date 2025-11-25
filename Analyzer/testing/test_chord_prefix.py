import os
import time
import subprocess
import argparse
import glob
import re 
from datetime import datetime


# Function to parse command line arguments
def parse_arguments():
    parser = argparse.ArgumentParser(description="Test openChord implementation.")
    parser.add_argument(
        "-v", action="store_true", 
        help="Enable verbose output, print evaluation results)."
    )
    parser.add_argument(
        "-xml", action="store_true", 
        help="Enable verbose output, print xml generation information)."
    )

    # mutual_exclusive_group = parser.add_mutually_exclusive_group()
    # mutual_exclusive_group.add_argument(
    #     "-n", type=int, required=True,
    #     help="Set the number of operations for each evaluation."
    # )
    #
    # mutual_exclusive_group.add_argument("-l", "--line", required=True, type=int, default=None, nargs="*",
    #                     help="Sequence of line numbers to process")

    # parser.add_argument(
    #     "-n", type=int, required=True,
    #     help="Set the number of operations for each evaluation."
    # )

    parser.add_argument("-l", "--line", required=True, type=int, default=None, nargs="*",
                        help="Sequence of line numbers to process")

    parser.add_argument(
        "-d", type=str, required=True,
        help="Pattern to match test directories (e.g., 'tests/test1*')"
    )



    parser.add_argument(
        "-o", type=str, required=True,
        help="Output directory"
    )

    return parser.parse_args()


def make_output_filename(output_dir: str, exp_name : str, prefix: int) -> str:
    timestamp = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")

    filename = f"{exp_name}_timing_data_prefix_{prefix}_{timestamp}.csv"
    return os.path.join(output_dir, exp_name, filename)

# Set the environment variable
os.environ["ATL_MODEL"] = "DHTsATL.als"

# Parse command line arguments
args = parse_arguments()


# Output directory for results
results_dir = args.o
os.makedirs(results_dir, exist_ok=True)

os.makedirs("/tmp/nuno.policarpo", exist_ok=True)

verbose = args.v
verbose_xml = args.xml
# slice_size = args.n
prefixes = args.line
file_pattern = args.d

# Get the directory part of the pattern and the search pattern separately
# test_dir = os.path.dirname(test_pattern) or "."
# pattern = os.path.basename(test_pattern)



# def concatenate_files(output_file, input_files):
#     with open(output_file, 'w') as outfile:
#         for file_pattern in input_files:
#             for filename in glob.glob(file_pattern):
#                 print("Concatenating " + filename)
#                 try:
#                     with open(filename, 'r') as infile:
#                         outfile.write(infile.read())
#                 except Exception as e:
#                     print(f"Error reading {filename}: {e}", file=sys.stderr)
# Iterate over all directories matching the pattern
# for dir_name in os.listdir(test_dir):
#     full_dir_path = os.path.join(test_dir, dir_name)



cmd_compile = [
    "./script.sh", "compile",
]

subprocess.run(cmd_compile, check=False)


node_pattern = re.compile(r"(\d+)nodes")

for prefix_size in prefixes:

    print("-" * 20)
    print(f"Prefix size: {prefix_size}")

    for full_dir_path in glob.glob(file_pattern):

            print("-" * 20)
            print(f"Processing directory: {full_dir_path}")

            # Extract experiment name
            exp_name = os.path.basename(full_dir_path)

            # Extract log file name
            log_file = os.path.join(full_dir_path, f"{exp_name}.log")
            if not os.path.isfile(log_file):
                print(f"Log file not found in {full_dir_path}, skipping...")
                continue

            # Extract successor file name
            succ_file = os.path.join(full_dir_path, f"{exp_name}-successor.log")
            if not os.path.isfile(succ_file):
                print(f"Successor file not found in {full_dir_path}, skipping...")
                continue

            # Extract number of nodes
            node_result = node_pattern.search(exp_name)
            if node_result is None:
                print(f"Number of nodes not not found in {full_dir_path}, skipping...")
                continue
            nodes = node_result.group(1)

            # Extract successor file name
            succ_file = os.path.join(full_dir_path, f"{exp_name}-successor.log")
            if not os.path.isfile(succ_file):
                print(f"Successor file not found in {full_dir_path}, skipping...")

            # Process with two max-lines values: 1 and 2

            log_size = 0

            with open(log_file, "rb") as f:
                log_size = sum(1 for _ in f)

            if True:
                print(f"Processing from line {0} to line {prefix_size}...")

                # Output files
                os.makedirs(os.path.join(results_dir, exp_name), exist_ok=True)
                out_file = f"/tmp/nuno.policarpo/{exp_name}_out_prefix_{prefix_size}.xml"
                log_time_file = os.path.join(results_dir, exp_name, f"{exp_name}_timing_prefix_{prefix_size}.txt")
                output_run_file = os.path.join(results_dir, exp_name, f"{exp_name}_run_prefix_{prefix_size}.txt")
                output_csv_file = make_output_filename(results_dir, exp_name, prefix_size)


                # Execute the first command and measure time
                start_time = time.time()
                cmd_xml = [
                    "./script.sh", "xml",
                    "-f", log_file,
                    "-i", succ_file,
                    "-o", out_file,
                    "-p", "ChordIdeal.py",
                    # "--starting-line", str(starting_line),
                    "--line-count",  str(prefix_size),
                    "-store",
                    "-lookup",
                    "-findnode",
                    "-member",
                    "-read-only",
                    "-stable",
                    "-ideal",
                ]

                if verbose_xml:
                    subprocess.run(cmd_xml, check=False)
                else:
                    subprocess.run(cmd_xml, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False)

                xml_time = time.time() - start_time

                # Save time taken for the first command
                with open(log_time_file, "w") as log_file_handle:
                    xml_measurement = f"XML generation from prefix of {prefix_size} lines: {xml_time:.2f} seconds"
                    log_file_handle.write(xml_measurement + "\n")
                    print(xml_measurement)

                # Execute the second command and measure time
                start_time = time.time()
                cmd_run = ["./script.sh", "run", out_file, output_csv_file]
                with open(output_run_file, "w") as output_run:
                    # Create a subprocess and pipe the output to both stdout and the file using tee
                    process = subprocess.Popen(cmd_run, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
                    assert process.stdout is not None
                    for line in process.stdout:
                        line_str = line.decode("utf-8")
                        if verbose:
                            print(line_str, end='')  # Print to stdout
                        output_run.write(line_str)  # Write to the file
                    process.wait()  # Wait for the command to finish
                evaluation_time = time.time() - start_time

                # Save time taken for the second command
                with open(log_time_file, "a") as log_file_handle:
                    evaluation_measurement = f"Evaluation from prefix of {prefix_size} lines: {evaluation_time:.2f} seconds"
                    log_file_handle.write(evaluation_measurement + "\n")
                    log_file_handle.write(f"Nodes: {nodes}\n")
                    print(evaluation_measurement)



                # Append times to the execution output file
                with open(output_run_file, "a") as output_run:
                    output_run.write(xml_measurement + "\n" + evaluation_measurement + "\n")
                    output_run.write(f"Nodes: {nodes}\n")

                # Save the execution output
                print(f"Output saved to {output_run_file}\n")

                print(f"CSV output saved to {output_csv_file}\n")

                # break
                # exit()

            # break  
