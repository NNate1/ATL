import sys
import glob

def concatenate_files(output_file, input_files):
    with open(output_file, 'w') as outfile:
        for file_pattern in input_files:
            for filename in glob.glob(file_pattern):
                # print("Concatenating " + filename)
                try:
                    with open(filename, 'r') as infile:
                        outfile.write(infile.read())
                except Exception as e:
                    print(f"Error reading {filename}: {e}", file=sys.stderr)

if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("Usage: python concat.py output_file input_files...")
        sys.exit(1)



    output_file = sys.argv[1]
    input_files = sys.argv[2:]

    concatenate_files(output_file, input_files)
