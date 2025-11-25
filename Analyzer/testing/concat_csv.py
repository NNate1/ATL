import pandas as pd
import glob
import os
import argparse

def main():
    parser = argparse.ArgumentParser(description="Concatenate timing data CSV files.")
    parser.add_argument("-d", "--input-dir", required=True, help="Root directory to search for CSV files")
    parser.add_argument("-o", "--output-file", required=True, help="Path to save the combined CSV file")

    args = parser.parse_args()

    # Recursively find all matching CSV files
    csv_files = glob.glob(os.path.join(args.input_dir, "**", "*_timing_data_prefix_*.csv"), recursive=True)

    if not csv_files:
        print("No matching CSV files found.")
        return

    print(f"Found {len(csv_files)} CSV files.")

    # Read and concatenate, optionally adding source file info
    df_list = []
    for f in csv_files:
        print(f"Processing file: {f}")
        try:
            df = pd.read_csv(f)
            df['source_file'] = os.path.basename(f)  # Optional: track source file
            df_list.append(df)
        except pd.errors.EmptyDataError:
            print(f"{f} is empty")

    combined_df = pd.concat(df_list, ignore_index=True)

    combined_df.to_csv(args.output_file, index=False)
    print(f"Combined CSV written to {args.output_file}")

if __name__ == "__main__":
    main()
