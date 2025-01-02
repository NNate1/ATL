import sys
import argparse
from io import TextIOWrapper


def normalize_timestamp( timestamp: str) -> str:
    time_parts = timestamp.split(":")
    second_and_millis = time_parts[2].split(".")
    
    hour = time_parts[0].zfill(2)
    minute = time_parts[1].zfill(2)
    second = second_and_millis[0].zfill(2)
    millis = second_and_millis[1].zfill(3)
    
    return f"{hour}:{minute}:{second}.{millis}"

def order_log(log: TextIOWrapper) -> list[str]:

    processed_entries = []

    for i, line in enumerate(log, 1):
        if i > 0 and i % 1000 == 0:
            print(f"Processed {i} lines...")

        datetime, event = line.split(", ", 1)

        date, timestamp = datetime.split(" ")

        formatted_entry = f"{date} {normalize_timestamp(timestamp)}, {event}"

        processed_entries.append(formatted_entry)


    processed_entries.sort()

    return processed_entries

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description='Order logs')


    parser.add_argument('log', type=str, help='Path to the input log file.')
    parser.add_argument('output', type=str, help='Path to the output log file.')
    # parser.add_argument('--verbose', action='store_true', help='Enable verbose output.')

    args = parser.parse_args(sys.argv[1::])

    ordered_log = []
    with open(args.log, 'r') as f:
        
        ordered_log = order_log(f)

    with open(args.output, 'w') as out:
        for entry in ordered_log:
            out.write(entry)

