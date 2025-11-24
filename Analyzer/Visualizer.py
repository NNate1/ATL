import matplotlib.pyplot as plt
import matplotlib.dates as mdates
from datetime import datetime
from Operations import * 


def generate_color_map(classes, use_fixed_colors=True):
    fixed_colors = {
        "ReadOnly": "blue",
        "Stable": "green",
        "MemberStart": "orange",
        "IdealStart": "purple",
        "ResponsibleStart": "magenta",
        "Store": "brown",
        "Lookup": "yellow",
        "FindNode": "gray",
        "Join": "lime",
        "Leave": "teal",
        "Fail": "red",
    }
    
    color_map = {}
    
    for cls in classes:
        # color_map[cls] = fixed_colors.get(cls, "#" + ''.join(random.choices('0123456789ABCDEF', k=6)))
        color_map[cls] = fixed_colors.get(cls)
    return color_map

# Function to parse datetime with milliseconds
def parse_time(time_str : str):
    return datetime.strptime(time_str, "%Y-%m-%d %H:%M:%S.%f")

def visualize_intervals(data, use_fixed_colors=True):
    
    fig, ax = plt.subplots(figsize=(12, 6))
    
    intervals = sorted(data.values(), key=lambda x: x.get_time())  # Sort by start time
    unique_types = set(obj.__class__.__name__ for obj in intervals)
    color_map = generate_color_map(unique_types, use_fixed_colors)
    
    min_time = min(parse_time(obj.get_time()) for obj in intervals)
    max_time = max(parse_time(obj.get_end_time()) if obj.get_end_time() else parse_time(obj.get_time()) for obj in intervals)
    
    print(min_time, max_time)


    filtered_intervals = [obj for obj in intervals if not obj.is_end()]

    for i, interval in enumerate(filtered_intervals):

        start = parse_time(interval.get_time())
        end = parse_time(interval.get_end_time()) if interval.get_end_time() else max_time
        # duration = (end - start).total_seconds()

        print(start, end, interval.get_name())

        # ax.barh(i, duration, left=start, color=color_map[obj.__class__.__name__], label=obj.get_name() if i == 0 else "")
        # ax.text(start, i, obj.get_name(), va='center', fontsize=8, color='white', weight='bold')


        # Draw the interval
        ax.hlines(y=i, xmin=start, xmax=end, color=color_map[interval.__class__.__name__], linewidth=3)
        
        # Add start and end markers
        ax.scatter(start, i, color=color_map[interval.__class__.__name__], s=50)

        if interval.get_end_time():
            ax.scatter(end, i, color=color_map[interval.__class__.__name__], s=50)


        mid_time = start + (end - start) / 2
        ax.text(mid_time, i, interval.visualize(), ha="center", va="bottom", fontsize=10, color="black")

        
        # Add labels
        # ax.text((start + end) / 2, i, label, ha="center", va="bottom", fontsize=10, color="black")
    
    # Set Y-axis labels
    ax.set_yticks(range(len(filtered_intervals)))
    ax.set_yticklabels([obj.get_name() for obj in filtered_intervals])

    # Format X-axis to show time with milliseconds
    ax.xaxis.set_major_formatter(mdates.DateFormatter('%H:%M:%S'))
    ax.set_xlabel("Time")
    ax.set_title("DHT Operation Intervals")

    plt.xticks(rotation=45)
    plt.grid(True, which='both', linestyle='--', linewidth=0.5)
    plt.show()

if __name__ == "__main__":
    # Example usage:
    data = {
        "1": ReadOnly("2025-02-27 14:00:00.0123", "op1"),
        "2": Stable("2025-02-27 14:01:30.0456", "op2"),
        "3": Lookup("2025-02-27 14:02:45.0789", "Lookup", "op3", 1, "NodeA", "KeyX")
    }
    data["1"].set_end_time("2025-02-27 14:01:00.0000")
    data["2"].set_end_time("2025-02-27 14:08:00.0000")
    # data["3"].set_end_time("2025-02-27 12:15:00")

    visualize_intervals(data, use_fixed_colors=True)
