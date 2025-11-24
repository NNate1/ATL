#!/bin/bash

concat="$(realpath "./concat.py")"
sort="$(realpath "./logsorter.py")"

if [ "$#" -ne 2 ]; then
	echo "Usage: $0 <directory with experiments> <output_dir>"
	exit 1
fi

dir=$1
output_dir=$2
missing_logs_file="$output_dir/missing_experiments.log"
complete_logs_file="$output_dir/complete_experiments.log"

# Clear the missing logs file before starting
mkdir -p "$output_dir"
true >"$missing_logs_file"

for exp in "$dir"/*; do
	echo "Processing: $exp"

	if [ -d "$exp" ]; then

		# Extract the experiment folder name
		exp_name=$(basename "$exp")
		exp_output_dir="${output_dir}/${exp_name}"
		mkdir -p "$exp_output_dir"

		output_log="${exp_output_dir}/${exp_name}.log"
		output_successor_log="${exp_output_dir}/${exp_name}-successor.log"

		# Flag to track missing logs
		missing_logs=false

		# Process main logs
		if ls "$exp"/*/openchord-*.log 1>/dev/null 2>&1; then
			python3 "${concat}" "$output_log" "$exp"/*/openchord-*.log

			python3 "${sort}" "$output_log" tmp2.log
			mv tmp2.log "$output_log"
		else
			echo "No openchord logs found in $exp" >&2
			missing_logs=true
		fi

		# Process successor logs only if main logs exist
		if [ "$missing_logs" = false ]; then
			if ls "$exp"/*/*cessor-change.log 1>/dev/null 2>&1; then
				python3 "${concat}" "$output_successor_log" "$exp"/*/*cessor-change.log

				python3 "${sort}" "$output_successor_log" tmp2.log
				mv tmp2.log "$output_successor_log"
			else
				echo "No successor logs found in $exp" >&2
				missing_logs=true
			fi
		fi

		# Record missing logs
		if [ "$missing_logs" = true ]; then
			echo "No logs found in $exp"
			echo "$exp" >>"$missing_logs_file"

			# Delete the experiment directory if logs are missing
			rm -rf "$exp_output_dir"
		else
			# Record successful experiment
			echo "$exp" >>"$complete_logs_file"
		fi
	fi
done

echo "Missing experiment logs have been recorded in: $missing_logs_file"
