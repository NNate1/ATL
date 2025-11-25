#!/bin/bash

ANALYZER_PY="../Analyzer_no_Visualizer.py"

ATL_MODEL="../../Models/DHTsATL.als"
# DHTS_ATL="DHTsATL.als"

EVALUATOR_DIR=".."
EVALUATOR_FILE="$EVALUATOR_DIR/Evaluator.java"
EVALUATOR_CLASS="$EVALUATOR_DIR/Evaluator.class"
EVALUATOR="Evaluator"

# NOTE: Set the alloy jar path
ALLOY_JAR="$EVALUATOR_DIR/alloy_6.2.jar"

# Compile the Evaluator
compile() {
	echo "Compiling Evaluator.java..."
	if javac --class-path $ALLOY_JAR $EVALUATOR_FILE; then
		echo "Compilation successful."
	else
		echo "Compilation failed."
		exit 1
	fi
}

# Clean up
clean() {
	echo "Cleaning up compiled files..."
	for file in "$EVALUATOR_DIR"/*.class; do
		rm -f "$file"
		echo "Removed: $file"
	done
}

# Execute the Evaluator
run() {
	# Check if the Evaluator.class file exists, compile if it doesn't
	[ -f $EVALUATOR_CLASS ] || compile

	source .env || export ATL_MODEL="../../Models/DHTsATL.als"
	#java -Xmx128g -cp $ALLOY_JAR:$EVALUATOR_DIR $EVALUATOR "$@"
	java -Xmx250g -cp $ALLOY_JAR:$EVALUATOR_DIR $EVALUATOR "$@"
}

# Generate trace XML
xml() {

	python3 $ANALYZER_PY "$@"

}

# Display help
show_help() {
	echo "Usage: ./script.sh [command] [options]"
	echo
	echo "Commands:"
	echo "  compile           Compile the Evaluator.java file"
	echo "  clean             Remove compiled class files"
	echo "  run [FILE]	  Evaluate the xml log"
}

# Parse the script arguments
while (($#)); do
	case "$1" in
	compile)
		compile
		;;
	clean)
		clean
		;;
	run)
		shift
		run "$@"
		exit
		;;
	xml)
		shift
		xml "$@"
		exit
		;;
	help | *)
		show_help
		exit
		;;
	esac
	shift
done
