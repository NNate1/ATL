import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.XMLNode;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4SolutionReader;

import java.time.Instant;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

public class Evaluator {
	public static void main(String[] args) throws Exception {
		if (args.length < 2) {
			System.out.println("Usage: java Evaluator <trace_file> <output_csv>");
			return;
		}

		String filename = args[0];
		int index = filename.lastIndexOf(File.separator);
		String baseFilename = filename.substring(index + 1);

		String csvOutputFile = args[1];

		String sourcepath = System.getenv("ATL_MODEL");

		if (sourcepath == null) {

			System.out.println("ATL_MODEL environment variable not set.");
			System.out.println(
					"Set the ATL_MODEL environment variable to the path of the Alloy ATL model file.");
			return;

		}

		String flagComment;
		String infoComment;

		try (BufferedReader reader = new BufferedReader(new FileReader(filename))) {
			infoComment = reader.readLine().replace("<!--", "").replace("-->", "").trim();

			flagComment = reader.readLine().replace("<!--", "").replace("-->", "").trim();

		} catch (Exception e) {
			System.out.println(e.getMessage());
			return;
		}

		int lineCount = -1;
		int originalTraceLength = -1;
		int processedTraceLength = -1;
		int nodes = -1;
		int maxNodes = -1;

		// Obtain information for csv entry from xml comment

		String[] tokens = infoComment.split("\\s+");
		for (String token : tokens) {
			if (token.contains("=")) {
				String[] parts = token.split("=");
				if (parts.length == 2) {
					String key = parts[0].trim();
					String value = parts[1].trim();

					switch (key) {
						case "line_count":
							lineCount = Integer.parseInt(value);
							break;
						case "original_trace_length":
							originalTraceLength = Integer.parseInt(value);
							break;
						case "processed_trace_length":
							processedTraceLength = Integer.parseInt(value);
							break;
						case "nodes":
							nodes = Integer.parseInt(value);
							break;

						case "max_nodes":
							maxNodes = Integer.parseInt(value);
							break;
					}
				}
			}
		}

		System.out.println(infoComment);
		System.out.println("line_count: " + lineCount + ", original_trace_length: " + originalTraceLength
				+ ", processed_trace_length: " + processedTraceLength + ", nodes: " + nodes
				+ ", max_nodes: " + maxNodes);

		var flags = new HashMap<String, Boolean>();
		final String ALL = "all";
		final String STORE = "store";
		final String LOOKUP = "lookup";
		final String FINDNODE = "find";
		final String MEMBERSHIP = "membership";
		final String READ_ONLY = "read_only";
		final String STABLE = "stable";
		final String IDEAL = "ideal";
		final String RESPONSIBILITY = "responsible";

		flags.put(ALL, flagComment.contains(ALL));
		flags.put(STORE, flagComment.contains(STORE));
		flags.put(LOOKUP, flagComment.contains(LOOKUP));
		flags.put(FINDNODE, flagComment.contains(FINDNODE));
		flags.put(MEMBERSHIP, flagComment.contains(MEMBERSHIP));
		flags.put(READ_ONLY, flagComment.contains(READ_ONLY));
		flags.put(STABLE, flagComment.contains(STABLE));
		flags.put(IDEAL, flagComment.contains(IDEAL));
		flags.put(RESPONSIBILITY, flagComment.contains(RESPONSIBILITY));

		// System.out.println(flagComment);
		// System.out.println(flags);

		// String[] expressions = {
		// "LookupConsistency",
		// "ValueConsistency",
		// "ValueFreshness",
		// "WeakValueFreshness",
		// "KeyConsistency",
		// "Reachability",
		// // "MembershipGuarantee",
		// "MembershipGuarantee_Responsible",
		// "MembershipGuarantee_Replier",
		// "FindNodeLookupConsistency",
		// "ResponsibilityTransfer",
		// "ResponsibilityExpiration",
		// "TerminationCompleteness",
		// };

		List<String> expressions = new ArrayList<>();

		if (flags.get(LOOKUP) && flags.get(STORE)) {
			expressions.add("LookupConsistency");
		}

		if (flags.get(LOOKUP) && flags.get(STORE) && flags.get(READ_ONLY) && flags.get(IDEAL)) {
			expressions.add("ValueConsistency");

			expressions.add("WeakValueFreshness");
		}
		if (flags.get(LOOKUP) && flags.get(STORE) && flags.get(IDEAL)) {
			expressions.add("ValueFreshness");
		}

		if (flags.get(FINDNODE) && flags.get(IDEAL) && flags.get(STABLE)) {
			expressions.add("KeyConsistency");
		}

		if (flags.get(FINDNODE) && flags.get(LOOKUP) && flags.get(RESPONSIBILITY)) {
			expressions.add("FindNodeLookupConsistency");
		}

		if (flags.get(FINDNODE) && flags.get(MEMBERSHIP) && flags.get(RESPONSIBILITY)) {
			expressions.add("ResponsibilityExpiration");
		}

		if (flags.get(FINDNODE) && flags.get(MEMBERSHIP)) {
			expressions.add("ResponsibilityTransfer");
			// expressions.add("ResponsibilityTransferV2");
			// expressions.add("ResponsibilityTransferV3");
		}

		// if (flags.get(FINDNODE) && flags.get(MEMBERSHIP) &&
		// flags.get(RESPONSIBILITY)) {
		if (flags.get(FINDNODE) && flags.get(MEMBERSHIP)) {

			expressions.add("MembershipGuarantee_Responsible");
		}

		// if (flags.get(FINDNODE) && flags.get(STORE) && flags.get(LOOKUP) &&
		// flags.get(MEMBERSHIP)
		// && flags.get(RESPONSIBILITY)) {

		if ((flags.get(FINDNODE) || flags.get(STORE) || flags.get(LOOKUP)) && flags.get(MEMBERSHIP)) {
			expressions.add("MembershipGuarantee_Replier");
			expressions.add("MembershipGuarantee");
		}

		if (flags.get(FINDNODE) && flags.get(IDEAL) && flags.get(MEMBERSHIP)) {
			expressions.add("Reachability");
		}

		if (flags.get(FINDNODE) && flags.get(STORE) && flags.get(LOOKUP) && flags.get(STABLE)) {
			expressions.add("TerminationCompleteness");

		}

		// expressions.clear();
		// expressions.add("Reachability");

		System.out.println("Expressions to test: " + expressions);
		System.out.println("Loading trace...");
		System.out.flush();
		long startTime = System.nanoTime();

		A4Reporter rep = new A4Reporter();
		XMLNode xmlNode = new XMLNode(new File(filename));

		Module ansWorld = CompUtil.parseEverything_fromFile(rep, null, sourcepath);

		A4Solution ans = A4SolutionReader.read(ansWorld.getAllReachableSigs(), xmlNode);

		long endTime = System.nanoTime();

		double loadTime = (endTime - startTime) / 1_000_000_000.0;
		System.out.println("\nLoaded trace, " + loadTime + "s\n");

		try (PrintWriter csvWriter = new PrintWriter(new FileWriter(csvOutputFile))) {
			// Write CSV header
			// csvWriter.println("Expression,Result,Precondition Time (s),Evaluation Time
			// (s)");
			csvWriter.println(
					"log_name,load_time,property,line_count,original_trace_length,processed_trace_length,parse_time,eval_time,total_time,result,precondition,nodes,max_nodes,timestamp");

			for (String expression : expressions) {
				System.out.flush();
				System.out.print(expression + ": ");

				Object result;
				double evalTime = 0;

				startTime = System.nanoTime();
				Expr expr = CompUtil.parseOneExpression_fromString(ansWorld, expression);
				result = ans.eval(expr);
				endTime = System.nanoTime();
				evalTime = (endTime - startTime) / 1_000_000_000.0;

				Object precondition = Boolean.TRUE;
				double precondition_seconds;
				if (result.equals(Boolean.TRUE)) {
					try {
						startTime = System.nanoTime();
						precondition = ans.eval(CompUtil.parseOneExpression_fromString(ansWorld,
								expression + "Precondition"));

						endTime = System.nanoTime();
						precondition_seconds = (endTime - startTime) / 1_000_000_000.0;
					} catch (Exception e) {
						precondition = Boolean.TRUE;
						precondition_seconds = 0;
					}

					if (precondition.equals(Boolean.FALSE)) {
						System.out.println("No scenario " + evalTime + "s precondition: "
								+ precondition_seconds + "s");
					} else {
						System.out.println(result.toString() + " " + evalTime
								+ "s precondition: " + precondition_seconds + "s");
					}
				} else {
					System.out.println(result.toString() + " " + evalTime + "s");

				}

				// double totalTime = loadTime + evalTime + precondition_seconds;
				double totalTime = loadTime + evalTime;

				String timestamp = Instant.now().toString();

				// "log_name,property,original_trace_length,processed_trace_length,parse_time,eval_time,total_time,result,precondition,nodes,timestamp"
				csvWriter.printf("%s,%.6f,%s,%d,%d,%d,%.6f,%.6f,%.6f,%s,%s,%d,%d,%s%n",
						baseFilename,
						loadTime,
						expression,
						lineCount,
						originalTraceLength,
						processedTraceLength,
						loadTime,
						evalTime,
						totalTime,
						result,
						precondition,
						nodes,
						maxNodes,
						timestamp);
			}
		}
	}
}
