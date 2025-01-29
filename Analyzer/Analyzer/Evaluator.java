import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.XMLNode;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4SolutionReader;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

public class Evaluator {
	public static void main(String[] args) throws Exception {
		String filename = args[0];

		String sourcepath = System.getenv("ATL_MODEL");

		if (sourcepath == null) {

			System.out.println("ATL_MODEL environment variable not set.");
			System.out.println(
					"Set the ATL_MODEL environment variable to the path of the Alloy ATL model file.");
			return;

		}

		String flag_comment;
		try (BufferedReader reader = new BufferedReader(new FileReader(filename))) {
			flag_comment = reader.readLine();
		} catch (Exception e) {
			System.out.println(e.getMessage());
			return;
		}

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

		flags.put(ALL, flag_comment.contains(ALL));
		flags.put(STORE, flag_comment.contains(STORE));
		flags.put(LOOKUP, flag_comment.contains(LOOKUP));
		flags.put(FINDNODE, flag_comment.contains(FINDNODE));
		flags.put(MEMBERSHIP, flag_comment.contains(MEMBERSHIP));
		flags.put(READ_ONLY, flag_comment.contains(READ_ONLY));
		flags.put(STABLE, flag_comment.contains(STABLE));
		flags.put(IDEAL, flag_comment.contains(IDEAL));
		flags.put(RESPONSIBILITY, flag_comment.contains(RESPONSIBILITY));

		// System.out.println(flag_comment);
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
			expressions.add("ResponsibilityTransfer");
		}

		if (flags.get(FINDNODE) && flags.get(MEMBERSHIP) && flags.get(RESPONSIBILITY)) {

			expressions.add("MembershipGuarantee_Responsible");
		}

		if (flags.get(FINDNODE) && flags.get(STORE) && flags.get(LOOKUP) && flags.get(MEMBERSHIP)
				&& flags.get(RESPONSIBILITY)) {

			expressions.add("MembershipGuarantee_Replier");
		}

		if (flags.get(FINDNODE) && flags.get(IDEAL) && flags.get(MEMBERSHIP)) {
			expressions.add("Reachability");
		}

		if (flags.get(FINDNODE) && flags.get(STORE) && flags.get(LOOKUP) && flags.get(STABLE)) {
			expressions.add("TerminationCompleteness");

		}

		// System.out.println("Expressions to test: " + expressions);
		System.out.println("Loading trace...");
		System.out.flush();
		long startTime = System.nanoTime();

		A4Reporter rep = new A4Reporter();
		XMLNode xmlNode = new XMLNode(new File(filename));

		Module ansWorld = CompUtil.parseEverything_fromFile(rep, null, sourcepath);

		A4Solution ans = A4SolutionReader.read(ansWorld.getAllReachableSigs(), xmlNode);

		long endTime = System.nanoTime();

		double elapsed_seconds = (endTime - startTime) / 1_000_000_000.0;
		System.out.println("\nLoaded trace, " + elapsed_seconds + "s\n");

		for (String expression : expressions) {
			System.out.flush();
			System.out.print(expression + ": ");

			startTime = System.nanoTime();
			Expr e = CompUtil.parseOneExpression_fromString(ansWorld, expression);
			var result = ans.eval(e);
			endTime = System.nanoTime();
			elapsed_seconds = (endTime - startTime) / 1_000_000_000.0;
			System.out.println(result.toString() + " " + elapsed_seconds + "s");
		}
	}
}
