import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.XMLNode;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4SolutionReader;

import java.io.File;

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

		System.out.println("Loading trace...\n");
		System.out.flush();

		long startTime = System.nanoTime();

		A4Reporter rep = new A4Reporter();
		XMLNode xmlNode = new XMLNode(new File(filename));

		Module ansWorld = CompUtil.parseEverything_fromFile(rep, null, sourcepath);

		A4Solution ans = A4SolutionReader.read(ansWorld.getAllReachableSigs(), xmlNode);

		long endTime = System.nanoTime();

		double elapsed_seconds = (endTime - startTime) / 1_000_000_000.0;
		System.out.println("\nLoaded trace, " + elapsed_seconds + "s\n");

		String[] expressions = {
				"KeyConsistency",
				"LookupConsistency",
				"ValueConsistency",
				"ValueFreshness",
				"WeakValueFreshness",
				"Reachability",
				// "MembershipGuarantee",
				"MembershipGuarantee_Responsible",
				"MembershipGuarantee_Replier",
				"FindNodeLookupConsistency",
				"ResponsibilityTransfer",
				"ResponsibilityExpiration",
				"TerminationCompleteness",
		};

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
