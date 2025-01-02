// package edu.mit.csail.sdg.alloy4whole;
// package evaluator;

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
		// String sourcepath = args[1];
		String sourcepath = "/mnt/c/Users/nunop/Documents/MEIC/Tese/ATL/DHTsATL.als";

		A4Reporter rep = new A4Reporter();
		XMLNode xmlNode = new XMLNode(new File(filename));

		Module ansWorld = CompUtil.parseEverything_fromFile(rep, null, sourcepath);
        	    
		A4Solution ans = A4SolutionReader.read(ansWorld.getAllReachableSigs(), xmlNode);

	
		String[] expressions = { 
		"KeyConsistency",
		"LookupConsistency",
		"ValueConsistency",
		"ValueFreshness",
		"WeakValueFreshness",
		"Reachability",
		"MembershipGuarantee",
		"ReplyMembershipGuarantee",
		"FindNodeLookupConsistency",
		"ResponsabilityTransfer",
		"ResponsibilityExpiration",
		"TerminationCompleteness",
		};

		for (String expression : expressions) {
			System.out.println("Starting evaluation of " + expression);
			long startTime = System.nanoTime();
			Expr e = CompUtil.parseOneExpression_fromString(ansWorld, expression);
			long endTime = System.nanoTime();
			double elapsed_seconds = (endTime - startTime) / 1_000_000_000.0;
			System.out.println(expression + ": " + ans.eval(e) + ", " + elapsed_seconds + "s");
			// System.out.println(expression + ": " + ans.eval(e) + ", " + (endTime - startTime) / 1_000_000_000+ "s");
		}
	}
}

// public static evaluate(String file_name, String class_path, String source_path) {
//
//     rep = A4Reporter()
//     xmlNode = XMLNode(File(str(file_name)))
//
//     ansWorld = CompUtil.parseEverything_fromFile(rep, None, str(source_path))
//     ans = A4SolutionReader.read(ansWorld.getAllReachableSigs(), xmlNode)
//
//     expressions = [
//         "KeyConsistency",
//         "LookupConsistency",
//         "ValueConsistency",
//         "ValueFreshness",
//         "WeakValueFreshness",
//         "Reachability",
//         "MembershipGuarantee",
//         "ReplyMembershipGuarantee",
//         "FindNodeLookupConsistency",
//         "ResponsabilityTransfer",
//         "ResponsibilityExpiration",
//         "TerminationCompleteness",
//     ]
//
//     for expression in expressions:
//         start_time = timeit.default_timer()
//         result = ans.eval(CompUtil.parseOneExpression_fromString(ansWorld, expression))
//         elapsed = timeit.default_timer() - start_time
//         print(f"{expression}: {result}, {elapsed}")
//     # e = CompUtil.parseOneExpression_fromString(ansWorld, "Node")
//     # print(ans.eval(e))
//
//     # Expr e = CompUtil.parseOneExpression_fromString(ansWorld, "univ");
//     # ans.eval(e);
//     # e = CompUtil.parseOneExpression_fromString(ansWorld, "Point");
//     # System.out.println(ans.eval(e));
//     # rep = A4Reporter()
