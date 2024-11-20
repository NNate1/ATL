module = "Evaluator"
import timeit

from pathlib import Path

import jpype
import jpype.imports


def evaluate(file_name: Path, class_path: Path, source_path: Path):
    try:
        jpype.startJVM(classpath=[class_path])
    except OSError as e:
        print(e)

    from edu.mit.csail.sdg.alloy4 import A4Reporter, XMLNode
    from edu.mit.csail.sdg.parser import CompUtil
    from edu.mit.csail.sdg.translator import (
        A4SolutionReader,
    )
    from java.io import File

    rep = A4Reporter()
    print(str(file_name))
    xmlNode = XMLNode(File(str(file_name)))

    ansWorld = CompUtil.parseEverything_fromFile(rep, None, str(source_path))
    ans = A4SolutionReader.read(ansWorld.getAllReachableSigs(), xmlNode)

    expressions = [
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
    ]

    for expression in expressions:
        start_time = timeit.default_timer()
        result = ans.eval(CompUtil.parseOneExpression_fromString(ansWorld, expression))
        elapsed = timeit.default_timer() - start_time
        print(f"{expression}: {result}, {elapsed}")
    # e = CompUtil.parseOneExpression_fromString(ansWorld, "Node")
    # print(ans.eval(e))

    # Expr e = CompUtil.parseOneExpression_fromString(ansWorld, "univ");
    # ans.eval(e);
    # e = CompUtil.parseOneExpression_fromString(ansWorld, "Point");
    # System.out.println(ans.eval(e));
    # rep = A4Reporter()
