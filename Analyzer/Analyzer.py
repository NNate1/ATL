import logging
import sys
import xml.etree.ElementTree as ET
from copy import deepcopy
from io import TextIOWrapper
from pathlib import Path
from typing import OrderedDict, cast

from Operations import (
    NO_NODE,
    NO_VALUE,
    Fail,
    FindNode,
    FunctionalOperation,
    Join,
    Leave,
    Lookup,
    Operation,
    Reply,
    Store,
)

FILENAME = "C:\\Users\\nunop\\Documents\\MEIC\\Tese\\ATL\\DHTsATL.als"
UNUSED_TAG = -1
# NO_REPLIER = "NoReplier"
# NO_VALUE = "NoValue"
# NO_REPONSIBLE = "NoResponsible"


def create_root() -> ET.Element:
    root = ET.Element("alloy", builddate="2021-11-03T15:25:43.736Z")
    return root


def add_builtin(instance: ET.Element, label: str, ID: str, parentID: str):
    seq_int = ET.SubElement(instance, "sig")
    seq_int.set("label", label)
    seq_int.set("ID", ID)
    seq_int.set("parentID", parentID)
    seq_int.set("builtin", "yes")


def add_element(
    instance: ET.Element, name: str, label: str, ID: str = "", parentID: str = ""
) -> ET.Element:
    sig = ET.SubElement(instance, name)
    sig.set("label", label)
    if ID:
        sig.set("ID", ID)
    if parentID:
        sig.set("parentID", parentID)

    return sig


def add_tuple(field: ET.Element, label1: str, label2: str) -> ET.Element:
    tpl = ET.SubElement(field, "tuple")
    add_element(tpl, "atom", label1)
    add_element(tpl, "atom", label2)

    return tpl


def add_types(field, id1: str, id2: str = ""):
    if id2:
        types = ET.SubElement(field, "types")
        ET.SubElement(types, "type", {"ID": id1})
        ET.SubElement(types, "type", {"ID": id2})
    else:
        ET.SubElement(field, "type", {"ID": id1})


def create_instance(
    nodes: set[str],
    keys: set[str],
    values: set[str],
    times: set[str],
    operations: "dict[str, Operation]",
):
    instance = ET.Element("instance")

    instance.set("bitwidth", "4")
    instance.set("maxseq", "2")
    instance.set("mintrace", "1")

    # instance.set("maxtrace", "10")
    instance.set("maxtrace", str(len(times) + 1))  # + 1 for backloop instance
    instance.set("command", "Run run$1 for 10")

    instance.set("filename", FILENAME)
    # instance.set("tracelength", "2")
    instance.set("tracelength", str(len(times) + 1))
    # instance.set("backloop", "1")

    instance.set("backloop", str(len(times)))

    # Not required
    # add_builtin(instance, "seq/Int", "0", "1")
    # add_builtin(instance, "Int", "1", "2")
    # add_builtin(instance, "String", "3", "2")

    # Node
    node_sig = add_element(instance, "sig", "this/Node", "4", "5")
    for node in nodes:
        # add_element(node_sig, "atom", id_node(node))
        add_element(node_sig, "atom", node)

    add_element(node_sig, "atom", NO_NODE)

    # Key
    key_sig = add_element(instance, "sig", "this/Key", "5", "2")
    for key in keys:
        add_element(key_sig, "atom", key)

    # Value
    value_sig = add_element(instance, "sig", "this/Value", "6", "2")
    for value in values:
        add_element(value_sig, "atom", value)

    add_element(value_sig, "atom", NO_VALUE)

    # Proposition
    add_element(instance, "sig", "ATL/P", "7", "8")
    prop = add_element(instance, "sig", "ATL/Proposition", "8", "2")
    prop.set("abstract", "yes")

    # Boundary
    boundary_sig = add_element(instance, "sig", "ATL/Boundary", "9", "2")
    # for boundary in times.values():
    for boundary in times:
        add_element(boundary_sig, "atom", boundary)

    # Member
    member_sig = add_element(instance, "sig", "this/Member", "10", "11")
    member_node = add_element(instance, "field", "node", "12", "10")

    # Responsible
    responsible_sig = add_element(instance, "sig", "this/Responsible", "13", "11")
    responsible_node = add_element(instance, "field", "node", "14", "13")
    responsible_key = add_element(instance, "field", "key", "15", "13")

    # Store
    store_sig = add_element(instance, "sig", "this/Store", "16", "17")

    store_values = add_element(instance, "field", "value", "18", "16")

    # Lookup
    lookup_sig = add_element(instance, "sig", "this/Lookup", "19", "17")

    lookup_values = add_element(instance, "field", "value", "20", "19")

    # Find Node
    find_node_sig = add_element(instance, "sig", "this/FindNode", "21", "17")

    find_node_responsible = add_element(instance, "field", "responsible", "22", "21")

    # Operation
    operation_sig = add_element(instance, "sig", "this/Operation", "17", "11")
    operation_sig.set("abstract", "yes")

    operation_node = add_element(instance, "field", "node", "23", "17")

    operation_replier = add_element(instance, "field", "replier", "24", "17")

    operation_key = add_element(instance, "field", "key", "25", "17")

    # Join
    join_sig = add_element(instance, "sig", "this/Join", "26", "27")

    # Leave
    leave_sig = add_element(instance, "sig", "this/Leave", "28", "27")

    # Fail
    fail_sig = add_element(instance, "sig", "this/Fail", "29", "27")
    # Membership Operation
    membership_op_sig = add_element(
        instance, "sig", "this/MembershipOperation", "27", "11"
    )
    membership_op_sig.set("abstract", "yes")

    membership_op_node = add_element(instance, "field", "node", "30", "27")

    # Ideal
    ideal_sig = add_element(instance, "sig", "this/IdealState", "31", "11")

    # ReadOnly
    read_only_sig = add_element(instance, "sig", "this/ReadOnlyRegimen", "32", "11")

    # Stable
    stable_sig = add_element(instance, "sig", "this/StableRegimen", "33", "11")

    # Interval
    add_element(instance, "sig", "ATL/T", "34", "11")
    interval_sig = add_element(instance, "sig", "ATL/Interval", "11", "2")
    interval_sig.set("abstract", "yes")

    interval_start = add_element(instance, "field", "start", "35", "11")

    interval_end = add_element(instance, "field", "end", "36", "11")

    # Universal
    univ = add_element(instance, "sig", "univ", "2")
    univ.set("builtin", "yes")
    univ.set("var", "yes")

    # Active
    active_sig = add_element(instance, "sig", "ATL/Active", "37")
    active_sig.set("var", "yes")

    # Happens
    happens_sig = add_element(instance, "sig", "ATL/Happens", "38")
    happens_sig.set("var", "yes")

    # Ongoing
    ongoing_sig = add_element(instance, "sig", "ATL/Ongoing", "39")
    ongoing_sig.set("var", "yes")
    # ET.SubElement(ongoing_sig, 'type', {"ID": "11"})

    # Starting
    starting_sig = add_element(instance, "sig", "ATL/Starting", "40")
    starting_sig.set("var", "yes")
    # ET.SubElement(ongoing_sig, 'type', {"ID": "39"})

    # Ending
    ending_sig = add_element(instance, "sig", "ATL/Ending", "41")
    ending_sig.set("var", "yes")
    # ET.SubElement(ongoing_sig, 'type', {"ID": "39"})

    for op in operations.values():
        # match type(op)
        if isinstance(op, FunctionalOperation):
            add_tuple(operation_node, op.get_name(), op.get_node())
            add_tuple(operation_key, op.get_name(), op.get_key())
            add_tuple(operation_replier, op.get_name(), op.get_replier())

            add_tuple(interval_start, op.get_name(), op.get_time())
            if end_time := op.get_end_time():
                add_tuple(interval_start, op.get_name(), end_time)

            match op.get_type():
                case "Store":
                    op = cast(Store, op)
                    add_element(store_sig, "atom", op.get_name())
                    add_tuple(store_values, op.get_name(), op.get_value())

                case "Lookup":
                    op = cast(Lookup, op)
                    add_element(lookup_sig, "atom", op.get_name())
                    add_tuple(lookup_values, op.get_name(), op.get_value())

                case "FindNode":
                    op = cast(FindNode, op)
                    add_element(find_node_sig, "atom", op.get_name())
                    add_tuple(
                        find_node_responsible, op.get_name(), op.get_responsible()
                    )

        elif op.get_type() in ("Join", "Leave", "Fail"):
            add_tuple(membership_op_node, op.get_name(), op.get_node())

            match op.get_type():
                case "Join":
                    add_element(join_sig, "atom", op.get_name())

                case "Leave":
                    add_element(leave_sig, "atom", op.get_name())

                case "Fail":
                    add_element(fail_sig, "atom", op.get_name())

    add_types(member_node, "10", "4")

    add_types(responsible_node, "13", "4")
    add_types(responsible_key, "13", "5")

    add_types(store_values, "16", "6")
    add_types(lookup_values, "19", "6")
    add_types(find_node_responsible, "21", "4")

    add_types(operation_node, "17", "4")
    add_types(operation_replier, "17", "4")
    add_types(operation_key, "17", "5")

    add_types(membership_op_node, "27", "4")

    add_types(interval_start, "11", "9")
    add_types(interval_end, "11", "9")

    add_types(active_sig, "8")
    add_types(happens_sig, "9")
    add_types(ongoing_sig, "11")

    add_types(starting_sig, "39")
    add_types(ending_sig, "39")

    return instance


def id_value(value: str):
    return "Value$" + str(value)


def id_key(key: str):
    return "Key$" + str(key)


def id_node(node: str):
    return "Node$" + str(node)


# TODO:
# Update ongoing operations
# Update states and regimens
# Update Members
# Update responsible


# time, type, id, node, args...
#
# 2022-09-27 18:00:00.000, Lookup, <ID>, <node>, <key>
# 2022-09-27 18:00:00.000, ReplyLookup, <ID>, <replier>, <value>
#
#
# 2022-09-27 18:00:00.000, Store, <ID>, <node>, <key>, <value>
# 2022-09-27 18:00:00.000, ReplyStore, <ID>, <replier>
#
#
# 2022-09-27 18:00:00.000, FindNode <ID>, <node>, <key>
# 2022-09-27 18:00:00.000, ReplyFindNode, <ID>, <replier>, <responsible_node>
#
#
# 2022-09-27 18:00:00.000, Join, <ID>, <node>
# 2022-09-27 18:00:00.000, ReplyJoin, <ID>


def read_log(log: TextIOWrapper):
    nodes = set()
    keys = set()
    values = set()

    # time_counter
    # times = OrderedDict()
    times = set()

    operations = OrderedDict()
    op_counts = dict()

    line_count = 0

    for line in log:
        if line_count == 500:
            break
        line_count += 1

        # strip line, and split comma ", ". But if a line has "A,\n". then also remove that comma

        components = line.strip().split(", ")
        for c in components:
            c.strip(",")
            # if c.endswith(","):
            #     components[-1] = c[:-1]

        logging.debug(f"line {line_count} {components}")

        time, optype = components[0:2]
        times.add(time)

        if optype in {"Lookup", "Store", "FindNode", "Join", "Leave", "Fail"}:
            id = components[2]
            node = components[3]
            args = components[4:] if len(components) > 4 else []

            op_counts[optype] = op_counts.get(optype, 0) + 1
            op = None

            match optype:
                case "Store":
                    op = Store(
                        time, optype, id, op_counts[optype], node, args[0], args[1]
                    )
                    keys.add(args[0])
                    values.add(args[1])

                case "Lookup":
                    op = Lookup(time, optype, id, op_counts[optype], node, args[0])
                    keys.add(args[0])

                case "FindNode":
                    op = FindNode(time, optype, id, op_counts[optype], node, args[0])
                    keys.add(args[0])

                case "Join":
                    op = Join(time, optype, id, op_counts[optype], node)

                case "Leave":
                    op = Leave(time, optype, id, op_counts[optype], node)

                case "Fail":
                    op = Fail(time, optype, id, op_counts[optype], node)

                case _:
                    logging.warning(
                        f"Unknown operation type at line {line_count}: {line}"
                    )

            nodes.add(node)
            if op is not None:
                operations[id] = op

        elif optype.startswith("Reply"):
            id = components[2]
            replier = components[3] if len(components) > 3 else None
            args = components[4:] if len(components) > 4 else []
            reply_optype = optype.replace("Reply", "")

            assert (
                reply_optype in ("Join", "Fail", "Leave") or replier is not None
            ), f"Missing replier of functional operation {line}"

            reply = Reply(time, optype, id, UNUSED_TAG, replier)
            if id in operations:
                op = operations[id]
                op.set_end_time(time)

                operations["Reply-" + id] = reply

                if isinstance(op, FunctionalOperation):
                    op.set_replier(replier)

                if len(args) > 0:
                    if isinstance(op, Lookup):
                        op.set_value(args[0])
                # case "FindNode":
                #     op.set_responsible(args[0])
                else:
                    logging.warning(
                        f"Reply for operation {id} missing result.\n Reply: {line}"
                    )

                op_counts[optype] = op_counts.get(optype, 0) + 1

            else:
                logging.warning(
                    f"Reply for operation {id} received before operation started.\n Reply: {line}"
                )

            if reply_optype == "Lookup":
                if len(args) == 0:
                    values.add(NO_VALUE)
                else:
                    values.add(args[0])
            elif reply_optype == "FindNode":
                nodes.add(args[0])

            assert reply_optype in ("Join", "Fail", "Leave") or (
                replier is not None
            ), f"line {line_count} {line}\n{components = }"
            # nodes.add(replier)
            if replier is not None:
                assert reply_optype in (
                    "Store",
                    "Lookup",
                    "FindNode",
                    "Remove",
                ), f"line {line_count} {line}\n{components = }"
                nodes.add(replier)
        elif optype in {"StartStableRegimen", "EndStableRegimen"}:
            # TODO: Implement stable regimens
            pass
        else:
            logging.warning(f"Unknown operation type at line {line_count}: {line}")

    # logging.debug(operations)
    logging.debug(f" times = {sorted(times)}")
    logging.debug(f" {nodes = }")
    logging.debug(f" {values = }")
    logging.debug(f" {keys = }")
    logging.info(f"lines read: {line_count}")
    logging.info(f"operations types: {op_counts}")
    logging.info(f"operations and replies recorded: {len(operations)}")
    logging.info(f"timestamps recorded: {len(times)}")

    return nodes, keys, values, times, operations

    for op in log.get("operations") or []:
        nodes.add(str(op.get("node")))
        times[op.get("time")] = len(times)

        operations.append(op)

        args = op.get("args")
        keys.add(str(args.get("key")))
        if value := args.get("value"):
            values.add(str(value))

        if reply := op.get("reply"):
            nodes.add(str(reply.get("replier")))
            times[reply.get("time")] = len(times)

            if value := reply.get("value"):
                values.add(str(value))

    # only model members that participate in the operations
    # members = members.intersection_update(nodes)

    instance = create_instance(nodes, keys, values, times, operations)

    return instance


def complete_trace(
    root: ET.Element, instance_template: ET.Element, operations: dict[str, Operation]
):
    ongoing = set()
    prev = None
    instance = None

    ongoing_sig = None
    starting_sig = None
    ending_sig = None

    logging.info("Completing trace")
    counter = 0
    for id, op in operations.items():
        counter += 1
        if counter % 100 == 0:
            logging.info(f"Generating operation {counter}/{len(operations)}")

        logging.debug(f"Operation {op.get_name()} at {op.get_time()}")
        logging.debug(f"Ongoing: {ongoing}")
        if op.get_time() != prev:
            if instance is not None:
                root.append(instance)

            logging.debug(f"New instance at {op.get_time()}")
            instance = deepcopy(instance_template)

            ongoing_sig = instance.find("sig[@label='ATL/Ongoing']")
            starting_sig = instance.find("sig[@label='ATL/Starting']")
            ending_sig = instance.find("sig[@label='ATL/Ending']")

            assert ongoing_sig is not None, "Ongoing sig not found"

            for e in ongoing:
                add_element(ongoing_sig, "atom", e.get_name())
            prev = op.get_time()

        else:
            assert instance is not None, "Instance not created"

        assert ongoing_sig is not None, "Ongoing sig not found"
        assert starting_sig is not None, "Starting sig not found"
        assert ending_sig is not None, "Ending sig not found"

        if op.is_end():
            add_element(ending_sig, "atom", operations[op.get_id()].get_name())
            assert (
                operations[op.get_id()] in ongoing
            ), f"Operation {op.get_name()} not in ongoing"
            ongoing.remove(operations[op.get_id()])
        else:
            add_element(starting_sig, "atom", op.get_name())
            add_element(ongoing_sig, "atom", op.get_name())
            assert op not in ongoing, f"Operation {op.get_name()} already in ongoing"
            ongoing.add(op)

    if instance is not None:
        root.append(instance)

    logging.info("Creating backloop instance")

    instance = deepcopy(instance_template)

    ongoing_sig = instance.find("sig[@label='ATL/Ongoing']")
    starting_sig = instance.find("sig[@label='ATL/Starting']")
    ending_sig = instance.find("sig[@label='ATL/Ending']")

    assert ongoing_sig is not None, "Ongoing sig not found"

    for e in ongoing:
        add_element(ongoing_sig, "atom", e.get_name())
    root.append(instance)


def eval(filename: Path):
    XMLNode xmlNode = new XMLNode(new File(outputfilename));
    String alloySourceFilename = xmlNode.iterator().next().getAttribute("filename");
    Module ansWorld = CompUtil.parseEverything_fromFile(rep, null, alloySourceFilename);
    A4Solution ans = A4SolutionReader.read(ansWorld.getAllReachableSigs(), xmlNode);

    Expr e = CompUtil.parseOneExpression_fromString(ansWorld, "univ");
    System.out.println(ans.eval(e));
    e = CompUtil.parseOneExpression_fromString(ansWorld, "Point");
    System.out.println(ans.eval(e));

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("usage: python Visualizer.py <log_path>")
        exit()
    if "-d" in sys.argv:
        sys.argv.remove("-d")
        log_level = logging.DEBUG
    else:
        log_level = logging.INFO

    logging.basicConfig(
        level=log_level,
        format="%(levelname)s: %(message)s",
        # filename="debug.log",
        # filemode="a",
    )
    with open(sys.argv[1]) as f:
        nodes, keys, values, times, operations = read_log(f)

    instance = create_instance(nodes, keys, values, times, operations)

    root = create_root()
    complete_trace(root, instance, operations)

    tree = ET.ElementTree(element=root)
    ET.indent(tree, space="\t", level=0)
    p = Path(sys.argv[1])
    p = p.with_suffix(".xml")

    log_folder = Path("traces")
    log_folder.mkdir(exist_ok=True)

    logging.info(f"Writing to {log_folder / p.name}")
    tree.write(log_folder / p.name)


    eval(log_folder / p.name)
