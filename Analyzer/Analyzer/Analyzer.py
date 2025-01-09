import argparse
import logging
import xml.etree.ElementTree as ET
from copy import deepcopy
from io import TextIOWrapper
from pathlib import Path
from itertools import pairwise
from typing import OrderedDict,  cast


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
    ReadOnly,
    ReadOnlyEnd,
    Stable,
    StableEnd,
    MemberStart,
    MemberEnd,
    Reply,
    Store,
    Interval
)


# TODO:
# Update responsible
# Update ideal
# Starting Ending 
# Read Initial members from log


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
    stable_regimens: "dict[str, Operation]",
    readonly_regimens: "dict[str, Operation]",
    members: "dict[str, MemberStart]",
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
    functional_operation_sig = add_element(instance, "sig", "this/FunctionalOperation", "17", "11")
    functional_operation_sig.set("abstract", "yes")

    functional_operation_node = add_element(instance, "field", "node", "23", "17")

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

    # # Starting
    # starting_sig = add_element(instance, "sig", "ATL/Starting", "40")
    # starting_sig.set("var", "yes")

    # Ending
    # ending_sig = add_element(instance, "sig", "ATL/Ending", "41")
    # ending_sig.set("var", "yes")


    ## Intervals

    # ReadOnly Intervals:
    for read_only in readonly_regimens.values():
        add_element(read_only_sig, "atom", read_only.get_name())
        add_tuple(interval_start, read_only.get_name(), read_only.get_time())
        if end_time := read_only.get_end_time():
            add_tuple(interval_end, read_only.get_name(), end_time)

    # Stable Intervals:
    for stable in stable_regimens.values():
        add_element(stable_sig, "atom", stable.get_name())
        add_tuple(interval_start, stable.get_name(), stable.get_time())
        if end_time := stable.get_end_time():
            add_tuple(interval_end, stable.get_name(), end_time)

    # Member Intervals:
    for member in members.values():
        add_element(member_sig, "atom", member.get_name())
        add_tuple(member_node, member.get_name(), member.get_node())

        add_tuple(interval_start, member.get_name(), member.get_time())
        if end_time := member.get_end_time():
            add_tuple(interval_end, member.get_name(), end_time)

    for op in operations.values():
        if isinstance(op, FunctionalOperation):
            add_tuple(functional_operation_node, op.get_name(), op.get_node())
            add_tuple(operation_key, op.get_name(), op.get_key())
            add_tuple(operation_replier, op.get_name(), op.get_replier())

            add_tuple(interval_start, op.get_name(), op.get_time())
            if end_time := op.get_end_time():
                add_tuple(interval_end, op.get_name(), end_time)

            match op.get_type():
                case "Store" | "Remove":
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

            add_tuple(interval_start, op.get_name(), op.get_time())
            if end_time := op.get_end_time():
                add_tuple(interval_end, op.get_name(), end_time)

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

    add_types(functional_operation_node, "17", "4")
    add_types(operation_replier, "17", "4")
    add_types(operation_key, "17", "5")

    add_types(membership_op_node, "27", "4")

    add_types(interval_start, "11", "9")
    add_types(interval_end, "11", "9")

    add_types(active_sig, "8")
    add_types(happens_sig, "9")
    add_types(ongoing_sig, "11")

    # add_types(starting_sig, "39")
    # add_types(ending_sig, "39")

    return instance


def id_value(value: str):
    return "Value$" + str(value)


def id_key(key: str):
    return "Key$" + str(key)


def id_node(node: str):
    return "Node$" + str(node)


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


def read_log(log: TextIOWrapper, max_lines=200) -> tuple[set[str], set[str], set[str], set[str], OrderedDict[str, Operation]]:
    nodes = set()
    keys = set()
    values = set()
    values = {NO_VALUE}

    times = set()

    operations = OrderedDict()
    op_counts = dict()

    line_count = 0

    ongoing = set()

    for line in log:
        if line_count == max_lines:
            break
        line_count += 1

        components = list(map(lambda x: x.strip(","), line.strip().split(", ")))


        logging.debug(f"line {line_count} {components}")

        time, optype = components[0:2]
        times.add(time)

        if optype in {"Lookup", "Store", "FindNode", "Remove", "Join", "Leave", "Fail"}:
            id = components[2]
            node = components[3]
            args = components[4:] if len(components) > 4 else []

            op = None

            op_counts[optype] = op_counts.get(optype, 0) + 1

            match optype:
                case "Store":
                    op = Store(
                        time, optype, id, op_counts[optype], node, args[0], args[1]
                    )
                    keys.add(args[0])
                    values.add(args[1])

                case "Remove":
                    op = Store(
                        time, optype, id, op_counts[optype], node, args[0], NO_VALUE
                    )
                    keys.add(args[0])
                    # values.add(NO_VALUE)
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
                ongoing.add(op)

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
                reply.tag = op.tag
                op.set_end_time(time)

                operations["Reply-" + id] = reply

                if isinstance(op, FunctionalOperation):
                    op.set_replier(replier)

                if len(args) > 0:
                    if isinstance(op, Lookup):
                        op.set_value(args[0])
                    elif isinstance(op, FindNode):
                        op.set_responsible(args[0])

                elif isinstance(op, FindNode):
                    logging.warning(
                        f"Reply for operation {id} missing result.\n Reply: {line}"
                    )

                op_counts[optype] = op_counts.get(optype, 0) + 1

            else:

                logging.warning(f"""Reply for operation {id} received before operation started.\nline: {line_count} {line}""")
                
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

            if replier is not None:
                assert reply_optype in (
                    "Store",
                    "Lookup",
                    "FindNode",
                    "Remove",
                ), f"line {line_count} {line}\n{components = }"
                nodes.add(replier)
        elif optype in {"StartStableRegimen", "EndStableRegimen"}:
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



def complete_trace(
    root: ET.Element, 
    instance_template: ET.Element,
    operations: dict[str, Operation],
    stable: dict[str, Interval],
    readonly: dict[str, Interval],
    members: dict[str, Interval],
):
    ongoing = set()
    prev = None
    instance = None

    ongoing_sig = None
    # starting_sig = None
    # ending_sig = None
    happens_sig = None

    logging.info("Completing trace")

    # add stable and readonly to operations
    events = operations | stable | readonly | members

    for (counter, (id, event)) in enumerate(sorted(events.items(), key=lambda x: x[1].get_time())):
        counter += 1
        if counter % 100 == 0:
            logging.info(f"Generating event {counter}/{len(events)}")

        logging.debug(f"event {event.get_name()} at {event.get_time()}")
        logging.debug(f"Ongoing: {ongoing}")

        if event.get_time() != prev:
            if instance is not None:
                root.append(instance)

            logging.debug(f"New instance at {event.get_time()}")
            instance = deepcopy(instance_template)

            ongoing_sig = instance.find("sig[@label='ATL/Ongoing']")
            # starting_sig = instance.find("sig[@label='ATL/Starting']")
            # ending_sig = instance.find("sig[@label='ATL/Ending']")

            happens_sig = instance.find("sig[@label='ATL/Happens']")

            assert ongoing_sig is not None, "Ongoing sig not found"
            assert happens_sig is not None, "Happens sig not found"


            add_element(happens_sig, "atom", event.get_time())

            for e in ongoing:
                add_element(ongoing_sig, "atom", e.get_name())
            prev = event.get_time()

        else:
            assert instance is not None, "Instance not created"

        assert ongoing_sig is not None, "Ongoing sig not found"
        # assert starting_sig is not None, "Starting sig not found"
        # assert ending_sig is not None, "Ending sig not found"

        assert happens_sig is not None, "Happens sig not found"

        if event.is_end():
            # add_element(ending_sig, "atom", events[event.get_id()].get_name())
            assert (
                events[event.get_id()] in ongoing
            ), f"event {event.get_name()} not in ongoing"
            
            ongoing.remove(events[event.get_id()])
        else:
            # add_element(starting_sig, "atom", event.get_name())
            add_element(ongoing_sig, "atom", event.get_name())
            assert event not in ongoing, f"event {event.get_name()} already in ongoing"
            ongoing.add(event)



    if instance is not None:
        root.append(instance)

    logging.info("Creating backloop instance")

    instance = deepcopy(instance_template)

    ongoing_sig = instance.find("sig[@label='ATL/Ongoing']")

    assert ongoing_sig is not None, "Ongoing sig not found"

    for e in ongoing:
        add_element(ongoing_sig, "atom", e.get_name())
    root.append(instance)


def detect_regimens(operations: OrderedDict[str, Operation]) -> tuple[dict, dict]:
    stable_regimens = {}
    membership_ops = set()
    ongoing_stable = None

    readonly_regimens = {}
    write_ops = set()
    ongoing_readonly = None

    prev = "" 

    for op in operations.values():
        time = op.get_time()


        logging.debug(f"Processing operation {op.get_name()} at {time}")

        # Stable
        if op.get_type() in ("Join" , "Leave", "Fail"):
            membership_ops.add(op.get_id())
            if ongoing_stable is not None:
                ongoing_stable.set_end_time(prev)

                end_stable = StableEnd(prev, ongoing_stable.id)
                stable_regimens["End-" + end_stable.get_id()] = end_stable

                ongoing_stable = None

        if len(membership_ops) == 0 and ongoing_stable is None:
            ongoing_stable = Stable(time, str(len(stable_regimens)))
            stable_regimens[ongoing_stable.get_id()] = ongoing_stable

        if op.get_type() in ("ReplyJoin" , "ReplyLeave", "Fail"):
            membership_ops.remove(op.get_id())

        # Readonly
        if op.get_type() in ("Store", "Remove"):
            write_ops.add(op.get_id())
            if ongoing_readonly is not None:
                ongoing_readonly.set_end_time(prev)

                end_readonly = ReadOnlyEnd(prev, ongoing_readonly.id)
                readonly_regimens["End-" + end_readonly.get_id()] = end_readonly

                ongoing_readonly = None


        if len(write_ops) == 0 and ongoing_readonly is None:
            ongoing_readonly = ReadOnly(time, str(len(readonly_regimens)))
            readonly_regimens[ongoing_readonly.get_id()] = ongoing_readonly

        if op.get_type() in ("ReplyStore" , "ReplyRemove"):
                    write_ops.remove(op.get_id())



        prev = time

    return stable_regimens, readonly_regimens



def first(s):
    '''Return the first element from an ordered collection
       or an arbitrary element from an unordered collection.
       Raise StopIteration if the collection is empty.
    '''
    return next(iter(s))

def detect_members(operations: OrderedDict[str, Operation]) -> dict:

    logging.debug(f"Detecting member intervals.")


    membership_intervals = {}

    current_members = {}

    next_op = first(operations.values())
    next_time = next_op.get_time()


    #TODO: Read Initial members from log
    initial_members = set()
    initial_members.add(next_op.node) 

    for node in initial_members:  
            member = MemberStart(node, next_time, "M" + str(len(membership_intervals)))

            assert node not in current_members, f"Node {node} is already a member, current members:\n{current_members}"

            current_members[node] = member

            membership_intervals[member.get_id()] = member

    for op, next_op in pairwise(operations.values()):
        
        next_time = next_op.get_time()

        logging.debug(f"Processing operation {op.get_name()} at {next_time}")

        infer_member_interval (op, next_time, operations, membership_intervals , current_members )

    if next_op:
        assert next_time is not None
        infer_member_interval (next_op, "1" + next_time, operations, membership_intervals , current_members )

    return membership_intervals

def infer_member_interval (op: Operation, next_time: str, operations : dict[str, Operation], membership_intervals : dict[str, Interval], current_members : dict[str, Interval]):
        if op.get_type() == "ReplyJoin":
            node = operations[op.get_id()].get_node()
            member = MemberStart(node, next_time, "M" + str(len(membership_intervals)))

            assert node not in current_members, f"Node {node} is already a member, current members:\n{current_members}"

            current_members[node] = member

            membership_intervals[member.get_id()] = member

        elif op.get_type() in  ("ReplyLeave", "Fail"):
            node = operations[op.get_id()].get_node()
            assert node in current_members, f"Node {node} is not a member, current members:\n{current_members}"

            start_member = current_members[node]
            start_member.set_end_time(next_time)

            end_member = MemberEnd(node, next_time, start_member.get_id())


            membership_intervals["End-" + end_member.get_id()] = end_member

            del current_members[node]



def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "logfile", type=Path, help="Path to the log file to process."
    )
    parser.add_argument(
        "output", type=Path, help="Path to save the generated XML file."
    )
    parser.add_argument(
        "--max-lines", type=int, default=float("inf"), help="Maximum number of lines to process."
    )
    parser.add_argument(
        "-v", "--verbose", action="store_true", help="Enable verbose logging."
    )

    args = parser.parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s - %(levelname)s - %(message)s"
        # filename="debug.log",
        # filemode="a",
    )


    with args.logfile.open("r", encoding="utf-8") as log:
        nodes, keys, values, times, operations = read_log(log, max_lines=args.max_lines)


    (stable, readonly) = detect_regimens(operations)

    logging.debug(f"Stable regimens: {stable}")
    logging.debug(f"Readonly regimens: {readonly}")

    members =  detect_members(operations)

    logging.debug(f"Membership intervals: {members}")

    # exit()

    for regimen in stable.values():
        times.add(regimen.get_time())
        if regimen.get_end_time():
            times.add(regimen.get_end_time())


    for regimen in readonly.values():
        times.add(regimen.get_time())
        if regimen.get_end_time():
            times.add(regimen.get_end_time())

    for member in members.values():
        times.add(member.get_time())
        if member.get_end_time():
            times.add(member.get_end_time())

    root = create_root()
    instance_template = create_instance(nodes, keys, values, times, operations, stable, readonly, members)

    # instance_template = create_instance(nodes, keys, values, times, operations, stable, readonly)




    complete_trace(root, instance_template, operations, stable, readonly, members)


    logging.info(f"Writing XML trace to {args.output}")
    tree = ET.ElementTree(root)
    tree.write(args.output, encoding="utf-8", xml_declaration=True)
    logging.info(f"XML trace successfully written to {args.output}")

    # class_path = Path(
    #     "/mnt/c/Users/nunop/Documents/MEIC/Tese/_org.alloytools.alloy.dist.jar"
    # )
    # source_path = Path("/mnt/c/Users/nunop/Documents/MEIC/Tese/ATL/DHTsATL.als")
    # evaluate(log_folder / p.name, class_path, source_path)


if __name__ == "__main__":
    main()
