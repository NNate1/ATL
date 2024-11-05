import sys
import json
import xml.etree.ElementTree as ET
from copy import deepcopy

FILENAME = "C:\\Users\\nunop\\Documents\\MEIC\\Tese\\ATL\\DHTsATL.als"
max_trace = 10
command = "Run for 10"

trace_length = 2
backloop = 1


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


def add_instance(root: ET.Element, trace_length: int, backloop: int):
    instance = ET.SubElement(root, "instance")
    instance.set("bitwidth", "4")
    instance.set("maxseq", "4")
    instance.set("mintrace", "1")
    instance.set("maxtrace", "10")
    # instance.set("command", command)
    instance.set("tracelength", str(trace_length))
    instance.set("backloop", str(backloop))

    # Not required
    # add_builtin(instance, "seq/Int", "0", "1")
    # add_builtin(instance, "Int", "1", "2")
    # add_builtin(instance, "String", "3", "2")

    add_element(instance, "sig", "ATL/P", "7", "8")

    prop = add_element(instance, "sig", "ATL/Proposition", "8", "2")
    prop.set("abstract", "yes")


def add_types(field, id1: str, id2: str = ""):
    if id2:
        types = ET.SubElement(field, "types")
        ET.SubElement(types, "type", {"ID": id1})
        ET.SubElement(types, "type", {"ID": id2})
    else:
        ET.SubElement(field, "type", {"ID": id1})


def create_instance(
    nodes: set, keys: set, values: set, times: dict[str, int], operations: list[dict]
):
    instance = ET.Element("instance")
    instance.set("bitwidth", "4")
    instance.set("maxseq", "4")
    instance.set("mintrace", "1")

    trace_length = len(times)
    instance.set("maxtrace", str(trace_length))
    # instance.set("command", command)
    instance.set("tracelength", str(trace_length))
    instance.set("backloop", str(trace_length - 1))

    # Not required
    # add_builtin(instance, "seq/Int", "0", "1")
    # add_builtin(instance, "Int", "1", "2")
    # add_builtin(instance, "String", "3", "2")

    # Universal
    univ = add_element(instance, "sig", "univ", "2")
    univ.set("builtin", "yes")
    univ.set("var", "yes")

    # Proposition
    add_element(instance, "sig", "ATL/P", "7", "8")
    prop = add_element(instance, "sig", "ATL/Proposition", "8", "2")
    prop.set("abstract", "yes")

    # Active
    active_sig = add_element(instance, "sig", "ATL/Active", "37")
    active_sig.set("var", "yes")
    add_types(active_sig, "8")

    # Boundary
    boundary_sig = add_element(instance, "sig", "ATL/Boundary", "9", "2")
    for boundary in times.values():
        add_element(boundary_sig, "atom", f"ATL/Boundary${boundary}")

    # Happens
    happens_sig = add_element(instance, "sig", "ATL/Happens", "38")
    happens_sig.set("var", "yes")
    add_types(happens_sig, "9")

    # Interval
    add_element(instance, "sig", "ATL/T", "34", "11")
    interval_sig = add_element(instance, "sig", "ATL/Interval", "11", "2")
    interval_sig.set("abstract", "yes")

    interval_start = add_element(instance, "field", "start", "35", "11")
    add_types(interval_start, "11", "9")

    interval_end = add_element(instance, "field", "end", "36", "11")
    add_types(interval_end, "11", "9")

    # Ongoing
    ongoing_sig = add_element(instance, "sig", "ATL/Ongoing", "39")
    ongoing_sig.set("var", "yes")
    # ET.SubElement(ongoing_sig, "type", {"ID": "11"})
    add_types(ongoing_sig, "11")

    # Starting
    starting_sig = add_element(instance, "sig", "ATL/Starting", "40")
    starting_sig.set("var", "yes")
    # ET.SubElement(ongoing_sig, "type", {"ID": "39"})
    add_types(starting_sig, "39")

    # Ending
    ending_sig = add_element(instance, "sig", "ATL/Ending", "41")
    ending_sig.set("var", "yes")
    # ET.SubElement(ongoing_sig, "type", {"ID": "39"})
    add_types(ending_sig, "39")

    # Node
    node_sig = add_element(instance, "sig", "this/Node", "4", "5")
    for node in nodes:
        add_element(node_sig, "atom", f"Node${node}")

    # Member
    member_sig = add_element(instance, "sig", "this/Member", "10", "11")
    member_node = add_element(instance, "sig", "node", "12", "10")
    add_types(member_node, "10", "4")

    # Key
    key_sig = add_element(instance, "sig", "this/Key", "5", "2")
    for key in keys:
        add_element(key_sig, "atom", f"Key${key}")

    # Responsible
    responsible_sig = add_element(instance, "sig", "this/Responsible", "13", "11")
    responsible_node = add_element(instance, "sig", "node", "14", "13")
    add_types(responsible_node, "13", "4")

    # Value
    value_sig = add_element(instance, "sig", "this/Value", "6", "2")
    for value in values:
        add_element(value_sig, "atom", f"Value${value}")

    # Operation
    operation_sig = add_element(instance, "sig", "this/Operation", "17", "11")
    operation_sig.set("abstract", "yes")

    operation_node = add_element(instance, "field", "node", "23", "17")
    add_types(operation_node, "17", "4")

    operation_replier = add_element(instance, "field", "node", "24", "17")
    add_types(operation_replier, "17", "4")

    operation_key = add_element(instance, "field", "node", "25", "17")
    add_types(operation_key, "17", "5")

    # Store
    store_sig = add_element(instance, "sig", "this/Store", "16", "17")

    store_values = add_element(instance, "field", "value", "18", "16")
    add_types(store_values, "16", "6")

    # Lookup
    lookup_sig = add_element(instance, "sig", "this/Lookup", "19", "17")

    lookup_values = add_element(instance, "field", "value", "20", "19")
    add_types(lookup_values, "19", "6")

    # Find Node
    find_node_sig = add_element(instance, "sig", "this/FindNode", "21", "17")

    find_node_responsible = add_element(instance, "field", "responsible", "22", "21")
    add_types(find_node_responsible, "21", "4")

    # Membership Operation
    membership_op_sig = add_element(
        instance, "sig", "this/MembershipOperation", "27", "11"
    )
    membership_op_sig.set("abstract", "yes")

    membership_op_node = add_element(instance, "field", "node", "30", "27")
    add_types(membership_op_node, "27", "4")

    # Join
    join_sig = add_element(instance, "sig", "this/Join", "26", "27")

    # Leave
    leave_sig = add_element(instance, "sig", "this/Leave", "28", "27")

    # Fail
    fail_sig = add_element(instance, "sig", "this/Fail", "29", "27")

    # Ideal
    ideal_sig = add_element(instance, "sig", "this/IdealState", "31", "11")

    # ReadOnly
    read_only_sig = add_element(instance, "sig", "this/ReadOnlyRegimen", "32", "11")

    # Stable
    stable_sig = add_element(instance, "sig", "this/StableRegimen", "33", "11")

    # TODO:
    # Functional Operations
    # Insert membership operations

    return instance


# TODO:
# Update ongoing operations
# Update states and regimens
# Update Members
# Update responsible


def add_members(instance: ET.Element):
    # member and node relations
    pass


def add_responsible(instance: ET.Element):
    # responsible and node -> key relations
    pass


def add_functional_ops(instance: ET.Element):
    pass


def read(log: dict):
    members = set(log.get("members") or [])
    nodes = set(members)

    keys = set()
    values = set()

    times = dict()
    operations = []

    print(f"{nodes = }\n{times = }\n{operations = }")

    for op in log.get("operations") or []:
        nodes.add(op.get("node"))
        times[op.get("time")] = len(times)

        operations.append(op)

        keys.add(op.get("key"))
        if value := op.get("value"):
            values.add(value)

        if reply := op.get("reply"):
            times[reply.get("time")] = len(times)

            if value := reply.get("value"):
                values.add(value)

    print(f"{nodes = }\n{times = }\n{operations = }")

    # only model members that participate in the operations
    # members = members.intersection_update(nodes)

    instance = create_instance(nodes, keys, values, times, operations)

    return instance


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("usage: python Visualizer.py <log_path>")
        exit()

    print(sys.argv)
    with open(sys.argv[1]) as f:
        log = json.load(f)
        print(json.dumps(log, sort_keys=True, indent=4))

    instance = read(log)
    instance_c = deepcopy(instance)

    root = create_root()
    root.append(instance)

    tree = ET.ElementTree(element=root)
    ET.indent(tree, space="\t", level=0)
    # add_instance(root, trace_length, backloop)
    # ET.indent
    ET.dump(root)
    tree.write("output.xml")
