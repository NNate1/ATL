import bisect 

# from pprint import pprint
from typing import OrderedDict
from pathlib import Path

from Operations import (
    MemberStart,
    MemberEnd,
    IdealStart,
    IdealEnd,
    Operation,
    ResponsibleEnd,
    ResponsibleStart
)


# 2024-11-12 19:56:48.781, Successor, 0C0C45F4, null
# 2024-11-12 19:57:19.607, Successor, 90FCB2D2, 0C0C45F4

class Pointer:
    def __init__(self, node: str, successor: str | None):
        self.node = node
        self.succ = successor

    def __str__(self):
        return f"{self.node} -> {self.succ}"

    def __repr__(self):
        return self.__str__()


# Circular order
def between(a: str, b: str, c: str) -> bool:
    if a == c:
        return True

    if a == b:
        return False

    if a < c:
        return a < b and b <= c

    return a <= b or b <= c


def is_ideal(pointers: dict[str, Pointer], current_members: list[str]) -> bool:

    for i in range(0, len(current_members)):

        if current_members[i] not in pointers:
            return False

        is_not_successor = pointers[current_members[i]].succ != current_members[(i + 1) % len(current_members)]
        is_not_only_node = len(current_members) != 1 or pointers[current_members[i]].succ is not None

        if (is_not_successor and is_not_only_node):
            return False

    return True

def get_ideal_responsible(ideal_log: Path, limit_time: str, all_keys: set[str], operations: OrderedDict[str, Operation], member_intervals: OrderedDict[str, MemberStart| MemberEnd]) -> tuple[dict, dict]:

    op_iter = 0
    op_list = sorted(operations.values(), key=lambda x: x.get_time())

    member_iter = 0
    member_list = sorted(member_intervals.values(), key=lambda x: x.get_time())

    current_members = []
    
    pointers : dict[str,Pointer] = {}


    ongoing_ideal = None
    ideal_states = OrderedDict()


    ongoing_responsibilities = {}
    responsible_intervals = OrderedDict()


    with open(ideal_log, 'r') as f:
        for line in f:
            time, _, member, succ = line.strip().split(', ')

            ## Infer current members
            while member_iter < len(member_list) and member_list[member_iter].get_time() < time:
                membership_node = member_list[member_iter].get_node()
                pos = bisect.bisect_left(current_members, membership_node)


                if member_list[member_iter].is_end():
                    assert not (pos < len(current_members) and current_members[pos] != membership_node), f"Node {member_list[member_iter].get_node()} is not a member, current members:\n{current_members}"
                    current_members.pop(pos)
                else:
                    assert not (pos < len(current_members) and current_members[pos] == membership_node), f"Node {member_list[member_iter].get_node()} is already a member, current members:\n{current_members}"
                    current_members.insert(pos, membership_node)



                is_ideal_state = is_ideal(pointers, current_members)


                if is_ideal_state != (ongoing_ideal is not None):
                    member_time = member_list[member_iter].get_time()

                    if ongoing_ideal is None:
                        ongoing_ideal = IdealStart(member_time, str(len(ideal_states)))
                        ideal_states[ongoing_ideal.get_id()] = ongoing_ideal

                    else:
                        ongoing_ideal.set_end_time(member_time)

                        end_ideal = IdealEnd(member_time, ongoing_ideal.id)
                        ideal_states["End-" + end_ideal.get_id()] = end_ideal

                        ongoing_ideal = None

                member_iter += 1


            if time > limit_time:
                break

            if succ == "null":
                succ = None

            pointers[member] = Pointer(member, succ)



            # print("-"*20)
            # print(f"Time: {time}")
            # print(f"Line: {line}")
            # pprint(pointers)

            #### Responsible
            new_responsibilities = {}
            for pointer in pointers.values():
                node = pointer.node
                succ = pointer.succ

                if succ is None:

                    # print(f"Node {node} is responsible for all keys")
                    new_responsibilities[node] = all_keys
                    continue

                new_keys = new_responsibilities.get(succ, set())
                new_responsibilities[succ] = new_keys



                # print(f"Node {node}, succ {succ}")
                for key in all_keys:
                    # print(f"Checking key {key}")
                    if between(node, key, succ):
                        # print(f"Adding key {key} to {succ}")
                        new_keys.add(key)



            for pointer in pointers.values():
                node = pointer.succ

                if node is None:
                    node = pointer.node

                prev_keys = ongoing_responsibilities.get(node, set())
                new_keys = new_responsibilities.get(node, set())

                # print(pointer.node, pointer.succ)
                # pprint(new_keys)

                if new_keys != prev_keys:
                    # print(f"Node {node} keys: {new_keys},\nold keys: {prev_keys}")
                    for r_start in reversed(responsible_intervals.values()):
                        if type(r_start) == ResponsibleStart and r_start.node == node:
                            # print(f"End {r_start.get_id()} at {time}")
                            r_start.set_end_time(time)
                            r_end = ResponsibleEnd(node, r_start.get_keys(), time, r_start.id)
                            responsible_intervals["End-" + r_end.get_id()] = r_end
                            break

                    r_start = ResponsibleStart(node, new_keys, time, str(len(responsible_intervals)))
                    responsible_intervals[r_start.get_id()] = r_start




            ongoing_responsibilities = new_responsibilities


            #### Ideal
            new_ideal = is_ideal(pointers, current_members)

            if new_ideal != (ongoing_ideal is not None):

                while op_iter < len(op_list) - 1 and op_list[op_iter].get_time() < time:
                    op_iter += 1

                if op_iter == len(op_list) - 1:
                    return ideal_states, responsible_intervals

                time = op_list[op_iter].get_time()

                if ongoing_ideal is None:
                    ongoing_ideal = IdealStart(time, str(len(ideal_states)))
                    ideal_states[ongoing_ideal.get_id()] = ongoing_ideal

                else:


                    ongoing_ideal.set_end_time(time)

                    end_ideal = IdealEnd(time, ongoing_ideal.id)
                    ideal_states["End-" + end_ideal.get_id()] = end_ideal

                    ongoing_ideal = None


    return ideal_states, responsible_intervals
