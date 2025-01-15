import bisect 

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

    if a < c:
        return a < b and b <= c

    return a <= b or b < c

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
            if time > limit_time:
                break

            ## Infer current members
            while member_iter < len(member_list) and member_list[member_iter].get_time() < time:
                member = member_list[member_iter].get_node()
                pos = bisect.bisect_left(current_members, member)


                if member_list[member_iter].is_end():
                    assert not (pos < len(current_members) and current_members[pos] != member), f"Node {member_list[member_iter].get_node()} is not a member, current members:\n{current_members}"
                    current_members.pop(pos)
                else:
                    assert not (pos < len(current_members) and current_members[pos] == member), f"Node {member_list[member_iter].get_node()} is already a member, current members:\n{current_members}"
                    current_members.insert(pos, member)

                member_iter += 1

            if succ == "null":
                succ = None

            pointers[member] = Pointer(member, succ)


            #### Responsible
            new_responsibilities = {}
            for pointer in pointers.values():
                node = pointer.node
                succ = pointer.succ

                if succ is None:

                    new_responsibilities[node] = all_keys
                    continue

                new_keys = new_responsibilities.get(succ, set())
                new_responsibilities[succ] = new_keys


                for key in all_keys:
                    if between(node, key, succ):
                        new_keys.add(key)


            for pointer in pointers.values():
                node = pointer.succ

                if node is None:
                    node = pointer.node

                prev_keys = ongoing_responsibilities.get(node, set())
                new_keys = new_responsibilities.get(node, set())


                for key in prev_keys ^ new_keys:
                    if key not in prev_keys:
                        r_start = ResponsibleStart(node, key, time, str(len(responsible_intervals)))
                        responsible_intervals[r_start.get_id()] = r_start
                    else:
                        for r_start in reversed(responsible_intervals.values()):
                            if type(r_start) == ResponsibleStart and r_start.node == node and r_start.key == key:
                                r_start.set_end_time(time)
                                r_end = ResponsibleEnd(node, key, time, r_start.id)
                                responsible_intervals["End-" + r_end.get_id()] = r_end

                                break




            ongoing_responsibilities = new_responsibilities


            #### Ideal
            new_ideal = True
            for i in range(0, len(current_members)):

                is_not_in_pointers = current_members[i] not in pointers
                is_not_successor = pointers[current_members[i]].succ != current_members[(i + 1) % len(current_members)]
                is_not_only_node = len(current_members) != 1 or pointers[current_members[i]].succ is not None

                if is_not_in_pointers or (is_not_successor and is_not_only_node):
                    new_ideal = False
                    break 

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
