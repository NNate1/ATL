import bisect 

from typing import OrderedDict
from pathlib import Path

from Operations import (
    MemberStart,
    MemberEnd,
    IdealStart,
    IdealEnd,
    Operation
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

def detect_ideal(ideal_log: Path, limit_time: str, keys: set[str], operations: OrderedDict[str, Operation], member_intervals: OrderedDict[str, MemberStart| MemberEnd]) -> tuple[dict, dict]:

    op_iter = 0
    op_list = sorted(operations.values(), key=lambda x: x.get_time())

    member_iter = 0
    member_list = sorted(member_intervals.values(), key=lambda x: x.get_time())

    current_members = []
    
    pointers = {}


    ongoing_ideal = None
    ideal_states = OrderedDict()

    responsibilites = {}

    with open(ideal_log, 'r') as f:
        for line in f:
            time, op, member, succ = line.strip().split(', ')
            if time > limit_time:
                break

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


            new_ideal = True
            for i in range(0, len(current_members)):

                is_not_in_pointers = current_members[i] not in pointers
                is_not_successor = pointers[current_members[i]].succ != current_members[(i + 1) % len(current_members)]
                is_not_only_node = len(current_members) != 1 or pointers[current_members[i]].succ is not None

                if is_not_in_pointers or (is_not_successor and is_not_only_node):
                    new_ideal = False
                    break 
            # else:
            #     new_ideal = True

            if new_ideal != (ongoing_ideal is not None):
                if ongoing_ideal is None:
                    ongoing_ideal = IdealStart(time, str(len(ideal_states)))
                    ideal_states[ongoing_ideal.get_id()] = ongoing_ideal

                else:

                    while op_iter < len(op_list) and op_list[op_iter].get_time() < time:
                        op_iter += 1

                    end_time = op_list[op_iter].get_time()
                    ongoing_ideal.set_end_time(end_time)

                    end_ideal = IdealEnd(end_time, ongoing_ideal.id)
                    ideal_states["End-" + end_ideal.get_id()] = end_ideal

                    ongoing_ideal = None


    return ideal_states, responsibilites
