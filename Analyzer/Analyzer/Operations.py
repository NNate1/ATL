module = "Operations"

NO_VALUE = "NO_VALUE"
NO_RESPONSIBLE = "NO_RESPONSIBLE"
NO_REPLIER = "NO_REPLIER"
NO_NODE = "NO_NODE"


class Interval:
    def __init__(self, start_time: str, id : str):
        self.start_time = start_time
        self.id = id
        self.end_time = None
        self.node = ""

    def get_time(self):
        return self.start_time

    def set_end_time(self, end_time: str):
        self.end_time = end_time
    
    def get_end_time(self):
        return self.end_time

    def get_id(self):
        return self.get_name()
        # return self.id

    def get_name(self):
        return f"{type(self).__name__}${id}"

    def is_end(self) -> bool:
        return False

    def __str__(self):
        end_time = getattr(self, "end_time", None)
        return f"{self.get_name()}, {self.start_time} -> {end_time}"

    def __repr__(self):
        return str(self)

class ReadOnly(Interval):
    def __init__(self, time: str, id : str):
        super().__init__(time, id)
    def get_name(self):
        return f"ReadOnly${self.id}"

class ReadOnlyEnd(Interval):
    def __init__(self, time: str, id : str):
        super().__init__(time, id)

    def get_name(self):
        return f"ReadOnly${self.id}"

    def is_end(self) -> bool:
        return True

class Stable(Interval):
    def __init__(self, time: str, id : str):
        super().__init__(time, id)

    def get_name(self):
        return f"Stable${self.id}"

class StableEnd(Interval):
    def __init__(self, time: str, id : str):
        super().__init__(time, id)

    def get_name(self):
        return f"Stable${self.id}"

    def is_end(self) -> bool:
        return True


class MemberStart(Interval):
    def __init__(self, node : str, time: str, id : str):
        super().__init__(time, id)
        self.node = node

    def get_name(self):
        return f"Member-{self.node}${self.id}"

    def get_node(self):
        return self.node

class MemberEnd(Interval):
    def __init__(self, node : str, time: str, id : str):
        super().__init__(time, id)
        self.node = node

    def get_name(self):
        return f"Member-{self.node}${self.id}"

    def is_end(self) -> bool:
        return True

    def get_node(self):
        return self.node

class IdealStart(Interval):
    def __init__(self, time: str, id : str):
        super().__init__(time, id)
    def get_name(self):
        return f"Ideal${self.id}"

class IdealEnd(Interval):
    def __init__(self, time: str, id : str):
        super().__init__(time, id)
    def get_name(self):
        return f"Ideal${self.id}"
    def is_end(self) -> bool:
        return True

class Operation:
    def __init__(
        self,
        time: str,
        optype: str,
        id: str,
        tag: int,
        node: str,
        end_time: str | None = None,
    ):
        self.time = time
        self.optype = optype
        self.id = id
        self.node = node
        self.end_time = end_time

        self.tag = tag

    def get_name(self):
        return f"{self.optype}${self.tag}"

    def get_type(self):
        return self.optype

    def get_time(self):
        return self.time

    def get_id(self):
        return self.id

    def get_node(self):
        assert self.node is not None
        return self.node

    def set_end_time(self, end_time: str):
        self.end_time = end_time

    def get_end_time(self):
        return self.end_time

    def is_end(self) -> bool:
        return False

    def __str__(self):
        return f"{self.time}, {self.get_name()}, id: {self.id}, node: {self.node}, end_time: {self.end_time}"

    def __repr__(self):
        return str(self)


class Reply(Operation):
    def __init__(
        self,
        time: str,
        optype: str,
        id: str,
        tag: int,
        node: str | None = None,
    ):
        super().__init__(time, optype, id, tag, node or NO_REPLIER)

    def get_node(self):
        assert self.node is not NO_REPLIER, "Missing reply node"
        return self.node

    def is_end(self) -> bool:
        return True


class FunctionalOperation(Operation):
    def __init__(
        self,
        time: str,
        optype: str,
        id: str,
        tag: int,
        node: str,
        key: str,
        replier: str | None = None,
        end_time: str | None = None,
    ):
        super().__init__(time, optype, id, tag, node, end_time)
        self.key = key
        self.replier = replier

    def get_key(self):
        return self.key

    def get_replier(self):
        if self.replier is None:
            return NO_NODE
        return self.replier

    def set_replier(self, replier):
        self.replier = replier

    def __str__(self):
        return f"{super().__str__()}, key: {self.key}, replier: {self.replier}"


class Store(FunctionalOperation):
    def __init__(
        self,
        time: str,
        optype: str,
        id: str,
        tag: int,
        node: str,
        key: str,
        value: str,
        replier: str | None = None,
        end_time: str | None = None,
    ):
        super().__init__(time, optype, id, tag, node, key, replier, end_time)
        self.value = value

    def set_value(self, value: str):
        self.value = value

    def get_value(self):
        if self.value is None:
            return NO_VALUE
        return self.value

    def str(self):
        return f"{super().__str__()}, value: {self.value}"


class Lookup(FunctionalOperation):
    def __init__(
        self,
        time: str,
        optype: str,
        id: str,
        tag: int,
        node: str,
        key: str,
        value: str | None = None,
        replier: str | None = None,
        end_time: str | None = None,
    ):
        super().__init__(time, optype, id, tag, node, key, replier, end_time)
        self.value = value

    def set_value(self, value: str):
        self.value = value

    def get_value(self):
        if self.value is None:
            return NO_VALUE
        return self.value

    def __str__(self):
        return f"{super().__str__()}, value: {self.value}"


class FindNode(FunctionalOperation):
    def __init__(
        self,
        time: str,
        optype: str,
        id: str,
        tag: int,
        node: str,
        key: str,
    ):
        super().__init__(time, optype, id, tag, node, key)
        self.responsible = None

    # def set_replier(self, replier: str):
    #     super().set_replier(replier)
    #     self.responsible = replier

    def get_responsible(self):
        if self.responsible is None:
            return NO_NODE
        return self.responsible

    def set_responsible(self, responsible: str):
        self.responsible = responsible

    def __str__(self):
        return f"{super().__str__()}, responsible: {self.responsible}"


class Join(Operation):
    def __init__(
        self,
        time: str,
        optype: str,
        id: str,
        tag: int,
        node: str,
        end_time: str | None = None,
    ):
        super().__init__(time, optype, id, tag, node, end_time)


class Leave(Operation):
    def __init__(
        self,
        time: str,
        optype: str,
        id: str,
        tag: int,
        node: str,
        end_time: str | None = None,
    ):
        super().__init__(time, optype, id, tag, node, end_time)


class Fail(Operation):
    def __init__(
        self,
        time: str,
        optype: str,
        id: str,
        tag: int,
        node: str,
    ):
        super().__init__(time, optype, id, tag, node)
        self.end_time = time
