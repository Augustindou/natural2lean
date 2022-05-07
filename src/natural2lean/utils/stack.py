from typing import Any


class Node:
    def __init__(self, value, next=None) -> None:
        self.value = value
        self.next: Node = next


class Stack:
    def __init__(self) -> None:
        self.head: Node = None
        self.size = 0

    def push(self, value) -> None:
        self.head = Node(value, self.head)
        self.size += 1

    def pop(self):
        if self.size == 0:
            return None

        value = self.head.value
        self.head = self.head.next
        self.size -= 1

        return value

    def peek(self):
        if self.size == 0:
            return None

        return self.head.value

    def __len__(self):
        return self.size

    def __bool__(self):
        return self.size > 0


if __name__ == "__main__":
    stack = Stack()
    for i in range(1, 11):
        stack.push(i)
    print(f"Stack: {stack}")

    for _ in range(1, 6):
        remove = stack.pop()
        print(f"Pop: {remove}")
    print(f"Stack: {stack}")
