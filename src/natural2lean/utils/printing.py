import textwrap

red = lambda s: "\u001b[31m" + s + "\u001b[0m"
green = lambda s: "\u001b[32m" + s + "\u001b[0m"
cyan = lambda s: "\u001b[36m" + s + "\u001b[0m"
underline = lambda s: "\u001b[4m" + s + "\u001b[0m"


INDENTATION = "  "


def indent(text, level=1):
    return textwrap.indent(text, INDENTATION * level)


def string_differences(old: str, new: str) -> str:
    """Adds color to the lines in new that were not in old.

    Args:
        old (str): the old string.
        new (str): the new string.

    Returns:
        str: The new string with
    """
    result = ""

    for line in new.splitlines():
        if line in old:
            result += line + "\n"
        else:
            result += green(line) + "\n"

    return result


def nth(n):
    if n == 1:
        return "1st"
    if n == 2:
        return "2nd"
    if n == 3:
        return "3rd"
    return f"{n}th"


def subscript(n: int):
    subscripts = {
        "0": "₀",
        "1": "₁",
        "2": "₂",
        "3": "₃",
        "4": "₄",
        "5": "₅",
        "6": "₆",
        "7": "₇",
        "8": "₈",
        "9": "₉",
    }

    result = ""
    for digit in str(n):
        result += subscripts[digit]

    return result
