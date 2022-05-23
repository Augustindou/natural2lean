import textwrap

INDENTATION = "  "


def indent(text, level=1):
    return textwrap.indent(text, INDENTATION * level)


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
