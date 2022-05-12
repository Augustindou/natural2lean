red = lambda text: f"\033[38;2;255;0;0m{text}\033[38;2;255;255;255m"
green = lambda text: f"\033[38;2;0;255;0m{text}\033[38;2;255;255;255m"
blue = lambda text: f"\033[38;2;0;0;255m{text}\033[38;2;255;255;255m"
white = lambda text: f"\033[38;2;255;255;255m{text}\033[38;2;255;255;255m"


def string_differences(old: str, new: str) -> str:
    result = ""

    for line in new.splitlines():
        if line in old:
            result += white(line) + "\n"
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


def to_indices(n: int):
    indices = {
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
        result += indices[digit]

    return result


if __name__ == "__main__":
    print(string_differences("abce", "abcd\nhello\nworld\n\n\ntest"))
