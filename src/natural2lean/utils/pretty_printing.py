# code from https://stackoverflow.com/questions/32500167/how-to-show-diff-of-two-string-sequences-in-colors

import difflib

red = lambda text: f"\033[38;2;255;0;0m{text}\033[38;2;255;255;255m"
green = lambda text: f"\033[38;2;0;255;0m{text}\033[38;2;255;255;255m"
blue = lambda text: f"\033[38;2;0;0;255m{text}\033[38;2;255;255;255m"
white = lambda text: f"\033[38;2;255;255;255m{text}\033[38;2;255;255;255m"


def string_differences(old, new):
    result = ""
    codes = difflib.SequenceMatcher(a=old, b=new).get_opcodes()
    for code in codes:
        if code[0] == "equal":
            result += white(old[code[1] : code[2]])
        # elif code[0] in ["delete", "replace"]:
        #     result += red(old[code[1] : code[2]])
        elif code[0] in ["insert", "replace"]:
            result += green(new[code[3] : code[4]])
    return result


def nth(n):
    if n == 1:
        return "1st"
    if n == 2:
        return "2nd"
    if n == 3:
        return "3rd"
    return f"{n}th"

if __name__ == "__main__":
    print(get_edits_string("abce", "abcd"))