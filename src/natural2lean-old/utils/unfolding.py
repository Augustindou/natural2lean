import re


def unfold(pattern: str, string: str) -> tuple[list[str], list[str]]:
    """Recursively unfolds the pattern in the string.

    Args:
        pattern (str): pattern to unfold, must contain 4 groups : complete match, element, separator, last element or tail (to be matched recursively).
        string (str): string to unfold.

    Returns:
        elements (list[str]): list of (n) elements in the string.
        separators (list[str]): list of (n-1) separators between elements.
    """
    elements = []
    separators = []

    # first match, has to work
    match = re.fullmatch(pattern, string)
    if match == None:
        return None, None

    # adding the first element
    elements.append(match.group(2).strip())

    # case for no second part (only 1 element)
    if match.group(3) == None:
        return elements, separators

    # adding the separator
    separators.append(match.group(3).strip())

    # matching the second part
    if re.fullmatch(pattern, match.group(4)) == None:
        # no more unfolding
        elements.append(match.group(4).strip())
        return elements, separators

    else:
        # unfold recursively
        new_elements, new_separators = unfold(pattern, match.group(4))
        # adding at the end of the lists
        elements += new_elements
        separators += new_separators

        return elements, separators


if __name__ == "__main__":
    pattern = r"( *([a-zA-Z]\w*) *(,) *([a-zA-Z]\w*(?: *, *[a-zA-Z]\w*)*) *)"
    print(unfold(pattern, "x_1 , x_2 , x_3"))
