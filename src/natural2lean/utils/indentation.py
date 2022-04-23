import textwrap

INDENTATION = "  "


def indent(text, level=1):
    return textwrap.indent(text, INDENTATION * level)
