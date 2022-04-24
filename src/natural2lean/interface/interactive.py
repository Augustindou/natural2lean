import PyInquirer

from ..structure.theorem import Example, Theorem
from ..text.have import Have


TH_ERROR_MESSAGE = ""
TH_ERROR_MESSAGE += "We could not match a theorem. \n  "
TH_ERROR_MESSAGE += "Try 'theorem [th_name]: [th_statement (implication)]' \n  "
TH_ERROR_MESSAGE += "or '[theorem statement (implication)]'\n"

SENTENCES_POSSIBILITIES = [
    Have,
]


def interactive_mode():
    print("Interactive mode is not implemented yet")

    # match first theorem
    last_input = PyInquirer.prompt(th_question())["theorem"]
    match = match_theorem(last_input)
    # loop if error
    while match is None:
        # match again
        last_input = PyInquirer.prompt(th_question(TH_ERROR_MESSAGE, last_input))[
            "theorem"
        ]
        match = match_theorem(last_input)

    print(match.translate())


# --------------------------------- THEOREM UTIL FUNCTIONS ---------------------------------


def th_question(
    message: str = "What theorem do you want to prove? (use ctrl+O to send)\n",
    default: str = "",
):
    return [
        {
            "type": "editor",
            "name": "theorem",
            "message": message,
            "default": default,
        }
    ]


def match_theorem(input: str):
    # match theorem
    try:
        match = Theorem.match(input)
    except ValueError:
        match = None

    if match is not None:
        return match

    # match example
    try:
        match = Example.match(input)
    except ValueError:
        match = None

    if match is not None:
        return match

    # no match found
    return None
