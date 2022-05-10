import re
from dataclasses import dataclass
from subprocess import PIPE, Popen
from typing import Union
from ..utils.indentation import indent

# if any of ERRORS is matched, the result will be FAIL, and the system will cancel the last input.
ERRORS = [r"tactic .+ failed", r"unknown tactic"]

# patterns need a fullmatch on a line to work
# patterns to recognize a goal, this will be checked first, and will create a new LeanBlock at each match. The only group must contain the goal.
GOAL_PATTERNS = [r"⊢ (.*)"]
# patterns to recognize variables, these will be checked second. The first group must contain the identifier(s) and the second must contain the corresponding set.
VAR_PATTERNS = [
    r"(.*) : ([ℕℤℚℝ].*)",
]
# patterns to recognize hypotheses, these will be checked last. the first group contains hypothesis name and the second contains the set.
HYP_PATTERNS = [r"(.*) : (.*)"]

# these are constants to understand better what is returned
NO_GOALS = 1
FAIL = -1
BACKTRACK = -2
EXIT = -3

# paths for where to execute
LEAN_PROJECT_DIRECTORY = "lean"
LEAN_MAIN_FILE = "Main.lean"
BUILD_COMMAND = "lake build"


@dataclass(frozen=True)
class LeanBlock:
    """A block of results from lean."""

    # (identifiers, set), variables can contain multiple identifiers
    variables: list[tuple[str, str]]
    # (hypothesis name, expression), each hypothesis can only contain one identifier
    hypotheses: list[tuple[str, str]]
    # the goal for this block
    goal: str

    def __str__(self) -> str:
        # variables
        variables = "\n".join(f"{_id} : {_set}" for _id, _set in self.variables)
        var_block = f"Variables :\n{indent(variables)}\n" if self.variables else ""

        # hypotheses
        hypotheses = "\n".join(f"{_name} : {_expr}" for _name, _expr in self.hypotheses)
        hyp_block = f"Hypotheses :\n{indent(hypotheses)}\n" if self.hypotheses else ""

        return self.goal + "\n" + var_block + hyp_block


def get_lean_feedback(input: str) -> Union[list[LeanBlock], int]:
    """Gets the feedback from lean.

    Args:
        input (str): the lean text to be checked

    Returns:
        list[LeanBlock]: a list of lean blocks, each containing variables, hypotheses and goals.
        int: FAIL on error, NO_GOALS the proof has worked
    """

    # get feedback
    feedback = get_raw_feedback(input)

    # errors
    match = match_list(ERRORS, feedback, type="search")
    if match is not None:
        return FAIL

    # separate blocks
    lean_blocks = separate_elements(feedback)

    if lean_blocks == []:
        return NO_GOALS

    return lean_blocks


def separate_elements(raw_feedback: str) -> list[LeanBlock]:
    """Separates the different elements, based on GOAL_PATTERNS, VAR_PATTERNS and HYP_PATTERNS.

    Args:
        raw_feedback (str): the feedback from lean.

    Returns:
        list[LeanBlock]: a list of goal structures.
    """

    # initialize variables
    blocks: list[LeanBlock] = []
    current_variables: list[tuple[str, str]] = []
    current_hypotheses: list[tuple[str, str]] = []

    # iterate over each line
    for line in raw_feedback.splitlines():
        # goal
        match = match_list(GOAL_PATTERNS, line, type="fullmatch")
        if match is not None:
            # create a new block
            blocks.append(
                LeanBlock(
                    variables=current_variables,
                    hypotheses=current_hypotheses,
                    goal=match.group(1),
                )
            )
            # clean the current variables and hypotheses
            current_variables = []
            current_hypotheses = []
            # skip to next line
            continue

        # variable
        match = match_list(VAR_PATTERNS, line, type="fullmatch")
        if match is not None:
            # add the variable to the current variables
            current_variables.append((match.group(1), match.group(2)))
            # skip to next line
            continue

        # hypothesis
        match = match_list(HYP_PATTERNS, line, type="fullmatch")
        if match is not None:
            # add each hypothesis separately
            for hyp in match.group(1).split():
                current_hypotheses.append((hyp, match.group(2)))
            # skip to next line
            continue

    return blocks


def match_list(patterns: list[str], text: str, type: str = "search") -> re.Match:
    """Returns the first match of a list of patterns.

    Args:
        patterns (list[str]): a list of patterns to try
        text (str): the text to match
        type (str, optional): the type of call, any of "search", "fullmatch", "match". Defaults to "search".

    Returns:
        bool: _description_
    """
    if type not in ["search", "fullmatch", "match"]:
        raise ValueError(f"type must be one of 'search', 'fullmatch', 'match'")
    if type == "search":
        call = re.search
    if type == "fullmatch":
        call = re.fullmatch
    if type == "match":
        call = re.match

    # check each pattern
    for pattern in patterns:
        match = call(pattern, text)
        # return first match
        if match is not None:
            return match

    # no match found
    return None


def get_raw_feedback(input: str) -> str:
    """Gets the raw feedback from lean.

    Args:
        input (str): the text to be fed to lean.

    Returns:
        str: the raw (terminal) feedback
    """

    with open(f"{LEAN_PROJECT_DIRECTORY}/{LEAN_MAIN_FILE}", "w") as f:
        f.write(input)

    raw_feedback = (
        Popen(
            BUILD_COMMAND,
            shell=True,
            cwd=LEAN_PROJECT_DIRECTORY,
            stdout=PIPE,
            stderr=PIPE,
        )
        .stdout.read()
        .decode("utf-8")
    )

    return raw_feedback
