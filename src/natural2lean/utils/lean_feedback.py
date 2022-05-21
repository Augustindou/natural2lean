import re
from pathlib import Path
from subprocess import PIPE, Popen
from typing import Union
from dataclasses import dataclass
from .exceptions import LeanError, TranslationError
from .printing import indent, nth
from ..proof_elements.statement.statement import Statement
from ..proof_elements.theorem.theorem import Theorem

# if any of ERRORS is matched, the result will be FAIL, and the system will cancel the last input.
ERRORS = [
    r"tactic .+ failed",
    r"error: unknown tactic",
    r"error: expected .*",
    r"error: unknown namespace",
]

# patterns need a fullmatch on a line to work
# patterns to recognize a goal, this will be checked first, and will create a new LeanBlock at each match. The only group must contain the goal.
GOAL_PATTERNS = [r"⊢ (.*)"]
# patterns to recognize variables, these will be checked second. The first group must contain the identifier(s) and the second must contain the corresponding set.
VAR_PATTERNS = [
    r"(.*) : ([ℕℤℚℝ].*)",
]
# patterns to recognize hypotheses, these will be checked last. the first group contains hypothesis name and the second contains the set.
HYP_PATTERNS = [r"(.*) : (.*)"]

MAIN_FILE = "Main.lean"
BUILD_COMMAND = "lake build"

@dataclass(frozen=True)
class LeanBlock:
    """A block of results from lean, each one containing variables, hypotheses and a goal."""

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


@dataclass
class State:
    goals: list[LeanBlock]
    statements: list[Union[Statement, Theorem]]
    lean_text: str

    def __str__(self):
        if len(self.goals) == 0:
            return ""

        result = f"Current goal: {indent(str(self.goals[0]))[2:]}"
        for i, goal in enumerate(self.goals[1:]):
            result += f"\n{nth(i+2)} goal: {indent(str(goal))}"

        return result

def lean_feedback(input: str, project_directory:Path) -> list[LeanBlock]:
    """Gets the feedback from lean.

    Args:
        input (str): the lean text to be checked

    Returns:
        list[LeanBlock]: a list of lean blocks, each containing variables, hypotheses and goals.
    """

    # get feedback
    feedback = raw_feedback(input, project_directory)

    # errors
    match = match_list(ERRORS, feedback, type="search")
    if match is not None:
        raise LeanError(f"Lean error: {match.group(0)}")

    # separate blocks
    lean_blocks = separate_elements(feedback)

    return lean_blocks

def raw_feedback(input:str, project_directory: Path) -> str:
    """Gets the raw feedback from lean.

    Args:
        input (str): the text to be fed to lean.

    Returns:
        str: the raw (terminal) feedback
    """

    with open(project_directory / MAIN_FILE, "w") as f:
        f.write(input)

    raw = (
        Popen(
            BUILD_COMMAND,
            shell=True,
            cwd=project_directory,
            stdout=PIPE,
            stderr=PIPE,
        )
        .stdout.read()
        .decode("utf-8")
    )

    return raw



# -------------------------------------------------------------------------
# HELPER FUNCTIONS
# -------------------------------------------------------------------------

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
        raise TranslationError(f"type must be one of 'search', 'fullmatch', 'match'")
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
