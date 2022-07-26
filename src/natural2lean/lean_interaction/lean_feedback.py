import re
from pathlib import Path
from subprocess import PIPE, Popen
from typing import Callable, Union
from dataclasses import dataclass
from ..utils.exceptions import LeanError
from ..utils.text import indent, nth
from ..proof_elements.statement.statement import Statement
from ..proof_elements.statement.induction import Induction
from ..proof_elements.theorem.theorem import Theorem


@dataclass(frozen=True)
class LeanBlock:
    """A block of results from lean, each one containing variables, hypotheses and a goal."""

    # (name, set), variables can contain multiple identifiers
    variables: list[tuple[str, str]]
    # (hypothesis name, expression), each hypothesis can only contain one identifier
    hypotheses: list[tuple[str, str]]
    # the goal for this block
    goal: str

    def __str__(self) -> str:
        # for missing cases
        if not self.variables and not self.hypotheses:
            return f"{self.goal} (missing case)"

        # variables
        if self.variables:
            variables = "\n".join(f"{id_} : {set_}" for id_, set_ in self.variables)
            var_block = f"Variables we can use :\n{indent(variables)}\n"
        else:
            var_block = ""

        # hypotheses
        if self.hypotheses:
            hypotheses = "\n".join(
                f"{name_} : {expr_}" for name_, expr_ in self.hypotheses
            )
            hyp_block = (
                f"What we have shown so far (for this goal) :\n{indent(hypotheses)}\n"
            )
        else:
            hyp_block = ""

        return self.goal + "\n" + var_block + hyp_block


@dataclass
class State:
    goals: list[LeanBlock]
    last_statement: Union[Theorem, Statement]
    lean_text: str

    def __str__(self):
        if len(self.goals) == 0:
            return ""

        if len(self.goals) == 1:
            return f"To finish this proof, we need to prove this: {indent(str(self.goals[0]))}"
        
        result = f"To finish this proof, we need to solve these {len(self.goals)} cases (goals):"
        for i, goal in enumerate(self.goals):
            result += f"\n{nth(i+1)} case: solve {indent(str(goal))}"

        return result


@dataclass
class SpecificError:
    pattern: str
    statement_check: Callable
    added_blocks: Callable


# if any of ERRORS is matched, the result will be FAIL, and the system will cancel the last input.
ERRORS = [
    r"error: tactic .+ failed",
    r"error: ring failed",
    r"error: unknown .+",
    r"error: expected .+",
    r"error: invalid .+",
    r"error: .+ is missing",
    r"error: type mismatch",
]

SPECIFIC_ERRORS = [
    SpecificError(
        pattern=r"error: unexpected end of input;",
        statement_check=lambda st: isinstance(st, Induction),
        added_blocks=lambda st: [
            LeanBlock(
                variables=[], hypotheses=[], goal=f"values of {st.variable.translate()}"
            )
        ],
    )
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

# missing cases are all lines between "missing cases" and "././" or "error" (other error)
MISSING_CASES_START = r"missing cases:\n"
MISSING_CASES_STOP = r"(?:\./\./|error:)"

MAIN_FILE = "Main.lean"
BUILD_COMMAND = "lake build"


def lean_feedback(
    input: str, statement: Statement, project_directory: Path
) -> list[LeanBlock]:
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
        raise LeanError(f"Lean error: {feedback[match.start():match.end()]}\n")

    # separate blocks
    lean_blocks = separate_elements(feedback)

    # check missing cases
    missing_cases = get_missing_cases(feedback)

    # check specific errors
    specific_errors = check_specific_errors(statement, feedback)

    return specific_errors + lean_blocks + missing_cases


def raw_feedback(input: str, project_directory: Path) -> str:
    """Gets the raw feedback from lean.

    Args:
        input (str): the text to be fed to lean.

    Returns:
        str: the raw (terminal) feedback
    """

    with open(project_directory / MAIN_FILE, "w") as f:
        f.write(input)

    res = Popen(
        BUILD_COMMAND,
        shell=True,
        cwd=project_directory,
        stdout=PIPE,
        stderr=PIPE,
    )

    return res.stdout.read().decode("utf-8") + res.stderr.read().decode("utf-8")


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
        raise Exception(f"type must be one of 'search', 'fullmatch', 'match'")
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
    """Separates the different elements, based on `GOAL_PATTERNS`, `SECONDARY_GOAL_PATTERNS`, `VAR_PATTERNS` and `HYP_PATTERNS`.

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


def get_missing_cases(raw_feedback: str) -> list[LeanBlock]:
    missing_cases = []

    match = re.search(MISSING_CASES_START, raw_feedback)
    if not match:
        return []

    for line in raw_feedback[match.end() :].splitlines():
        if re.match(MISSING_CASES_STOP, line):
            break

        missing_cases.append(LeanBlock([], [], line))

    return missing_cases


def check_specific_errors(statement: Statement, raw_feedback: str) -> list[LeanBlock]:
    if not statement:
        return []

    specific_blocks = []
    for error in SPECIFIC_ERRORS:
        if re.search(error.pattern, raw_feedback) and error.statement_check(statement):
            specific_blocks += error.added_blocks(statement)

    return specific_blocks
