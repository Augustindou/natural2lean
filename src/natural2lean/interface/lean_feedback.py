from dataclasses import dataclass
import re
from subprocess import PIPE, Popen

GOAL_PATTERN = r"⊢ (.*)"
HYP_BLOCK_PATTERN = r"unsolved goals\n((?:.|\s)*?)\n⊢"
PATH_TO_MAIN = "lean/Main.lean"
SETS = ["ℕ", "ℤ", "ℚ", "ℝ"]


@dataclass(frozen=True)
class LeanFeedback:
    """Feedback from lean."""

    variables: dict[str, str]
    hypotheses: list[str]
    goals: list[str]


def get_lean_feedback(input: str) -> LeanFeedback:
    # copy to main
    with open(PATH_TO_MAIN, "w") as f:
        f.write(input)

    # get feedback
    raw_feedback = (
        Popen("lake build -d=lean", shell=True, stdout=PIPE, stderr=PIPE)
        .stdout.read()
        .decode("utf-8")
    )

    # get goals
    goals = re.findall(GOAL_PATTERN, raw_feedback)

    # parse variables and hypotheses
    match = re.search(HYP_BLOCK_PATTERN, raw_feedback)
    if match is None:
        return None
    statements = match.group(1).splitlines()
    variables = []
    hypotheses = []
    for statement in statements:
        if statement.split(" : ")[1].split()[0] in SETS:
            variables.append(statement)
        else:
            hypotheses.append(statement)

    return LeanFeedback(variables=variables, hypotheses=hypotheses, goals=goals)
