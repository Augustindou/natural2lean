from dataclasses import dataclass
import re
from subprocess import PIPE, Popen

GOAL_PATTERN = r"⊢ (.*)"
HYP_BLOCK_PATTERN = r"unsolved goals\n((?:.|\s)*?)\n⊢"
BACKTRACK_INDICATORS = ["BACKTRACK", "BACK"]
TACTIC_FAILED = r"tactic .+ failed"
PATH_TO_MAIN = "lean/Main.lean"
SETS = ["ℕ", "ℤ", "ℚ", "ℝ"]

NO_GOALS = 0
BACKTRACK = -1
FAIL = -2


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
        Popen("lake build", shell=True, cwd="lean", stdout=PIPE, stderr=PIPE)
        .stdout.read()
        .decode("utf-8")
    )
    
    if raw_feedback.upper() in BACKTRACK_INDICATORS:
        return BACKTRACK

    # get goals
    goals = re.findall(GOAL_PATTERN, raw_feedback)
    if not goals:
        return NO_GOALS

    # match failed
    match = re.search(TACTIC_FAILED, raw_feedback)
    if match:
        return FAIL

    # parse variables and hypotheses
    match = re.search(HYP_BLOCK_PATTERN, raw_feedback)
    if match is None:
        raise Exception("Could not parse lean feedback")

    statements = match.group(1).splitlines()
    variables = []
    hypotheses = []
    for statement in statements:
        # skip "case inr.inl"
        if statement.split()[0] in ["case"]:
            continue
        if statement.split(":")[1].split()[0] in SETS:
            variables.append(statement)
        else:
            hypotheses.append(statement)

    return LeanFeedback(variables=variables, hypotheses=hypotheses, goals=goals)
