import re

from .lean_feedback import FAIL, NO_GOALS, get_lean_feedback
from ..structure.matching import Translatable
from ..utils.indentation import indent


# if any element of the key is in the goal, the system will add the value to the proof if it solves a goal
CONCLUSIONS: dict[tuple[str], str] = {
    (r"even", r"divisible"): "try exact ⟨_, by assumption⟩",
    (r"%.*=",): "apply mod_rewrite.mpr; try exact ⟨_, by assumption⟩",
}


def get_conclusion(state, statement: Translatable) -> str:
    """Returns the conclusion to add to the proof if the statement is a goal, or None if the conclusion does not work / the statement is not a goal."""
    if statement_is_goal(statement, state.goals[0].goal):
        return find_conclusion(state)
    return None


def statement_is_goal(statement: Translatable, goal: str) -> bool:
    # TODO : improve the method for this
    # get first line
    tr = statement.translate().splitlines()[0]
    # remove parenthesis and spaces
    tr = tr.replace("(", "").replace(")", "").replace(" ", "")
    goal = goal.replace("(", "").replace(")", "").replace(" ", "")

    # compare
    if goal in tr:
        return True
    return False


def find_conclusion(state) -> str:
    for indicators, ccl in CONCLUSIONS.items():
        ccl = indent(ccl.strip())
        for indicator in indicators:
            if re.search(indicator, state.goals[0].goal):
                lean_fb = get_lean_feedback(state.lean_text + ccl)
                if lean_fb is FAIL:
                    break
                if lean_fb is NO_GOALS or len(lean_fb) < len(state.goals):
                    return ccl
                break
    return None
