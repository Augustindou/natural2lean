from pathlib import Path
import re
from .lean_feedback import LeanBlock, State, lean_feedback
from ..utils.text import indent
from ..utils.exceptions import LeanError, NoConclusion
from ..utils.translatable import Translatable


# if any element of the key is in the goal, the system will add the value to the proof if it solves a goal
CONCLUSIONS: dict[tuple[str], str] = {
    (r"not\s*divisible",): "simp_all [divisible]",
    (r"even", r"divisible"): "try exact ⟨_, by assumption⟩",
    (r"%.*=",): "apply mod_rewrite.mpr; try exact ⟨_, by assumption⟩",
}


def get_conclusion(
    state: State, statement: Translatable, project_directory: Path
) -> tuple[list[LeanBlock], str]:
    """Returns the conclusion to add to the proof if the statement is a goal, or None if the conclusion does not work / the statement is not a goal."""
    if statement_is_goal(statement, state.goals[0].goal):
        return find_conclusion(state, project_directory)
    raise NoConclusion(f"No conclusion found for {state.goals[0].goal}")


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


def find_conclusion(
    state: State, project_directory: Path
) -> tuple[list[LeanBlock], str]:
    for indicators, ccl in CONCLUSIONS.items():
        indented_ccl = indent(ccl.strip())
        for indicator in indicators:
            if re.search(indicator, state.goals[0].goal):

                try:
                    lean_fb = lean_feedback(
                        state.lean_text + "\n\n" + indented_ccl,
                        project_directory,
                    )
                except LeanError:
                    break

                if len(lean_fb) < len(state.goals):
                    return lean_fb, ccl

                break
    raise NoConclusion(f"No conclusion found for {state.goals[0].goal}")
