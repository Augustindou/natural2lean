from pathlib import Path
import re

from natural2lean.proof_elements.statement.statement import Statement
from .lean_feedback import LeanBlock, State, lean_feedback
from ..utils.text import indent
from ..utils.exceptions import LeanError, NoConclusion
from ..utils.translatable import Translatable


# if any element of the key is in the goal, the system will add the value to the proof if it solves a goal
CONCLUSIONS: dict[tuple[str], str] = {
    (r"¬divisible", r"even", r"odd", r"divisible"): "simp_all",
    (r"∃ .+, .+",): "exact ⟨_, by repeat (first | trivial | ring | simp_all)⟩",
    (
        r"even",
    ): "apply even_rewrite.mpr; exact ⟨_, by repeat (first | trivial | ring | simp_all)⟩",
    (
        r"odd",
    ): "apply odd_rewrite.mpr; exact ⟨_, by repeat (first | trivial | ring | simp_all)⟩",
    (
        r"%.*=",
        r"divisible",
    ): "apply mod_rewrite.mpr; exact ⟨_, by repeat (first | trivial | ring | simp_all)⟩",
    (r"",): "assumption",
}


def get_conclusion(
    state: State,
    goals: str,
    statement: Translatable,
    project_directory: Path,
) -> tuple[list[LeanBlock], str]:
    """Returns the conclusion to add to the proof if the statement is a goal, or None if the conclusion does not work / the statement is not a goal."""
    if statement_is_goal(statement, goals):
        return find_conclusion(state, goals, statement, project_directory)
    raise NoConclusion(f"No conclusion found for {state.goals[0].goal}")


def statement_is_goal(statement: Translatable, goals: set[str]) -> bool:
    # TODO : improve the method for this
    # get first line
    tr = statement.translate().splitlines()[0]

    # remove parenth and spaces
    tr = tr.replace("(", "").replace(")", "").replace(" ", "")

    for goal in goals:
        # remove parenth and spaces
        goal = goal.replace("(", "").replace(")", "").replace(" ", "")
        if goal in tr:
            return True
    return False


def find_conclusion(
    state: State, goals: list[str], statement: Statement, project_directory: Path
) -> tuple[list[LeanBlock], str]:
    for indicators, ccl in CONCLUSIONS.items():
        indented_ccl = indent(ccl.strip())
        for indicator in indicators:
            if any(re.search(indicator, goal) for goal in goals):
                try:
                    lean_fb = lean_feedback(
                        input=state.lean_text + "\n\n" + indented_ccl,
                        statement=statement,
                        project_directory=project_directory,
                    )
                except LeanError:
                    break

                if len(lean_fb) < len(state.goals):
                    return lean_fb, ccl

                break
    raise NoConclusion(f"No conclusion found for {state.goals[0].goal}")
