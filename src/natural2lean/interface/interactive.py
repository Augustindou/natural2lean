from copy import deepcopy
from dataclasses import dataclass
import re
from InquirerPy import inquirer

from .lean_feedback import get_lean_feedback, FAIL, NO_GOALS
from ..propositions.multiple_propositions import MultiplePropositions
from ..structure.matching import Matching, Translatable
from ..text.theorem import Example, Theorem
from ..text.case import Case
from ..text.have import Have
from ..utils.indentation import indent

RED_COLOR = "\033[1;31m"
RESET_COLOR = "\033[0m"
color_red = lambda s: RED_COLOR + s + RESET_COLOR

STATEMENT_POSSIBILITIES: list[Matching] = [
    Case,
    Have,
    MultiplePropositions,
]
LEAN_HEADER = ""
LEAN_HEADER += "import LeanUtils\n"
LEAN_HEADER += 'def main : IO Unit := IO.println s!"Hello, world!"\n'
LEAN_HEADER += "open Nat\n\n"

# if any element of the key is in the goal, the system will add the value to the proof if it solves a goal
CONCLUSIONS: dict[tuple[str], str] = {
    (r"even", r"divisible"): "try exact ⟨_, by assumption⟩",
    (r"%.*=") : "apply mod_rewrite.mpr; try exact ⟨_, by assumption⟩",
}


@dataclass
class State:
    goals: list[str]
    variables: list[str]
    hypotheses: list[str]
    lean_text: str

    def __str__(self):
        current_goal = self.goals[0] if self.goals else None
        variables = indent("\n".join(self.variables), 2)
        hypotheses = indent("\n".join(self.hypotheses), 2)
        other_goals = indent("\n".join(self.goals[1:]), 2)
        res = ""
        res += f"Current goal: {current_goal}\n"
        res += f"Variables:\n{variables}\n"
        res += f"Hypotheses:\n{hypotheses}\n"
        if len(self.goals) > 1:
            res += f"Other goals:\n{other_goals}\n"
        return indent(res, 4)


def interactive_mode():
    # initial state
    state = State(goals=[], variables=[], hypotheses=[], lean_text=LEAN_HEADER)
    print()

    # get theorem and update text
    theorem = get_theorem()
    state.lean_text += theorem.translate()

    # lean feedback
    lean_feedback = get_lean_feedback(state.lean_text)

    # update goals and hypotheses
    state.goals = lean_feedback.goals
    state.variables = lean_feedback.variables
    state.hypotheses = lean_feedback.hypotheses

    get_proof(state)


def get_proof(state: State, indentation_lvl=1) -> str:
    # print current state
    print(state)
    old_state = deepcopy(state)

    # get next statement
    statement = get_statement(state)

    if (
        statement_is_goal(statement, state.goals[0])
        and (ccl := find_conclusion(state, indentation_lvl=indentation_lvl)) is not None
    ):
        state.lean_text += ccl + "\n\n"
    else:
        state.lean_text += indent(statement.translate(hyp=f"h{len(state.hypotheses)}", hyp_list=state.hypotheses)) + "\n"

    # send to lean
    lean_feedback = get_lean_feedback(state.lean_text)
    # backtrack on fail
    if lean_feedback is FAIL:
        print(color_red(indent("Failed to understand statement. Backtracking...\n")))
        return get_proof(old_state, indentation_lvl=indentation_lvl)
    # end of proof
    if lean_feedback is NO_GOALS:
        print(f"Proof is correct! Congratulations! 🚀")
        return
    # update goals and hypotheses
    state.goals = lean_feedback.goals
    state.variables = lean_feedback.variables
    state.hypotheses = lean_feedback.hypotheses

    return get_proof(state, indentation_lvl=indentation_lvl)


# -------------------------------- GET THEOREM --------------------------------


def get_theorem() -> Theorem:
    match = match_theorem(
        inquirer.text(
            message="Enter a theorem statement.\n ",
            validate=lambda s: match_theorem(s) is not None,
            invalid_message="Invalid theorem. Try 'theorem [th_name]: if [hyp] then [ccl]' or simply 'if [hyp] then [ccl]'",
        ).execute()
    )
    print()
    return match


def match_theorem(input: str):
    possibilities: list[Theorem] = [Theorem, Example]
    for possibility in possibilities:
        try:
            match = possibility.match(input)
        except ValueError:
            match = None
        if match is not None:
            return match
    return None


# ------------------------------- GET STATEMENT -------------------------------


def get_statement(state) -> Translatable:
    match = match_statement(
        inquirer.text(
            message="Input a statement\n ",
            validate=lambda s: match_statement(s) is not None,
            invalid_message="Invalid statement.",
        ).execute()
    )
    print()
    return match


def match_statement(input: str):
    # match statement
    for possibility in STATEMENT_POSSIBILITIES:
        try:
            match = possibility.match(input)
        except ValueError:
            match = None
        if match is not None:
            return match
    return None


# ----------------------------- STATEMENT VS GOAL -----------------------------


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


def find_conclusion(state: State, indentation_lvl: int = 1) -> str:
    for indicators, ccl in CONCLUSIONS.items():
        ccl = indent(ccl.strip(), indentation_lvl)
        for indicator in indicators:
            if re.search(indicator, state.goals[0]):
                # return if it worked
                lean_fb = get_lean_feedback(state.lean_text + ccl)
                if lean_fb is NO_GOALS or len(lean_fb.goals) < len(state.goals):
                    return ccl
    return None
