from copy import deepcopy
from dataclasses import dataclass
from InquirerPy import inquirer

from .lean_feedback import get_lean_feedback
from ..math_mode.multiple_identifiers import MultipleIdentifiers
from ..structure.matching import Translatable
from ..structure.theorem import Example, Theorem
from ..text.have import Have
from ..utils.indentation import indent


STATEMENT_POSSIBILITIES = [
    Have,
]
LEAN_HEADER = ""
LEAN_HEADER += "import LeanUtils.Tactic\n"
LEAN_HEADER += "open Nat\n\n"

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


def get_proof(state:State) -> str:
    # print current state
    print(state)
    old_state = deepcopy(state)
    
    # get next statement
    statement = get_statement(state)
    state.lean_text += indent(statement.translate(hyp=f"h{len(state.hypotheses)}"))
    
    # send to lean
    lean_feedback = get_lean_feedback(state.lean_text)
    # update goals and hypotheses
    state.goals = lean_feedback.goals
    state.variables = lean_feedback.variables
    state.hypotheses = lean_feedback.hypotheses
    
    # more goals
    if len(state.goals) > len(old_state.goals):
        # TODO split
        pass

    if len(state.goals) == len(old_state.goals):
        return get_proof(state)

    if len(state.goals) < len(old_state.goals):
        return state.lean_text
    
    print("why did i get here ?")
    print(state)


# -------------------------------- GET THEOREM --------------------------------


def get_theorem() -> Theorem:
    match = match_theorem(
        inquirer.text(
            message="What theorem do you want to prove?\n  ",
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
            message="Input a statement\n  ",
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
