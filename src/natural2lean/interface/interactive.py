from dataclasses import dataclass
from .conclude_proof import get_conclusion
from .lean_feedback import BACKTRACK, EXIT, FAIL, NO_GOALS, LeanBlock, get_lean_feedback
from .user_input import theorem_prompt, statement_prompt
from ..structure.matching import Translatable
from ..utils.stack import Stack
from ..utils.indentation import indent
from ..utils.pretty_printing import nth, get_edits_string


LEAN_HEADER = (
    "import LeanUtils\n"
    'def main : IO Unit := IO.println s!"Hello, world!"\n'
    "open Nat"
)

red = lambda s: "\033[31m" + s + "\033[0m"
green = lambda s: "\033[32m" + s + "\033[0m"


@dataclass
class State:
    goals: list[LeanBlock]
    lean_text: str

    def __str__(self):
        if len(self.goals) == 0:
            return ""

        result = f"Current goal: {indent(str(self.goals[0]))[2:]}"
        for i, goal in enumerate(self.goals[1:]):
            f"\n{nth(i+1)} goal: {indent(str(goal))}"

        return result


def interactive_mode():
    # initialize stack
    stack = Stack()
    stack.push(State(goals=[], lean_text=LEAN_HEADER))

    # print welcome message with info
    # TODO

    # main loop
    while True:
        current_state: State = stack.peek()
        print(current_state)
        # get theorem if no goals
        if not current_state.goals:
            theorem = theorem_prompt()

            if theorem == EXIT:
                print(red("👋 Bye !\n"))
                return

            if theorem == BACKTRACK:
                backtrack(stack)
                continue

            # getting feedback
            new_lean_text = current_state.lean_text + "\n\n" + theorem.translate()
            lean_feedback = get_lean_feedback(new_lean_text)

            if lean_feedback == FAIL:
                print(red("🧨 Theorem statement didn't work, try again."))
                continue

            if lean_feedback == NO_GOALS:
                print(
                    red(
                        "🧨 It seems like your theorem statement did not produce any goal to solve. Try again."
                    )
                )
                continue

            # lean_feedback is a list of goals
            stack.push(State(goals=lean_feedback, lean_text=new_lean_text))
            continue

        # get statement if goals
        elif current_state.goals:
            statement = statement_prompt()

            if statement == EXIT:
                print(red("👋 Bye !"))
                return

            if statement == BACKTRACK:
                backtrack(stack)
                continue

            if (ccl := get_conclusion(current_state, statement)) is not None:
                # statement solves the goal
                new_lean_text = current_state.lean_text + ccl
            else:
                new_lean_text = current_state.lean_text + indent(
                    statement.translate(
                        hyp=f"h{len(current_state.goals[0].hypotheses)}",
                        hyp_list=current_state.goals[0].hypotheses,
                    )
                )

            # getting feedback
            lean_feedback = get_lean_feedback(new_lean_text)

            if lean_feedback == FAIL:
                print(red("🧨 Statement didn't work, try again."))
                continue

            elif lean_feedback == NO_GOALS:
                print(green("🚀 Congratulations, you solved all the goals !"))
                stack.push(State(goals=[], lean_text=new_lean_text))
                continue

            # solved at least one goal
            elif len(current_state.goals) < len(lean_feedback):
                print(
                    green(
                        f"🚀 Congratulations, you solved a goal ! There are {len(lean_feedback)} goals left."
                    )
                )

            # lean_feedback is a list of goals
            stack.push(State(goals=lean_feedback, lean_text=new_lean_text))
            continue


def backtrack(stack: Stack):
    if len(stack) == 1:
        print(red("Cannot backtrack anymore, try 'exit' if you want to quit.\n"))
        return

    print(red("Backtracking...\n"))
    stack.pop()
    new_state: State = stack.peek()
