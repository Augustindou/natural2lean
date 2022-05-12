from dataclasses import dataclass
from .conclude_proof import get_conclusion
from .lean_feedback import BACKTRACK, EXIT, FAIL, NO_GOALS, LeanBlock, get_lean_feedback
from .user_input import theorem_prompt, statement_prompt
from ..utils.stack import Stack
from ..utils.indentation import indent
from ..utils.pretty_printing import nth, string_differences, to_indices

red = lambda s: "\u001b[31m" + s + "\u001b[0m"
green = lambda s: "\u001b[32m" + s + "\u001b[0m"
cyan = lambda s: "\u001b[36m" + s + "\u001b[0m"
underline = lambda s: "\u001b[4m" + s + "\u001b[0m"

WELCOME_MESSAGE = (
    f"Welcome to the Natural2Lean interactive mode ! You can enter line-by-line proofs for theorems and get feedback on what you have already proven (hypotheses) and what you need to prove (goal). If your input could not be translated or did not work, you will be asked to {red('try again')}. In this case, try to simplify your statement !\n"
    f"\n"
    f"Keywords :\n"
    f"    If you made a mistake, you can use the {cyan('backtrack')} (or {cyan('back')}) keyword to go one step back.\n"
    f"    If you want to exit, you can use the {cyan('exit')} or {cyan('quit')} keywords.\n"
    f"\n"
    f"You can visit {underline('github.com/Augustindou/natural2lean/blob/main/README.md#how-the-system-works')} to have an overview on what the system will recognize."
)

LEAN_HEADER = (
    "import LeanUtils\n"
    'def main : IO Unit := IO.println s!"Hello, world!"\n'
    "open Nat"
)


@dataclass
class State:
    goals: list[LeanBlock]
    lean_text: str

    def __str__(self):
        if len(self.goals) == 0:
            return ""

        result = f"Current goal: {indent(str(self.goals[0]))[2:]}"
        for i, goal in enumerate(self.goals[1:]):
            result += f"\n{nth(i+2)} goal: {indent(str(goal))}"

        return result


def interactive_mode():
    # initialize stack
    stack = Stack()
    stack.push(State(goals=[], lean_text=LEAN_HEADER))

    # print welcome message with info
    print(WELCOME_MESSAGE)

    # main loop
    while True:
        current_state: State = stack.peek()
        print(string_differences(str(stack.peek(1)), str(current_state)))
        # get theorem if no goals
        if not current_state.goals:
            theorem = theorem_prompt()

            if theorem == EXIT:
                print(cyan("👋 Bye !\n"))
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
                print(cyan("👋 Bye !\n"))
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
                        hyp=f"h{to_indices(len(current_state.goals[0].hypotheses))}",
                        hyp_list=current_state.goals[0].hypotheses,
                    )
                )

            # getting feedback
            lean_feedback = get_lean_feedback(new_lean_text)

            if lean_feedback == FAIL:
                print(
                    red(
                        "🧨 The system could not understand your statement, try again.\n"
                    )
                )
                continue

            elif lean_feedback == NO_GOALS:
                print(green("🚀 Congratulations, you solved all the goals !"))
                stack.push(State(goals=[], lean_text=new_lean_text))
                continue

            # solved at least one goal
            elif len(current_state.goals) > len(lean_feedback):
                plural = len(lean_feedback) > 1
                n_goals = ("are" if plural else "is") + f" {len(lean_feedback)} goal" + ('s' if plural else '')
                print(
                    green(
                        f"🚀 Congratulations, you solved a goal ! There {n_goals} left.\n"
                    )
                )

            # created a new goal
            elif len(current_state.goals) < len(lean_feedback) and not statement.can_create_new_goals():
                print(
                    red(
                        "🧨 The system could not understand your statement, try again.\n"
                    )
                )
                continue

            # lean_feedback is a list of goals
            stack.push(State(goals=lean_feedback, lean_text=new_lean_text))
            continue


def backtrack(stack: Stack):
    if len(stack) == 1:
        print(red("🧨 Cannot backtrack anymore, try 'exit' if you want to quit."))
        return

    print(cyan("⏪ Backtracking...\n"))
    stack.pop()
    new_state: State = stack.peek()
