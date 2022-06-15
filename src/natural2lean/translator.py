import os
import shutil
import platform
from pathlib import Path, PureWindowsPath
from .proof_elements.statement import CCL_POSSIBILITIES, get_statement
from .proof_elements.theorem import get_theorem, NamedTheorem
from .utils.text import indent, subscript
from .utils.exceptions import LeanError, NoConclusion, TranslationError
from .lean_interaction.conclude_proof import get_conclusion
from .lean_interaction.lean_feedback import State, lean_feedback

DEFAULT_PATHS = {
    "Darwin": Path.home() / Path(".natural2lean"),
    "Linux": Path.home() / Path(".natural2lean"),
    "Windows": Path.home() / Path("AppData/Roaming/.natural2lean"),
}

LEAN_PROJECT_GIT_REPO = (
    "https://github.com/Augustindou/natural2lean-lean-project-template.git"
)
GIT_LOCATION = ".git"

LEAN_HEADER = "\n".join(
    [
        "import LeanUtils",
        'def main : IO Unit := IO.println s!"Hello, world!"',
        "open Nat",
    ]
)


windows = platform.system() == "Windows"


class Translator:
    """An object managing a stack of theorems and statements that form proofs."""

    def __init__(self, lean_project_directory: str = None):
        self.stack: list[State] = [
            State(goals=[], statements=[], lean_text=LEAN_HEADER)
        ]
        self.theorems: list[tuple[str, str]] = []

        try:
            default_path = DEFAULT_PATHS[platform.system()]
        except KeyError:
            raise Exception(
                f"Unsupported platform: `{platform.system()}`, please report this bug."
            )

        # path to project
        if lean_project_directory:
            if windows:
                lean_project_directory = PureWindowsPath(lean_project_directory)
            self.project_directory = Path(lean_project_directory)
        else:
            self.project_directory = default_path

        # check if project exists
        if not self.project_directory.exists():
            # if exists at the default location, copy the folder
            if default_path.exists():
                shutil.copytree(
                    default_path,
                    self.project_directory,
                )
            # otherwise, download the project
            else:
                self.project_directory.mkdir(parents=True)
                print("Downloading lean project template...\n")
                os.system(f"git clone {LEAN_PROJECT_GIT_REPO} {self.project_directory}")
                print()

        # lake build to make sure lean it will work (this will download Mathlib if it is not already)
        try:
            lean_feedback(LEAN_HEADER, self.project_directory)
        except LeanError:
            raise Exception(
                "The lean header alone should not cause an error, please report this bug."
            )

    def new(self, string: str) -> State:
        """Adds a new state to the stack, this function will call new_theorem or new_statement depending on whether the last state has goals to solve or not.

        Args:
            string (str): the string to be parsed

        Returns:
            State: the state after the theorem or statement has been added

        Raises:
            AssertionError: if the last state still has a goal to be solved.
            TranslationError: if the string could not be parsed into a theorem.
            LeanError: if the translation by the system could not be understood by lean.
        """
        old_state: State = self.state()
        if len(old_state.goals) == 0:
            return self.new_theorem(string)
        else:
            return self.new_statement(string)

    def new_theorem(self, string: str) -> State:
        """Adds a new state to the stack, with a new theorem. This will create goals to solve, and these goals will be part of the returned state.

        Args:
            string (str): the string to be parsed into a theorem

        Returns:
            State: the state after the theorem has been added

        Raises:
            AssertionError: if the last state still has a goal to be solved.
            TranslationError: if the string could not be parsed into a theorem.
            LeanError: if the translation by the system could not be understood by lean.
        """
        theorem = get_theorem(string)

        # add theorem to list
        if isinstance(theorem, NamedTheorem):
            self.theorems.append((theorem.latex_name, theorem.lean_name))

        old_state: State = self.state()
        assert (
            len(old_state.goals) == 0
        ), "Should close goals before proving new theorem"

        lean_text = old_state.lean_text + "\n\n" + theorem.translate()

        # lean_feedback(lean_text) should throw an error if lean could not understand the translated theorem
        new_state = State(
            goals=lean_feedback(lean_text, self.project_directory),
            statements=old_state.statements + [theorem],
            lean_text=lean_text,
        )

        self.stack.append(new_state)
        return new_state

    def new_statement(self, string: str) -> State:
        """Adds a new state to the stack, with a new statement. The stack should have at least one goal. This will add hypotheses to the goal, these hypotheses can be retrieved from the returned state.

        Args:
            string (str): the string to be parsed into a statement

        Returns:
            State: the state after the statement has been added

        Raises:
            AssertionError: if the last state doesn't have any goal to be solved.
            TranslationError: if the string could not be parsed into a theorem.
            LeanError: if the translation by the system could not be understood by lean.
        """
        statement = get_statement(string, proven_theorems=self.theorems[:-1])

        old_state: State = self.state()
        assert (
            len(old_state.goals) > 0
        ), "Should start a theorem before adding statements"

        try:
            lean_fb, translation = get_conclusion(
                old_state, statement, self.project_directory
            )
        except NoConclusion:
            if any(isinstance(statement, poss) for poss in CCL_POSSIBILITIES):
                raise NoConclusion(
                    f"Could not match a non-conclusive statement, nor conclude a proof with '{string}'.\n"
                )

            hyp_name = f"h{subscript(len(old_state.goals[0].hypotheses))}"
            if old_state.goals[0].hypotheses:
                last_hyp = old_state.goals[0].hypotheses[-1][0]
            else:
                last_hyp = None
            translation = statement.translate(
                hyp_name=hyp_name,
                last_hyp=last_hyp,
            )

            lean_fb = lean_feedback(
                old_state.lean_text + "\n\n" + indent(translation),
                self.project_directory,
            )

        lean_text = old_state.lean_text + "\n\n" + indent(translation)

        # lean_feedback(lean_text) should throw an error if lean could not understand the translated theorem
        new_state = State(
            goals=lean_fb,
            statements=old_state.statements + [statement],
            lean_text=lean_text,
        )

        if (
            len(new_state.goals) > len(old_state.goals)
            and not statement.can_create_new_goals()
        ):
            raise LeanError(
                "Statement created a new goal, but this type of statement is not allowed to.\n"
            )

        self.stack.append(new_state)
        return new_state

    def backtrack(self) -> State:
        """Removes the last input given to the Translator, hence, the last state of the stack. If no input had been given earlier, this function will return None.

        Returns:
            State: the state after the last input has been removed.
        """
        if len(self.stack) == 1:
            return None

        # remove last state
        old_state = self.stack.pop()

        # remove theorem if it was popped
        if isinstance(old_state.statements[-1], NamedTheorem):
            self.theorems.pop()

        return self.state()

    def state(self) -> State:
        """Returns the current state of the Translator.

        Returns:
            State: the current state of the Translator.
        """
        return self.stack[-1]
