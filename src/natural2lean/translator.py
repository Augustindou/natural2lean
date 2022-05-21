import os
import shutil
import platform
from pathlib import Path, PureWindowsPath
from .proof_elements.statement import CCL_POSSIBILITIES, get_statement
from .proof_elements.theorem import get_theorem
from .utils.stack import Stack
from .utils.printing import indent, subscript
from .utils.exceptions import LeanError, TranslationError
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
LEAN_PROJECT = "lean"

LEAN_HEADER = "\n".join(
    [
        "import LeanUtils",
        'def main : IO Unit := IO.println s!"Hello, world!"',
        "open Nat",
    ]
)


windows = platform.system() == "Windows"


class Translator:
    def __init__(self, lean_project_directory: str = None):
        self.stack = Stack()
        self.stack.push(State(goals=[], statements=[], lean_text=LEAN_HEADER))

        # path to project
        if lean_project_directory:
            if windows:
                lean_project_directory = PureWindowsPath(lean_project_directory)
            self.project_directory = Path(lean_project_directory) / LEAN_PROJECT
        else:
            self.project_directory = DEFAULT_PATHS[platform.system()] / LEAN_PROJECT

        # check if project exists
        if not self.project_directory.exists():
            # if exists at the default location, copy the folder
            if (DEFAULT_PATHS[platform.system()] / LEAN_PROJECT).exists():
                shutil.copytree(
                    DEFAULT_PATHS[platform.system()] / LEAN_PROJECT,
                    self.project_directory,
                )
            # otherwise, download the project
            else:
                self.project_directory.mkdir(parents=True)
                os.system(
                    f"git clone {LEAN_PROJECT_GIT_REPO} {self.project_directory}"
                )

        # lake build to make sure lean it will work (this will download Mathlib if it is not already)
        try:
            lean_feedback(LEAN_HEADER, self.project_directory)
        except LeanError:
            raise Exception(
                "The lean header alone should not cause an error, please report this bug."
            )

    def new_theorem(self, string: str) -> State:
        """Adds a new state to the stack, with a new theorem

        Args:
            string (str): the string to be parsed into a theorem

        Returns:
            State: the state after the theorem has been added
        """
        theorem = get_theorem(string)

        old_state: State = self.stack.peek()
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

        self.stack.push(new_state)
        return new_state

    def new_statement(self, string: str) -> State:
        """Adds a new state to the stack, with a new statement

        Args:
            string (str): the string to be parsed into a statement

        Returns:
            State: the state after the statement has been added
        """
        statement = get_statement(string)

        old_state: State = self.stack.peek()
        assert (
            len(old_state.goals) > 0
        ), "Should start a theorem before adding statements"
        
        if (ccl := get_conclusion(old_state, statement, self.project_directory)):
            translation = ccl
        else:
            hyp_count = len(old_state.goals[0].hypotheses)
            hyp_name = f"h{subscript(hyp_count)}"
            translation = statement.translate(hyp_name=hyp_name)
            
        if ccl is None and any([isinstance(statement, poss) for poss in CCL_POSSIBILITIES]):
            raise TranslationError(f"Could not conclude a proof with '{string}', and could not match a non-conclusive statement")

        lean_text = (
            old_state.lean_text
            + "\n\n"
            + indent(translation)
        )

        # lean_feedback(lean_text) should throw an error if lean could not understand the translated theorem
        new_state = State(
            goals=lean_feedback(lean_text, self.project_directory),
            statements=old_state.statements + [statement],
            lean_text=lean_text,
        )

        self.stack.push(new_state)
        return new_state

    def backtrack(self) -> None:
        self.stack.pop()

    def lean_text(self) -> str:
        return self.stack.peek().lean_text
