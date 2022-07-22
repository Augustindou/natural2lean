import os
import shutil
import platform
from pathlib import Path, PureWindowsPath

from natural2lean.utils.translatable import Translatable
from .proof_elements.theorem import get_theorem
from .proof_elements.theorem.theorem import Theorem
from .proof_elements.statement import CCL_POSSIBILITIES, get_statement
from .proof_elements.statement.statement import Statement
from .utils.text import indent, subscript
from .utils.exceptions import LeanError, NoConclusion
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
            State(goals=[], last_statement=None, lean_text=LEAN_HEADER)
        ]
        # containing latex name, lean name, number of arguments
        self.theorems: list[tuple[str, str, int]] = []
        # position in proof (for now, only inductions)
        self.proof_status: list[Statement] = []
        # last statement that failed to be translated
        self.last_failed_statement: Translatable = None

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
            lean_feedback(LEAN_HEADER, None, self.project_directory)
        except LeanError:
            raise Exception(
                "The lean header alone should not cause an error, please check that lean4 is installed on your system, and report this bug if it is."
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
        theorem = get_theorem(string, i=len(self.theorems))

        self.proof_status = []

        old_state: State = self.state()
        assert (
            len(old_state.goals) == 0
        ), "Should close goals before proving new theorem"

        lean_text = old_state.lean_text + "\n\n" + theorem.translate()

        # lean_feedback(lean_text) should throw an error if lean could not understand the translated theorem
        try:
            new_state = State(
                goals=lean_feedback(lean_text, theorem, self.project_directory),
                last_statement=theorem,
                lean_text=lean_text,
            )
        except LeanError as e:
            self.last_failed_statement = theorem
            raise e

        # add theorem to list
        if isinstance(theorem, Theorem):
            self.theorems.append(
                (theorem.latex_name, theorem.lean_name, theorem.n_args)
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
        statement = get_statement(
            string, proven_theorems=self.theorems, proof_status=self.proof_status
        )

        if statement.change_status():
            self.proof_status.append(statement)

        old_state: State = self.state()
        assert (
            len(old_state.goals) > 0
        ), "Should start a theorem before adding statements"

        try:
            lean_fb, translation = get_conclusion(
                state=old_state,
                goals=self._all_current_goals(),
                statement=statement,
                project_directory=self.project_directory,
            )
        except NoConclusion:
            if any(isinstance(statement, poss) for poss in CCL_POSSIBILITIES):
                self.last_failed_statement = statement
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

            try:
                lean_fb = lean_feedback(
                    input=old_state.lean_text + "\n\n" + indent(translation),
                    statement=statement,
                    project_directory=self.project_directory,
                )
            except LeanError as e:
                self.last_failed_statement = statement
                raise e

        lean_text = old_state.lean_text + "\n\n" + indent(translation)

        # lean_feedback(lean_text) should have thrown an error if lean could not understand the translated theorem
        new_state = State(
            goals=lean_fb,
            last_statement=statement,
            lean_text=lean_text,
        )

        if (
            len(new_state.goals) > len(old_state.goals)
            and not statement.can_create_new_goals()
        ):
            self.last_failed_statement = statement
            raise LeanError("Lean detected an error in your statement.\n")

        self.stack.append(new_state)
        return new_state

    def interpretation_feedback(self) -> list[tuple[str, str]]:
        """Returns a list of tuples (`type`, `section`) describing the way the last input was processed.

        The type can be one of the following:
        - `"keyword"`: the `section` of the string is a keyword used to interpret the string (e.g. "theorem", "have")
        - `"parameter"`: the `section` of the string is a parameter used in the translation (e.g. a theorem name, a math expression)
        - `"ignored"`: the `section` of the string was ignored (most filling words like "we", "therefore", ...)
        """
        if self._is_bottom_state():
            return None
        return self.stack[-1].last_statement.interpretation_feedback()

    def failed_statement_interpretation(self) -> list[tuple[str, str]]:
        if self.last_failed_statement is None:
            return None
        return self.last_failed_statement.interpretation_feedback()

    def backtrack(self) -> State:
        """Removes the last input given to the Translator, hence, the last state of the stack. If no input had been given earlier, this function will return None.

        Returns:
            State: the state after the last input has been removed.
        """
        if self._is_bottom_state():
            return None

        # remove last state
        old_state = self.stack.pop()

        # remove theorem if it was popped
        if isinstance(old_state.last_statement, Theorem):
            self.theorems.pop()

        return self.state()

    def state(self) -> State:
        """Returns the current state of the Translator.

        Returns:
            State: the current state of the Translator.
        """
        return self.stack[-1]

    def _all_current_goals(self) -> set[str]:
        current_goals = set()
        for state in self.stack[::-1]:
            # stop when exiting the current proof
            if not state.goals:
                break
            # add each goal
            current_goals.add(state.goals[0].goal)

        return current_goals

    def _is_bottom_state(self) -> bool:
        return len(self.stack) == 1
