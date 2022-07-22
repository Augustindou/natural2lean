class Translatable:
    def translate(self, **kwargs) -> str:
        """Returns the lean translation of the object."""
        raise NotImplementedError()

    def interpretation_feedback(self) -> list[tuple[str, str]]:
        """Returns a list of tuples (`type`, `section`) describing the way the string was processed.

        The type can be one of the following:
        - `"keyword"`: the section of the string is a keyword used to interpret the string (e.g. "theorem", "have")
        - `"parameter"`: the section of the string is a parameter used in the translation (e.g. a theorem name, a math expression)
        - `"ignored"`: the section of the string was ignored (most filling words like "we", "therefore", ...)
        """
        raise NotImplementedError()

    def can_create_new_goals(self) -> bool:
        """Returns whether the object should be allowed to create new goals."""
        return False

    def change_status(self) -> bool:
        """Returns whether the object should change the status (e.g. if doing an induction on a variable)."""
        return False
