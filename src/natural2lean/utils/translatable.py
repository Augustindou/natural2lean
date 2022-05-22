class Translatable:
    def translate(self, **kwargs) -> str:
        """Returns the lean translation of the object."""
        raise NotImplementedError()
    
    def can_create_new_goals(self) -> bool:
        """Returns whether the object should be allowed to create new goals."""
        return False
