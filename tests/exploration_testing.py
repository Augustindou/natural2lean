from natural2lean import Translator
from natural2lean.lean_interaction.lean_feedback import raw_feedback
from pathlib import Path

translator = Translator()

translator.new(r"if $n$ is a natural number and $n+1=4$, then $n = 3$")
translator.new(r"we will use contradiction")