from natural2lean import Translator
# end-to-end tests can be found in the natural2lean-cli repo at https://github.com/Augustindou/natural2lean-cli

from natural2lean.utils.exceptions import LeanError


translator = Translator()

translator.new(r"Theorem Square of even number is even: if $m \in \mathbb{N}$ is even, then $m^2$ is even.")
translator.new(r"By definition, if $m$ is even, we have a natural number $n$ such that $m = 2n$.")
try:
    translator.new(r"Therefore we have $m^2 = (2n)^3 = 4n^2 = 2(2n^2)$.")
except LeanError as e:
    translator.failed_statement_interpretation()