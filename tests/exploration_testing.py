from natural2lean import Translator

translator = Translator()

# ------------------------------------------------------------------------------
translator.new(
    "Theorem Square of even number is even: if $m \in \mathbb{N}$ is even, then $m^2$ is even."
)

translator.new(
    "By definition, if $m$ is even, we have a natural number $n$ such that $m = 2n$."
)

translator.new("Therefore we have $m^2 = (2n)^2 = 4n^2 = 2(2n^2)$.")

translator.new("Therefore $m^2$ is even.")
# ------------------------------------------------------------------------------
translator.new("Theorem Square mod 3: If $q$ is a natural not divisible by $3$, then $q^2 \mod 3 = 1$.")

translator.new("Considering the different possibilities of the modulo operation, we have $q \mod 3 \in \{ 0, 1, 2 \}$")

translator.new("For the first case, as $q$ is not divisible by $3$, we have a contradiction for $0$.")

translator.new("For the second case, we have $q \mod 3 = 1$")

translator.new("By definition of the modulo operation, we have $k \in \mathbb{N}$ such that $q = 3k + 1$")

translator.new("By expansion, we have $q^2 = (3k+1)^2 = 9k^2+6k+1 = 3(3k^2 + 2k) + 1$")

translator.new("hence, we have $q^2 \mod 3 = 1$")

translator.new("For the last case, by definition of the modulo operation, we have $k \in \mathbb{N}$ such that $q = 3k + 2$")

translator.new("Following the same expansion, we have $q^2 = (3k+2)^2 = 3(3k^2+4k+1) +1$")

translator.new("Hence, we have $q^2 \mod 3 = 1$ again")
