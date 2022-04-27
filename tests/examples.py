from natural2lean.math_mode.math import Math
from natural2lean.propositions.implication import Implication
from natural2lean.structure.matching import Matching
from natural2lean.text.theorem import Example, Theorem
from natural2lean.propositions.multiple_propositions import MultiplePropositions
from natural2lean.text.have import Have
from natural2lean.text.such_that import SuchThat
from natural2lean.utils.indentation import indent


def main():
    examples: list[tuple[Matching, str]] = []
    # identifiers
    examples.append((Math, "$x, y$"))
    # identifiers in set
    examples.append((Math, "$x, y \\in \\mathbb{N}$"))
    # identifier in set ({1, 2, 3})
    examples.append((Math, "$x \in \{1, 2, 3\}$"))
    # expression
    examples.append((Math, "$a+\\frac{b}{c+1}$"))
    # equation
    examples.append((Math, "$a \leq b \lt b+1$"))
    # multiple propositions
    examples.append((MultiplePropositions, "$a$ is divisible by $b$ and $\\frac{a}{b} = a^2$"))
    # implication
    examples.append(
        (
            Implication,
            "If $q^2$ is divisible by $3$, then $q$ is also divisible by $3$.",
        )
    )
    # theorem
    examples.append(
        (
            Theorem,
            "Theorem Square mod 3: \nIf $q$ is a natural not divisible by $3$, then $q^2 \\mod 3 = 1$.",
        )
    )
    # example (unnamed theorem)
    examples.append(
        (Example, "If $q$ is a natural not divisible by $3$, then $q^2 \\mod 3 = 1$.")
    )
    # such that
    examples.append((SuchThat, "a natural number $n$ such that $m = 2n$."))
    # have
    examples.append((Have, "Therefore we have $m^2 = (2n)^2 = 4n^2 = 2(2n^2)$"))
    examples.append(
        (Have, "By definition, we have a natural number $n$ such that $m = 2n$.")
    )

    for cls, example in examples:
        print(f"\n----------- {cls.__name__} -----------\n")
        print(f"LaTeX:\n{example}")
        print()
        print(f"Lean:\n{cls.match(example).translate()}")

if __name__ == "__main__":
    main()
