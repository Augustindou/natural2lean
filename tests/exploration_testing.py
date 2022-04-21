from natural2lean.math_mode.math import Math
from natural2lean.propositions.implication import Implication
from natural2lean.structure.matching import Matching
from natural2lean.structure.theorem import Theorem
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
    # expression
    examples.append((Math, "$a+\\frac{b}{c+1}$"))
    # equation
    examples.append((Math, "$a \leq b \lt b+1$"))
    # implication
    examples.append((Implication, "If $q^2$ is divisible by $3$, then $q$ is also divisible by $3$."))
    # theorem
    examples.append((Theorem, "Theorem Square mod 3: \nIf $q$ is a natural not divisible by $3$, then $q^2 \\mod 3 = 1$."))
    # have
    examples.append((Have, "Therefore we have $m^2 = (2n)^2 = 4n^2 = 2(2n^2)$"))
    # such that
    examples.append((SuchThat, "we have a natural number $n$ such that $m = 2n$."))
    
    for cls, example in examples:
        print(f"\n----------- {cls.__name__} -----------\n")
        print(f"LaTeX:\n{indent(example, 2)}")
        print()
        print(f"Lean:\n{indent(cls.match(example).translate(), 2)}")

    # multiple props
    # print(f"\n----------- {MultiplePropositions.__name__} -----------\n")
    # print(f"LaTeX:\n{indent('$a, b$ and $c$ are integers and $\\sqrt{a} + b^2 = c^2$', 2)}")
    # print()
    # print(MultiplePropositions("$a, b$ and $c$ are integers and $\\sqrt{a} + b^2 = c^2$"))

if __name__ == "__main__":
    main()