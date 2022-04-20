from natural2lean.structure.theorem import Theorem
from natural2lean.propositions.multiple_propositions import MultiplePropositions
from natural2lean.text.have import Have

if __name__ == "__main__":
    example = r"Therefore we have $m^2 = (2n)^2 = 4n^2 = 2(2n^2)$"

    object = Have(example)
    print(object.translate())
