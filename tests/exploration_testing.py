from natural2lean.structure.theorem import Theorem
from natural2lean.propositions.multiple_propositions import MultiplePropositions

if __name__ == "__main__":
    example = "$a^2$ is divisible by 3"

    object = MultiplePropositions(example)
    print(object.translate())
