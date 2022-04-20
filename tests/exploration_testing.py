from natural2lean.structure.theorem import Theorem
from natural2lean.propositions.multiple_propositions import MultiplePropositions

if __name__ == "__main__":
    example = r"Theorem square of q divisible by 3 means q is divisible by 3: If $q$ is a natural number and $q^2$ is divisible by $3$, then $q$ is also divisible by $3$."

    object = Theorem(example)
    print(object.translate())
