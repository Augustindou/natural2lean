from natural2lean.structure.theorem import Theorem

if __name__ == "__main__":
    theorem = "Theorem Square mod 3: \n If $q$ is a natural not divisible by $3$, then $q^2 \\mod 3 = 1$.\n\n"

    th = Theorem.match(theorem)
    print(th.translate())
