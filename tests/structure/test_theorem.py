import unittest
from natural2lean.structure.theorem import Theorem


class TestTheorem(unittest.TestCase):
    def test_theorem_examples(self):
        th_latex_1 = r"Theorem Square of even number is even: if $m \in \mathbb{N}$ is even, then $m^2$ is even."
        # TODO : If $q$ is a natural 'and' is divisible by $3$ ? would not work because it would separate "q is a natural" from "is divisible by 3", so it should result in "q : Nat" and "divisible 3 3" as the math mode would match the 3 in the second proposition
        th_latex_2 = "Theorem Square mod 3: \n If $q$ is a natural not divisible by $3$, then $q^2 \\mod 3 = 1$.\n\n"
        th_latex_3 = r"Theorem square of q divisible by 3 means q is divisible by 3: If $q$ is a natural number and $q^2$ is divisible by $3$, then $q$ is also divisible by $3$."
        latex_theorems = [th_latex_1, th_latex_2, th_latex_3]

        th_lean_1 = "theorem square_of_even_number_is_even (m : Nat) (h0 : even (m)) : even (m^2) := by\n"
        th_lean_2 = "theorem square_mod_3 (q : Nat) (h0 : ¬ divisible (3) (q)) : q^2 % 3 = 1 := by\n"
        th_lean_3 = "theorem square_of_q_divisible_by_3_means_q_is_divisible_by_3 (q : Nat) (h0 : divisible (3) (q^2)) : divisible (3) (q) := by\n"
        lean_theorems = [th_lean_1, th_lean_2, th_lean_3]

        for latex_theorem, lean_theorem in zip(latex_theorems, lean_theorems):
            res = Theorem.match(latex_theorem).translate()
            self.assertEqual(res, lean_theorem)


if __name__ == "__main__":
    unittest.main()
