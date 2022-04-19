import unittest
from natural2lean.propositions.multiple_propositions import MultiplePropositions


class TestSeparatePropostions(unittest.TestCase):
    def test_working_examples(self):
        examples = {
            "$a$ is even and $a^2$ is even": "even (a) ∧ even (a^2)",
            "$a$ is an even natural number, $a^2$ is divisible by $3$ and $b \\in \\mathbb{Z}$": "(a : Nat) ∧ even (a) ∧ divisible 3 (a^2) ∧ (b : Int)",
            "$a, b$ and $c$ are integers and $\\sqrt{a} + b^2 = c^2$": "(a b c : Int) ∧ (((a) ^ (1/2)) + b^2 = c^2)",
        }

        for latex, lean in examples.items():
            res = MultiplePropositions(latex).translate()
            self.assertEqual(res, lean)

    def test_error(self):
        # missing $ $ around the "3"
        self.assertRaises(ValueError, MultiplePropositions, "$a^2$ is divisible by 3")


if __name__ == "__main__":
    unittest.main()
