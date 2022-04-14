import unittest
from natural2lean.math_mode import Equation, Expression


class TestEquation(unittest.TestCase):
    def test_simple_matched(self):
        self.assertEqual(Equation.match("a = b"), Equation("a = b"))
        self.assertEqual(Equation.match("a = b ≤ c"), Equation("a = b ≤ c"))
        self.assertEqual(Equation.match("a = b > c ≥ d"), Equation("a = b > c ≥ d"))

    def test_not_matched(self):
        self.assertIsNone(Equation.match("a b"))
        self.assertIsNone(Equation.match("a*b"))
        self.assertIsNone(Equation.match("(a)"))
        self.assertIsNone(Equation.match("+"))
        self.assertIsNone(Equation.match("1"))

    def test_raises(self):
        self.assertRaises(ValueError, Equation, "a = b ≠ c ≠ d")
        self.assertRaises(ValueError, Equation, "a > b < c = d")
        self.assertRaises(ValueError, Equation, "a ≥ b ≤ c = d")
        self.assertRaises(ValueError, Equation, "a < b = c ≠ d")
        self.assertRaises(ValueError, Equation, "a ≥ b = c ≠ d")

    def test_contents(self):
        self.assertEqual(
            Equation.match("a = b").expressions, [Expression("a"), Expression("b")]
        )
        self.assertEqual(Equation.match("a = b").operators, ["="])
        self.assertEqual(
            Equation.match("a ≤ b < c+1").expressions,
            [Expression("a"), Expression("b"), Expression("c+1")],
        )
        self.assertEqual(Equation.match("a ≤ b < c+1").operators, ["≤", "<"])


if __name__ == "__main__":
    unittest.main()
