import unittest
from natural2lean.math_mode import Math, Expression, Identifier


class TestMath(unittest.TestCase):
    def test_simple_matched(self):
        # identifiers
        self.assertEqual(Math.match("$x$"), Math("x"))
        self.assertEqual(Math.match("$x,y $"), Math("x, y"))
        # expressions
        self.assertEqual(Math.match("$a+b$"), Math("a+b"))
        self.assertEqual(Math.match("$\\frac{1}{2}$"), Math("((1)/(2))"))
        self.assertEqual(
            Math.match("$\\frac{1}{2}+\\sqrt{1}$"), Math("((1)/(2))+((1)^(1/2))")
        )
        # equations
        self.assertEqual(Math.match("$a = b$"), Math("a = b"))
        self.assertEqual(Math.match("$a+b ≤ c+1$"), Math("a+b ≤ c+1"))
        self.assertEqual(Math.match("$a = b > c ≥ d$"), Math("a = b > c ≥ d"))

    def test_contents(self):
        # identifiers
        self.assertEqual(Math.match("$x$").content.identifiers, [Identifier("x")])
        self.assertEqual(
            Math.match("$x,y $").content.identifiers, [Identifier("x"), Identifier("y")]
        )
        # expressions
        self.assertEqual(Math.match("$a+b$").content, Expression("a+b"))
        self.assertEqual(Math.match("$\\frac{1}{2}$").content, Expression("((1)/(2))"))
        # equations
        self.assertEqual(
            Math.match("$a = b$").content.expressions,
            [Expression("a"), Expression("b")],
        )
        self.assertEqual(Math.match("$a = b$").content.operators, ["="])
        self.assertEqual(
            Math.match("$a = b > c ≥ d$").content.expressions,
            [Expression("a"), Expression("b"), Expression("c"), Expression("d")],
        )
        self.assertEqual(
            Math.match("$a = b > c ≥ d$").content.operators, ["=", ">", "≥"]
        )


if __name__ == "__main__":
    unittest.main()
