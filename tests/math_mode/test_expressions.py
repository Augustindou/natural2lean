import unittest
from natural2lean.math_mode import Expression


class TestExpression(unittest.TestCase):
    def test_simple_matched(self):
        tests = [
            (Expression.match(r"1 / 2"), Expression("1/2")),
            (Expression.match(r"a + b"), Expression("a + b")),
            (Expression.match(r"x^2"), Expression("x^2")),
            (Expression.match(r"-a"), Expression("-a")),
        ]

        for input, expected in tests:
            self.assertEqual(input, expected)

    def test_not_matched(self):
        tests = [
            Expression.match(r"12"),
            Expression.match(r"ab"),
            Expression.match(r"a = b"),
            # TODO : correct regex in Expressions to avoid elements conaining relation operators (for now, order is important  for submatching in math_mode.Math.set_contents())
            # Expression.match(r"a = b + 1"),
            # Expression.match(r"a + b + 1 = 2"),
        ]

        for input in tests:
            self.assertIsNone(input)


if __name__ == "__main__":
    unittest.main()
