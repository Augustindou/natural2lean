import unittest
from natural2lean.math_mode.expression import Expression


class TestExpression(unittest.TestCase):
    def test_simple_matched(self):
        tests = [
            (Expression.match(r"1 / 2"), Expression("1/2")),
            (Expression.match(r"a + b"), Expression("a + b")),
            (Expression.match(r"x^2"), Expression("x^2")),
            (Expression.match(r"-a"), Expression("-a")),
            (Expression.match(r"12"), Expression("12")),
            (Expression.match(r"ab"), Expression("ab")),
        ]

        for input, expected in tests:
            self.assertEqual(input, expected)

    def test_not_matched(self):
        tests = [
            Expression.match(r"a = b"),
            Expression.match(r"a = b + 1"),
            Expression.match(r"a + b + 1 = 2"),
        ]

        for input in tests:
            self.assertIsNone(input)


if __name__ == "__main__":
    unittest.main()
