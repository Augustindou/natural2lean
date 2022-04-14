import unittest
from natural2lean.utils import unfold
from natural2lean.math_mode import Equation, MultipleIdentifiers


class TestUnfolding(unittest.TestCase):
    def test_equation(self):
        pattern = Equation.pattern

        tests = {
            "a * b = 2 + c": (["a * b", "2 + c"], ["="]),
            "a = b = c = d": (["a", "b", "c", "d"], ["=", "=", "="]),
            "a = b < c ≤ d": (["a", "b", "c", "d"], ["=", "<", "≤"]),
            "(a+b+c) = (a*b*c)": (["(a+b+c)", "(a*b*c)"], ["="]),
        }

        for input, (expected_elements, expected_separators) in tests.items():
            elements, separators = unfold(pattern, input)
            self.assertEqual(elements, expected_elements)
            self.assertEqual(separators, expected_separators)

    def test_identifiers(self):
        pattern = MultipleIdentifiers.pattern

        tests = {
            "a, b": (["a", "b"], [","]),
            "a, b, c": (["a", "b", "c"], [",", ","]),
            "hello, world": (["hello", "world"], [","]),
            "x_1 , x_2 , x_3": (["x_1", "x_2", "x_3"], [",", ","]),
            "a": (["a"], []),
            "x_1": (["x_1"], []),
        }

        for input, (expected_elements, expected_separators) in tests.items():
            elements, separators = unfold(pattern, input)
            self.assertEqual(elements, expected_elements)
            self.assertEqual(separators, expected_separators)


if __name__ == "__main__":
    unittest.main()
