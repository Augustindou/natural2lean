import unittest
from natural2lean.utils import translate_latex_math


class TestTranslateLatexMath(unittest.TestCase):
    def test_symbol_replacement(self):
        tests = {
            r"a \mod b": r"a % b",
            r"a \mod 3 + 2": r"a % 3 + 2",
            r"a \cdot b": r"a * b",
            r"a \cdot b + c": r"a * b + c",
            r"\bigg(a + b\bigg)": r"(a + b)",
            r"\left(a + b\right)": r"(a + b)",
            r"\left(a + b\right) \cdot \bigg(c \mod 3\bigg)": r"(a + b) * (c % 3)",
            r"a \in \mathbb{N}": r"a ∈ ℕ",
            r"a \in \mathbb{Z}": r"a ∈ ℤ",
            r"a \in \mathbb{R}": r"a ∈ ℝ",
        }

        for input, expected in tests.items():
            result = translate_latex_math(input)
            self.assertEqual(result.replace(" ", ""), expected.replace(" ", ""))

    def test_function_replacement(self):
        tests = {
            r"\frac{a}{b}": r"((a) / (b))",
            r"\frac{a}{b + c}": r"((a) / (b + c))",
            r"\sqrt{a}": r"((a)^(1 / 2))",
            r"\sqrt{a + b}": r"((a + b)^(1 / 2))",
            r"e^{a}": r"e ^ (a)",
            r"e^{3+2}": r"e ^ (3 + 2)",
            r"\frac{\sqrt{a}}{b+2}^{c+1}": r"((((a)^(1/2))) / (b + 2)) ^ (c + 1)",
            r"\sqrt{\frac{a}{b}}": r"((((a) / (b)))^(1 / 2))",
            r"x_1": r"x_1",
            r"x_{12}": r"x_12",
        }
        for input, expected in tests.items():
            result = translate_latex_math(input)
            self.assertEqual(result.replace(" ", ""), expected.replace(" ", ""))

    def test_implicit_operations(self):
        tests = {
            r"2a": r"2 * a",
            r"2(x + y)": r"2 * (x + y)",
            r"(x + y)2": r"(x + y) * 2",
            r"2x2": r"2 * x2",
            r"(x + y)(z + w)": r"(x + y) * (z + w)",
            r"(x + y)2(z + w)": r"(x + y) * 2 * (z + w)",
            r"2(x + y)2(z + w)": r"2 * (x + y) * 2 * (z + w)",
            r"12": r"12",
            # case for 2 a b -> 2 * a * b not considered since LaTeX would interpret this the same as 2ab
            r"2 a b": r"2 * a b",
        }
        for input, expected in tests.items():
            result = translate_latex_math(input)
            self.assertEqual(result.replace(" ", ""), expected.replace(" ", ""))

    def test_general(self):
        tests = {
            r"2\frac{a}{b}": r"2 * ((a) / (b))",
            r"a, b \in \{1, 2, 3\}": r"a, b ∈ __SET__[1, 2, 3]",
        }
        for input, expected in tests.items():
            result = translate_latex_math(input)
            self.assertEqual(result.replace(" ", ""), expected.replace(" ", ""))


if __name__ == "__main__":
    unittest.main()
