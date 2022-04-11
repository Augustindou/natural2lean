import unittest  
from math_mode.translate_math import Latex2LeanMath

class TestLatex2LeanMath(unittest.TestCase):
    def test_symbol_replacement(self):
        tests = {
            r"a \mod b": r"a % b",
            r"a \mod 3 + 2": r"a % 3 + 2",
            r"a \cdot b": r"a * b",
            r"a \cdot b + c": r"a * b + c",
            r"\bigg(a + b\bigg)": r"(a + b)",
            r"\left(a + b\right)": r"(a + b)",
            r"\left(a + b\right) \cdot \bigg(c \mod 3\bigg)": r"(a + b) * (c % 3)",
        }
        
        for input, expected in tests.items():
            result = Latex2LeanMath(input).result()
            self.assertEqual(result, expected)
    
    def test_function_replacement(self):  
        # TODO
        pass
        #     r"\sqrt{2}^{1+2}",
        #     r"\frac{\sqrt{2} + 3}{\sqrt{2}}",
        #     r"\frac{1}{2}",
        #     r"\sqrt{2}",
        #     r"e ^ \sqrt{2}",
        #     r"e ^ \frac{2}{3} + \frac{2}{3}",
        #     r"2e",
        #     r"2(e + 1)",
        #     r"2e(e + 1)",
        #     r"e(e + 1)",
        #     r"(e + 3e)(e + 1)",
        #     r"(e + 1)ab",
        # ]
    
    def test_implicit_operations(self):  
        # TODO
        pass
    
    def test_general(self):  
        # TODO
        pass
  
        data = [1, 2, 3]
        result = sum(data)  
        self.assertEqual(result, 6)  
  
if __name__ == '__main__':  
    unittest.main()  
