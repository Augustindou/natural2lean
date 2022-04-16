import unittest
from natural2lean.math_mode.identifier import Identifier
from natural2lean.math_mode.multiple_identifiers import MultipleIdentifiers


class TestIdentifiers(unittest.TestCase):
    def test_simple_matched(self):
        tests = [
            (Identifier.match("a"), Identifier("a")),
            (Identifier.match("hello_world"), Identifier("hello_world")),
            (Identifier.match("x_1"), Identifier("x_1")),
            (Identifier.match("x1"), Identifier("x1")),
        ]

        for input, expected in tests:
            self.assertEqual(input, expected)

    def test_not_matched(self):
        tests = [
            Identifier.match("a b"),
            Identifier.match("a*b"),
            Identifier.match("(a)"),
            Identifier.match("+"),
            Identifier.match("1"),
        ]

        for input in tests:
            self.assertIsNone(input)

    def test_multiple_matched(self):
        tests = [
            (MultipleIdentifiers.match("a"), MultipleIdentifiers("a")),
            (MultipleIdentifiers.match("a, b"), MultipleIdentifiers("a, b")),
            (MultipleIdentifiers.match("a,b,c"), MultipleIdentifiers("a, b, c")),
        ]

        for input, expected in tests:
            self.assertEqual(input, expected)

    def test_multiple_not_matched(self):
        tests = [
            MultipleIdentifiers.match("a + b"),
            MultipleIdentifiers.match("a + b, c + d"),
        ]

        for input in tests:
            self.assertIsNone(input)

    def test_identifier_in_set(self):
        # TODO
        pass


if __name__ == "__main__":
    unittest.main()
