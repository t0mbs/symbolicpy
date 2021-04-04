import unittest
import ast
from Tree import *

class TestBinaryOperators(unittest.TestCase):
    def test_addition(self):
        self.ManageTest([
            ["x=1",     "x__0 == 1"],
            ["x+=1",    "x__1 == x__0 + 1"],
            ["x=x+100", "x__2 == x__1 + 100"]
        ])

    def test_subtraction(self):
        self.ManageTest([
            ["y=99",    "y__0 == 99"],
            ["y-=100",  "y__1 == y__0 - 100"],
            ["x=10",    "x__0 == 10"],
            ["x-=y",    "x__1 == x__0 - y__1"]
        ])

    def test_multiplication(self):
        self.ManageTest([
            ["x=0",     "x__0 == 0"],
            ["x*=0",    "x__1 == x__0 * 0"],
            ["y=x",     "y__0 == x__1"],
            ["y*=x",    "y__1 == y__0 * x__1"]
        ])

    def test_division(self):
        self.ManageTest([
            ["x=0",     "x__0 == 0"],
            ["x=x/0",    "x__1 == x__0 / 0"],
            ["y=100",   "y__0 == 100"],
            ["y/=x",    "y__1 == y__0 / x__1"],
        ])

    def test_modulo(self):
        self.ManageTest([
            ["x=50",     "x__0 == 50"],
            ["x%=5",     "x__1 == x__0 % 5"],
            ["y=10",     "y__0 == 10"],
            ["y=x%3",    "y__1 == x__1 % 3"]
        ])

    def test_pow(self):
        self.ManageTest([
            ["x=9",     "x__0 == 9"],
            ["x**=1",    "x__1 == x__0 ** 1"],
            ["y=10",     "y__0 == 10"],
            ["y=x**3",   "y__1 == x__1 ** 3"]
        ])


    def ManageTest(self, operations, sat = True):
        self.ResetTest()
        for o in operations:
            self.AddTest(o[0], o[1])
        self.ExecuteTest(sat)

    def ExecuteTest(self, sat = True):
        string = ';'.join(self.ops)
        t = Tree(string)
        props = t.root_state.properties
        self.assertEqual(len(props), len(self.ops))

        # Test properties
        for i in range(len(self.ops)):
            self.assertEqual(str(props[i]), self.props[i])

        # Test z3 SAT
        self.assertEqual(t.z3.solve(props), sat)


    def ResetTest(self):
        self.ops = []
        self.props = []

    def AddTest(self, op, prop):
        self.ops.append(op)
        self.props.append(prop)

if __name__ == '__main__':
    unittest.main()
