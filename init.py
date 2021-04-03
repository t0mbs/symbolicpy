import copy
from Tree import *

filename = "tests/test.py"
with open(filename) as f:
    contents = f.read()

t = Tree(ast.parse(contents))
