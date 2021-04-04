import copy
from Tree import *

def main():
    filename = "tests/basic_conditionals.py"
    with open(filename) as f:
        contents = f.read()

    t = Tree(contents)

if __name__ == '__main__':
    main()
