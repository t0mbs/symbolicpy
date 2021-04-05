import copy
from Tree import *
from Graph import *

logging.basicConfig(format='%(levelname)s:%(message)s', level=logging.DEBUG)

def main():
    filename = "tests/test_script.py"
    with open(filename) as f:
        contents = f.read()

    t = Tree(contents)

    g = Graph(t)
    g.draw(t.root_state)
    g.render()

if __name__ == '__main__':
    main()
