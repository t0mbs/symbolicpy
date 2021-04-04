import graphviz
import sympy
import textwrap
from Tree import *

class Graph:
    def __init__(self, t: Tree):
        self.tree = t
        self.dot = graphviz.Digraph(comment='Computation Tree')
        self.dot.attr(fontname="Courier")

    def draw(self, state):
        # 1. Get root state
        if state.sat:
            c="grey"
        else:
            c="firebrick1"
        self.dot.node(state.name, self.generateLabel(state), shape="rectangle", color=c, margin="0.2", fontname="Courier")
        if state.left is not None:
            self.draw(state.left)
            self.dot.edge(state.name, state.left.name)
        if state.right is not None:
            r = self.draw(state.right)
            self.dot.edge(state.name, state.right.name)

    def render(self):
        self.dot.render('graph-output/graph.gv', view=True)

    def generateLabel(self, state):
        label = "%s\n\n" % state.name

        # Variables
        label += "Variables: %s\n\n" % ",".join(state.variables)
        # Properties
        p_str = []
        for p in state.properties:
            p_str.append(str(p))

        formula = " and ".join(p_str)

        # Simplify formula
        if formula == '':
            label += "No properties"
        else:
            label += "Formula: %s" % textwrap.fill(formula, 64)
        return label
