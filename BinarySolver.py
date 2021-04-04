import ast
from Property import *
from State import *
from typing import Any

class BinarySolver:
    """Binary solver is used to solve AST Binary Operations, which can be nested

    Parameters
    ----------
    state : State
        Current state file, used to get symbolic variable names.

    Attributes
    ----------
    state

    """
    def __init__(self, state: State):
        self.state = state

    def solve(self, l: Any, op: Any, r: Any) -> Any:
        """Solve an AST Binary Operation

        Parameters
        ----------
        l : Any
            Left node can be a variable of type ast.Name, a constant of type
            ast.Constant, a nested Binary Operation of type ast.BinOp or a
            Property returned recursively
        op : Any
            The relevant ast binary operator class (e.g. ast.Add)
        r : Any
            Right node can have the same values types as l

        Returns
        -------
        Property
            Return a recursive Property representing the Binary Operation OR
            a simplified Constant if all nodes are Constants

        """

        # Node values default to the symbolic variable names, if relevant
        if isinstance(l, ast.Name):
            l_node = self.state.getActiveVariable(l.id)
        if isinstance(r, ast.Name):
            r_node = self.state.getActiveVariable(r.id)

        # Solve any nested binary operations recursively
        if isinstance(l, ast.BinOp):
            l = self.solve(l.left, l.op, l.right)
        if isinstance(r, ast.BinOp):
            r = self.solve(r.left, r.op, r.right)

        # Create temporary variables to represent properties
        if isinstance(l, Property):
            l_node = self.state.createSymbolicVariable(l).name
        if isinstance(r, Property):
            r_node = self.state.createSymbolicVariable(r).name

        # When both are constants, simplify to one constant
        if isinstance(l, ast.Constant) and isinstance(r, ast.Constant):
            p = Property(l.value, op, r.value)
            return ast.Constant(eval("%s %s %s" % (l.value, p.op, r.value)))

        # Set property node to constant value if relevant
        if isinstance(r, ast.Constant):
            r_node = r.value
        if isinstance(l, ast.Constant):
            l_node = l.value

        return Property(l_node, op, r_node)
