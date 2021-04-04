import ast
import logging
from State import *
from Property import *
from SymbolicVariable import *
from Z3Solver import *
from BinarySolver import *

logging.basicConfig(format='%(levelname)s:%(message)s', level=logging.DEBUG)

class Tree:
    """The Computation Tree, which walks down the Python Abstract Syntax Tree (AST)

    Parameters
    ----------
    code : string
        A string of python to be symbolically executed

    Attributes
    ----------
    root : State
        The root State, all future states are an r or l-node
    state : State
        The current State
    z3 : Z3Solver
        The handler class for Z3 SMT solving

    """
    def __init__(self, code: str):
        self.root = State()
        self.state = self.root

        self.z3 = Z3Solver()
        self.walk(ast.parse(code))


    def walk(self, tree: Any):
        """Walking down the AST at depth 1

        Parameters
        ----------
        tree : Any
            The AST being walked down

        """

        for node in ast.iter_child_nodes(tree):
            t = type(node)
            logging.info("Iterating over AST node of type %s" % t)

            # Is a variable assignment (e.g. x = y)
            if t is ast.Assign:
                # Can have multiple variables left of the operator (e.g. x, y, z = 2)
                for target in node.targets:
                    self.assign(node.value, target.id)

            # Is an augmented variable assignment (e.g. x += y)
            elif t is ast.AugAssign:
                self.augassign(node)

            # Is an IF statement
            elif t is ast.If:
                self.conditional(node)

            # Is everything else
            else:
                logging.info("Ignored AST node")

    def assign(self, value: Any, name: str):
        """Handle assignment operations

        Parameters
        ----------
        value : Any
            The value will be the initial state of the symbolic variable
            e.g. name = y, value = x => y__0 == x__0
        name : str
            The name of the concrete variable

        """

        # Assigning a variable's value to another variable
        if isinstance(value, ast.Name):
            v = self.state.getActiveVariable(value.id)
            self.state.createSymbolicVariable(v, name)
        # Assigning a constant value to the variable (simplest)
        elif isinstance(value, ast.Constant):
            self.state.createSymbolicVariable(value.value, name)
        # Go recursive if there is a binary operation
        elif isinstance(value, ast.BinOp):
            # Translate binary operation to properties, or simplified constant
            solver = BinarySolver(self.state)
            p = solver.solve(value.left, value.op, value.right)
            if isinstance(p, ast.Constant):
                self.state.createSymbolicVariable(p.value, name)
            else:
                self.state.createSymbolicVariable(p, name)
        else:
            logging.error("The type %s of the assignment value for variable is unrecognized" % type(node.value))

    def augassign(self, node: ast.AugAssign):
        """Handing a augmented assignment operation

        Parameters
        ----------
        node : ast.AugAssign
            The AST AugAssign node containing the variable and its state change

        """
        solver = BinarySolver(self.state)
        # The l-node will never be a Constant, therefore neither will the return
        p = solver.solve(node.target, node.op, node.value)
        self.state.createSymbolicVariable(p, node.target.id)

    def conditional(self, node: ast.If):
        """Handling a conditional operation

        Parameters
        ----------
        node : ast.If
            The relevant ast.If node

        """
        # Create new logical properties for relevant variables in relevant state
        test = node.test

        # 1. Register new conditional property
        true_state = copy.deepcopy(self.state)

        true_state.addConditionalProperties(test.left, test.ops, test.comparators)

        sat = self.z3.solve(true_state.properties)

        # Does the true state solve?
        if sat:
            logging.info("Z3 SAT")
            self.state.right = true_state
            # TODO: add the inverse property for false node if there's an else
            self.state.left = copy.deepcopy(self.state)

            self.state = true_state
            self.walk(node)

        # TODO: Merge back

        # Dead
        else:
            logging.info("Z3 UNSAT")
            true_state.sat = False
            pass
