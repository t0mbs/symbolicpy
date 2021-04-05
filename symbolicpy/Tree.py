import ast
import logging
from State import *
from Property import *
from SymbolicVariable import *
from Z3Solver import *
from BinarySolver import *


class Tree:
    """The Computation Tree, which walks down the Python Abstract Syntax Tree (AST)

    Parameters
    ----------
    code : string
        A string of python to be symbolically executed

    Attributes
    ----------
    ast: ast.Module
        The full AST, whose nodes are then referenced by symbolic states
    root : State
        The root state, all future states are an r or l-node
    state : State
        The active symbolic state
    state_queue : List[State]
        The queue of inactive, but satisfiable symbolic states
    z3 : Z3Solver
        The handler class for Z3 SMT solving

    """
    def __init__(self, code: str):
        # Root symbolic state
        self.root_state = State()

        # The Abstract Symbolic Tree
        self.root_ast = list(ast.iter_child_nodes(ast.parse(code)))
        # If string is a function definition
        if isinstance(self.root_ast[0], ast.FunctionDef):
            # Initiate "empty" symbolic variables
            for arg in self.root_ast[0].args.args:
                self.root_state.createSymbolicVariable(arg.arg)
            self.root_ast = self.root_ast[0].body

        self.z3 = Z3Solver()
        self.walk(self.root_state, self.root_ast)

    def walk(self, state, tree):
        """Walking down the AST at depth 1

        Parameters
        ----------
        tree : Any
            The AST being walked down

        """

        if state.sat == False:
            return

        for i in range(len(tree)):
            node = tree[i]
            t = type(node)

            logging.debug("Evaluating AST node of type %s" % t)

            # Is a variable assignment (e.g. x = y)
            if t is ast.Assign:
                # Can have multiple variables left of the operator (e.g. x, y, z = 2)
                for target in node.targets:
                    self.assign(state, node.value, target.id)

            # Is an augmented variable assignment (e.g. x += y)
            elif t is ast.AugAssign:
                self.augassign(state, node)

            # Is an IF statement symbolic state gets forked
            # Interrupt execution
            elif t is ast.If:
                self.conditional(state, node, i)

                # Terminate the original state
                state.active = False

                # Passing current index will re-evaluate the conditional inf.
                self.walk(state.left, tree[i+1:])
                self.walk(state.right, tree[i+1:])

                # Interrupt execution
                return

            # Is everything else
            else:
                logging.debug("Ignored AST node")

    def assign(self, state: State, value: Any, name: str):
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
            v = state.getActiveVariable(value.id)
            state.createSymbolicVariable(name, v)
        # Assigning a constant value to the variable (simplest)
        elif isinstance(value, ast.Constant):
            state.createSymbolicVariable(name, value.value)
        # Go recursive if there is a binary operation
        elif isinstance(value, ast.BinOp):
            # Translate binary operation to properties, or simplified constant
            solver = BinarySolver(state)
            p = solver.solve(value.left, value.op, value.right)
            if isinstance(p, ast.Constant):
                state.createSymbolicVariable(name, p.value)
            else:
                state.createSymbolicVariable(name, p)
        else:
            logging.error("The type %s of the assignment value for variable is unrecognized" % type(node.value))

    def augassign(self, state: State, node: ast.AugAssign):
        """Handing a augmented assignment operation

        Parameters
        ----------
        node : ast.AugAssign
            The AST AugAssign node containing the variable and its state change

        """
        solver = BinarySolver(state)
        # The l-node will never be a Constant, therefore neither will the return

        p = solver.solve(node.target, node.op, node.value)
        state.createSymbolicVariable(node.target.id, p)

    def conditional(self, state: State, node: ast.If, index: int):
        """Handling a conditional operation
        Every conditional will create two symbolic states; true and false
        If these states' properties are SMT unsat; they will be marked as dead.

        Parameters
        ----------
        node : ast.If
            The relevant ast.If node

        """
        # Create new logical properties for relevant variables in relevant state
        test = node.test

        # Generate Conditional Properties (e.g. x__17 >= y__0)
        p_true = state.generateConditionalProperties(test.left, test.ops, test.comparators)
        p_false = copy.copy(p_true)
        p_false.is_true = False

        logging.debug("Forking %s with conditional %s" % (state.name, str(p_true)))
        # Register new conditional symbolic state for TRUE
        true_state = self.forkState(state, p_true)
        state.right = true_state
        self.solve(true_state)

        # Register new conditional symbolic state for FALSE
        false_state = self.forkState(state, p_false)
        state.left = false_state
        self.solve(false_state)

        # Walk recursively down nested IF code
        if true_state.sat:
            self.walk(true_state, node.body)

        # Set false state's AST to orelse Body if exists
        # Process Else conditional
        if false_state.sat and hasattr(node, 'orelse'):
            # Walk recursively down nested ELSE code
            self.walk(false_state, node.orelse)

    def forkState(self, state: State, properties: list):
        s = copy.deepcopy(state)
        s.right = s.left = None
        s.setStateName()
        s.properties.append(properties)
        return s

    def solve(self, state: State):
        logging.debug("Solving %s using Z3" % (state.name))
        state.sat = self.z3.solve(state.properties)
        logging.debug("%s solved using Z3 with state %r" % (state.name, state.sat))
