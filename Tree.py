import ast
from State import *
from Property import *
from SymbolicVariable import *
from Z3Solver import *

class Tree:
    def __init__(self, ast_tree):
        self.root = State()
        self.solver = Z3Solver()
        # Current active state
        self.state = self.root
        self.walk(ast_tree)

    def binOpPropertyHelper(self, l, op, r):
        pass

    def solveBinOp(self, node):
        print(ast.dump(node, indent=4))
        # Solve for two constants
        l = node.left
        r = node.right
        op = node.op

        # l and r both have three possible types; ast.Name (variable), ast.Constant (constant), or ast.BinOp (nested binary operation).
        # 1. Reduce nested binary operations into properties (?)
        if isinstance(l, ast.BinOp):
            l = self.solveBinOp(l)
        if isinstance(r, ast.BinOp):
            r = self.solveBinOp(r)

        # 2. If l is a property, assign it to a temporary variable
        if isinstance(l, Property):
            print("IS TEMP")
            self.state.tempSymbolicVariable(l)
            l = ast.Name("tv")
            print(l)

        # Simplify two constants down to one by executing operation
        # Because of left-side variable assignment, this can only happen in recursions
        if isinstance(l, ast.Constant) and isinstance(r, ast.Constant):
            print("Simplifying multiple constants!", l.value, op, r.value)
            return ast.Constant(eval(ast.unparse(node)))


        # Iterate on the symbolic variable
        # TODO: Simplify logic
        if isinstance(l, ast.Name) and isinstance(r, ast.Constant):
            print("Where")
            print(l.id)
            p = Property(
                self.state.getActiveVariable(l.id),
                op,
                r.value
            )
            print(p.l, p.op, p.r)
            return p

        if isinstance(l, ast.Constant) and isinstance(r, ast.Name):
            print("There")
            return Property(
                l.value,
                op,
                self.state.getActiveVariable(r.id)
            )

        # If left is a variable??
        if isinstance(l, ast.Name) and isinstance(r, ast.Name):
            print("Here")
            return Property(
                self.state.getActiveVariable(l.id),
                op,
                self.state.getActiveVariable(r.id)
            )

        return self.binOpPropertyHelper(l, op, r)



    def assign(self, node, name):
        # Assigning a variable's value to another variable
        if isinstance(node.value, ast.Name):
            self.state.copySymbolicVariable(name, node.value.id)
        # Assigning a constant value to the variable (simplest)
        elif isinstance(node.value, ast.Constant):
            self.state.addSymbolicVariable(name, node.value.value)
        # Go recursive if there is a binary operation
        elif isinstance(node.value, ast.BinOp):
            print("BINARY OPERATION TIME")
            # Fork left variable
            # Translate binary operation to properties, or simplified constant
            p = self.solveBinOp(node.value)
            if isinstance(p, ast.Constant):
                self.state.forkSymbolicVariable(name, p.value)
            else:
                self.state.forkSymbolicVariable(name, p)
        else:
            print("The type of the assignment value for variable is unrecognized", type(node.value))

    def walk(self, tree):
        for node in ast.iter_child_nodes(tree):

            # Instantiate a new symbolic variable (x0, x1, x2) on assignment
            # TODO: Simplify properties and recycle variables (e.g. x2==x1, x1==x0 to x2==x0)
            # If an incremented symbolic variable is assigned, and its predecessor has no relations.

            if isinstance(node, ast.Assign): # Add AugAssign and AnnAssign here
                for target in node.targets:
                    # Left variable name
                    name = target.id
                    # Recursive function to deal with nested binary operations
                    self.assign(node, name)

            elif isinstance(node, ast.AugAssign):
                node.left = node.target
                node.right = node.value
                p = self.solveBinOp(node)
                if isinstance(p, ast.Constant):
                    self.state.forkSymbolicVariable(node.target.id, p.value)
                else:
                    self.state.forkSymbolicVariable(node.target.id, p)

            elif isinstance(node, ast.AnnAssign):
                pass
            elif isinstance(node, ast.Delete):
                pass

            elif isinstance(node, ast.If):
                # TODO: support multiple comparators or operations
                # Create new logical properties for relevant variables in relevant state
                print("If", node, )
                test = node.test

                # 1. Register new conditional property
                true_state = copy.deepcopy(self.state)

                # NEEDS TO BE RECURSIVE
                true_state.addProperties(test.left, test.ops, test.comparators)

                sat = self.solver.solve(true_state.properties)

                # Does the true state solve?
                if sat:
                    print("sat")
                    self.state.right = true_state
                    # TODO: add the inverse property for false node if there's an else
                    self.state.left = copy.deepcopy(self.state)

                    self.state = true_state
                    # print(ast.dump(node, indent=4))
                    self.walk(node)

                # TODO: Merge back

                # Dead
                else:
                    print("unsat")
                    pass
