import ast
from SymbolicVariable import *

# TODO: Comment
# TODO: Split into Binary and Conditional subtypes
class Property:
    # l and r Can be symbolic variable, or constant value
    def __init__(self, l, op, r):
        self.l = l
        self.r = r

        self.r_isvar = type(r) == SymbolicVariable
        self.l_isvar = type(l) == SymbolicVariable

        conditional_operators = {
            ast.Eq: "==",
            ast.NotEq: "!=",
            ast.Lt: "<",
            ast.LtE: "<=",
            ast.Gt: ">",
            ast.GtE: ">=",
        }

        binary_operators = {
            ast.Add: "+",
            ast.Sub: "-",
            ast.Mult: "*",
            ast.Div: "/",
            ast.Mod: "%",
            ast.Pow: "**",
            ast.LShift: "<<",
            ast.RShift: ">>"
        }

        if type(op) in conditional_operators:
            self.type = "conditional"
            self.op = conditional_operators[type(op)]

        elif type(op) in binary_operators:
            self.type = "binary"
            self.op = binary_operators[type(op)]

        else:
            logging.error("The operator %s is not supported", op)

    def getSymbolicVariables(self):
        v = []
        if self.r_isvar:
            v.append(self.r)
        if self.l_isvar:
            v.append(self.l)
        return v

    def getExprName(self, v):
        if type(v) == SymbolicVariable:
            return v.name
        return v


    def getExpressions(self):
        expressions = []
        if type(self.r) == Property:
            # Need to unwind recursive properties into simple expressions (e.g. x==y, y==z)
            # This is done because Z3 does not accept complex expressions contianing conditional operators (e.g. x==y==z)
            # 1. Recursive unwind if conditional
            if self.r.type == "conditional":
                expressions.append("%s %s %s" % (self.getExprName(self.l), self.op, self.getExprName(self.r.l)))
                # If conditional, should be recursive
            elif self.r.type == "binary":
                expressions.append("%s %s %s" % (self.getExprName(self.l), self.op, self.r.getRecursiveExpression()))
                return expressions

            # Merge expressions lists
            expressions[len(expressions):] = self.r.getExpressions()
        else:
            expressions.append(self.getUnwoundExpression())
        return expressions

    def getRecursiveExpression(self):
        if type(self.r) == Property:
            return "%s %s %s" % (self.getExprName(self.l), self.op, self.r.getRecursiveExpression())
        else:
            return self.getUnwoundExpression()

    def getUnwoundExpression(self):
        return "%s %s %s" % (self.getExprName(self.l), self.op, self.getExprName(self.r))

    def __str__(self):
        return self.getRecursiveExpression()
