import z3

class Z3Solver:
    def __init__(self):
        pass
    # For each property passed, translate the op to Z3
    def solve(self, properties):
        s = z3.Solver()
        for p in properties:
            # Instantiate Z3 variables locally
            for v in p.getSymbolicVariables():
                locals()[v.name] = z3.Int(v.name)

            expressions = p.getExpressions()
            for expression in expressions:
                print("Expression: ", expression)
                s.add(eval(expression))

        print("Solving for:", s)
        return (s.check().r == z3.Z3_L_TRUE)

    # TODO: Implement for pretty print
    def simplify(self, properties):
        pass
