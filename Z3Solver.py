from z3 import *
import logging

class Z3Solver:
    """Z3 handler class"""

    # For each property passed, translate the op to Z3
    def solve(self, properties: list) -> bool:
        """Solve given a set of properties

        Parameters
        ----------
        properties : list[Property]
            List of properties

        Returns
        -------
        bool
            Whether or not the equation is SAT

        """
        self.simplify(properties)
        s = z3.Solver()
        for p in properties:

            # Instantiate Z3 variables locally
            for v in p.getSymbolicVariables():
                locals()[v.name] = z3.Int(v.name)

            expressions = p.getExpressions()
            for expression in expressions:
                if p.is_true:
                    s.add(eval(expression))
                else:
                    s.add(z3.Not(eval(expression)))

        logging.debug("Z3 is evaluating %s" % s)

        sat = s.check().r

        # TODO: implement
        if (sat == z3.Z3_L_TRUE):
            m = s.model()

        return (sat == z3.Z3_L_TRUE)


    def simplify(self, properties: list) -> z3.ApplyResult:
        """Use z3 to simplify equations

        Parameters
        ----------
        properties : List[Property]
            Description of parameter `properties`.

        Returns
        -------
        z3.ApplyResult
            Contains simplified properties.

        """
        expressions = []
        for p in properties:
            # Instantiate Z3 variables locally
            for v in p.getSymbolicVariables():
                locals()[v.name] = z3.Int(v.name)
            expressions.append(p.z3String())


        expression = "z3.And(%s)" % ", ".join(expressions)
        t = z3.Tactic('simplify')
        return t(eval(expression))
