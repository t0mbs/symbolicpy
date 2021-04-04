import z3
import logging

logging.basicConfig(format='%(levelname)s:%(message)s', level=logging.DEBUG)

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
                s.add(eval(expression))

        logging.debug("Z3 solving is evaluating: %s" % s)

        sat = s.check().r

        # TODO: implement
        if (sat == z3.Z3_L_TRUE):
            m = s.model()
            print(m)
        
        logging.debug("Z3 solution value: %i " % sat)
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
            expressions.append(str(p))


        expression = "z3.And(%s)" % ", ".join(expressions)
        t = z3.Tactic('simplify')
        return t(eval(expression))
