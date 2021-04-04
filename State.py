import copy
import uuid
import logging
from Property import *
from SymbolicVariable import *
from typing import Any

logging.basicConfig(format='%(levelname)s:%(message)s', level=logging.DEBUG)

class State:
    """A single possible symbolic state, and its references

    Attributes
    ----------
    variables : Dict[str, List[SymbolicVariable]]
        Dictionary mapping concrete variables to all their symbolic equivalents.
    properties : List[Property]
        List of all state properties.
    right : State
        Right reference (True)
    left : State
        Left reference (False)
    sat : bool
        Whether or not the state is satisfiable

    """

    def __init__(self, rand_names = False):

        self.variables = {}
        self.properties = []
        self.right = None
        self.left = None
        self.sat = True

        # Generate random string for canonical variable names
        if rand_names:
            self.rand = str(uuid.uuid4())[:8]
        else:
            self.rand = ''
        self.tmp = "%s%s" % ('tmp', self.rand)

    def generateCanonicalName(self, name: str) -> str:
        """Generates the canonical name of a symbolic value

        Parameters
        ----------
        name : str
            The name of the concrete variable

        Returns
        -------
        str
            The canonical name of the symbolic value

        """
        if name not in self.variables.keys():
            self.variables[name] = []
        return "%s_%s_%d" % (name, self.rand, len(self.variables[name]))

    def createSymbolicVariable(self, value: Any, name = None) -> SymbolicVariable:
        """Create a symbolic variable.

        Parameters
        ----------
        value : Any
            Initial property of the symbolic variable
            Can be a constant, symbolic variable or property containing a binary operator
        name : str
            Concrete name fo the variable

        Returns
        -------
        SymbolicVariable
            The newly created symbolic variable

        """
        # Default to temporary variable name
        if name is None:
            name = self.tmp

        # Check if variable already exists
        exists = name in self.variables

        # Register variable
        canonical_name = self.generateCanonicalName(name)
        variable = SymbolicVariable(canonical_name)

        # Append to relevant list
        self.variables[name].append(variable)

        # Add property representing the variable's symbolic value
        self.properties.append(Property(variable, ast.Eq(), value))
        logging.debug("Adding new variable %s with value %s" % (name, value))
        return variable

    def addConditionalProperties(self, left: Any, ops: list, comparators: list):
        """Add a list of properties derived from conditional operators

        Parameters
        ----------
        left : Any
            Left element in the conditional operation, either variable or constant
        ops : list
            List of conditional operators
        comparators : list
            List of right elements in the conditional operation
            Length and order is aligned with ops

        """
        self.properties.append(self.addConditionalPropertiesRecursive(left, ops, comparators))

    def addConditionalPropertiesRecursive(self, left: Any, ops: list, comparators: list) -> Property:
        """Recursive helper for addConditionalProperties

        Returns
        -------
        Property
            Returns the Property tree

        """
        # Pop first operator and comparator
        op = ops.pop(0)
        comparator = comparators.pop(0)

        l = self.unpackObjectValue(left)
        r = self.unpackObjectValue(comparator)

        if (len(comparators) > 0):
            return Property(l, op, self.addConditionalPropertiesRecursive(comparator, ops, comparators))
        else:
            return Property(l, op, r)

    def unpackObjectValue(self, obj: Any) -> Any:
        """Helper for addConditionalPropertiesRecursive, gets an object's value

        Parameters
        ----------
        obj : Any
            An ast.Name or an ast.Constant

        Returns
        -------
        Any
            Returns a SymbolicVariable, or the value of the constant

        """
        if isinstance(obj, ast.Name):
            return self.getActiveVariable(obj.id)
        elif isinstance(obj, ast.Constant):
            return obj.value
        else:
            logging.error("Expected object of type ast.Name or ast.Constant. Got object of type %s" % type(obj))

    def getActiveVariable(self, name: str) -> SymbolicVariable:
        """Gets the symbolic value that is currently active

        Parameters
        ----------
        name : str
            Concrete variable name

        Returns
        -------
        SymbolicVariable
            Last symbolic variable

        """
        return self.variables[name][-1]
