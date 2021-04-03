import copy
from Property import *
from SymbolicVariable import *

# Each state is a node in the tree
class State:
    def __init__(self):
        self.variables = {}
        self.properties = []
        self.right = None
        self.left = None
        self.active = False

    def generateCanonicalName(self, name):
        return "%s_%d" % (name, len(self.variables[name]))

    def addSymbolicVariable(self, name, value):
        # 1. Check if dictionary key exists
        if name not in self.variables.keys():
            self.variables[name] = []

        # 2. Generate canonical name
        canonical_name = self.generateCanonicalName(name)

        # 3. Instantiate new symbolic variable
        v = SymbolicVariable(canonical_name)

        # 4. Register symbolic variable
        self.registerSymbolicVariable(name, v, value)

    def copySymbolicVariable(self, name, copied_variable):
        # 1. Generate canonical name for new variable
        canonical_name = self.generateCanonicalName(name)

        # 2. Get active copied variable
        for t in self.variables[copied_variable]:
            if t.active == True:
                # 3. Copy the desired variable
                v = copy.deepcopy(t)

                # 4. Update the canonical name
                v.name = canonical_name

                # 5. Register variable
                # TODO: Fix, is broken
                self.registerSymbolicVariable(name, v, )
                return

    def tempSymbolicVariable(self, property):
        name = "tv"

        # 1. Check if dictionary key exists
        if name not in self.variables.keys():
            self.variables[name] = []

        canonical_name = self.generateCanonicalName(name)
        v = SymbolicVariable(canonical_name)
        self.registerSymbolicVariable(name, v, property)

    # TODO: this does not support initial assignment
    def forkSymbolicVariable(self, name, property):
        print("Forking", property)

        canonical_name = self.generateCanonicalName(name)

        for t in self.variables[name]:
            if t.active == True:
                # 3. Copy the desired variable
                v = copy.deepcopy(t)

                # 4. Update the canonical name
                v.name = canonical_name

        self.registerSymbolicVariable(name, v, property)

    def registerSymbolicVariable(self, name, variable, value, operator = ast.Eq):
        # 3. Deactivate other symbolic variables, to avoid use it in future operations
        # TODO: scope variables
        for v in self.variables[name]:
            v.active = False

        # Append to relevant list
        self.variables[name].append(variable)

        # Add property representing the variable's symbolic value
        print(variable, operator, value)
        self.properties.append(Property(variable, operator(), value))

    def addProperty(self, left, op, right):
        self.properties.ammend(left, op, right)


    def addProperties(self, left, ops, comparators):
        self.properties.append(self.addPropertiesRecursive(left, ops, comparators))

    def addPropertiesRecursive(self, left, ops, comparators):
        op = ops.pop(0)
        comparator = comparators.pop(0)

        if type(left) == ast.Name:
            l = self.getActiveVariable(left.id)
        else:
            l = left.value

        if type(comparator) == ast.Name:
            r = self.getActiveVariable(comparator.id)
        else:
            r = comparator.value

        if (len(comparators) > 0):
            return Property(l, op, self.addPropertiesRecursive(comparator, ops, comparators))
        else:
            return Property(l, op, r)

    def getActiveVariable(self, name):
        for t in self.variables[name]:
            if t.active == True:
                return t
