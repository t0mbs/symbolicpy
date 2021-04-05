# Objectives
* Symbolic Execution for source code (Shell?)
* Conditional identification
  * Preliminary pass-through and binary tree generation,
* Step function
  * Execution (with type inference?)
    * Load it up into some kind of controlled environment.
  * Assign symbolic values (x0, y0)
* Computation tree generator
* Loop detection and recursion limits
* Symbolic Solvers SMT; use Z3 or MAYBE CVC
  * Z3 for numbers,
  * Z3-str for string manipulation; https://www.cs.purdue.edu/homes/xyzhang/Comp/fse13.pdf

This is highly complex;
https://github.com/bannsec/pySym/blob/master/docs/what_is_implemented.rst
https://github.com/carlospolop

Partial list of existing solutions;
https://github.com/ksluckow/awesome-symbolic-execution



=> Super simple at first; one file, one function, many conditionals, pure symbolic, only int types.
Why is C so important?
* Many languages can be compiled into C (C++, Rust, cGo)
* If it can be solved for C, it can be solved for all of these languages.
Essentially C tools act as "semi-compiled" DSE.

Benefits of running it on low-level binary?
  * Compatible with essentially any language,
  * Can be run much quicker,
  * Can have simplified logic;
    * Python sourcecode IFs have; multi-line, inline, lambda, etc.
    * Formats can be more complex than assembly
    * Syntax is also version-dependent, so all of a sudden you need to update your DSE tool along side the language.
Also; this detection logic is built into the compilers, so often DSE is built on top of the compilers (e.g. KLEE)
Z3 string solving.

# Do it for Python,
## Step 1, parsing the file
1. Build your Parser, to identify functions, variables and IF statements
  * Could pull from ADSL https://github.com/python/cpython/blob/master/Parser/Python.asdl
  * Could also use Python's parser library to access parse trees; https://docs.python.org/3/library/parser.html
  * Parser is deprecated, use AST (Abstract Syntact Tree) instead https://docs.python.org/3/library/ast.html#module-ast
  * Visualize using: https://github.com/pombredanne/python-ast-visualizer/blob/master/astvisualizer.py

* For now, only care about:
  * Run on FUNCTIONS with INPUTS
  * Dead-ends (or unsat)
  * Error identification
  * Computation tree generation (Graphing)
    * http://www.cs.umd.edu/class/fall2020/cmsc430/Graphviz.html
  * Trace generation (if errors are encountered)
  * Document code

* Dependencies
  * `python3.9 -m pip install graphviz`
  * `python3.9 -m pip install z3-solver`
  * `python3.9 -m pip install sympy`



* Support left-constant conditional statements, (DONE)
* Support complex conditionals (DONE)
* Implement simple binary operators (DONE)
* Implement AugAssign (DONE)
* Cleanup & Doc (Done)
  * Error handling (Done)
  * Implement logger (Done)
  * Comment code (Done)
  * Refactor code (Done)
  * Address TODOs (Done)
  * Unit tests (DONE)
* Graph it out (Done)
* Fix inactivity (Done)
* Walk and think through recursion (Done)
* Revisit the "inactive states", to revisit them rather than only pursuing a single execution path. (Done)
  * Unless it's UNSAT, in which case it's dead. (Done)
* Add ELSE statements (Done)
* Add function / user input support (Done)


* Nice to have
  * Improve memory stuff
    * Simplify equations
    * Recycle old or unused variables
    * Only send to Z3 those "net new" variables to evaluate
      * e.g. z == y, don't send x
      * This would not work if z or y has a symbolic dependency to x
  * Add step function
  * Support ast.AnnAssign and ast.Delete
  * Implement SymPy for simplification and pretty printing of equation
  * Replace simply GraphViz by HTML frontend
* Parsing the file name
* Line-injection for positions (with graph)
* Support FLAGS!!!
* GitHub implementation
  * GitHub badge
  * Compatibility table

* Add logical comparison (&&, ||)




Advanced
* Implement BitVectors for bit shifting
* Implement complex binary operators (FloorDiv, MatMult, BitOr, BitXor, BitAnd)
* Implement complex comparison operators is, isnot, in, not in as conditional operators, (optional)
* Implement unary operators
* Implement complex function arguments (e.g. positional arguments)
* Implement DSE
* SSE / DSE Syncing on "if" statement => with line injection
* Implement other object types (e.g. dict, list, real)
* Suggest fuzzing values
* Define entrypoint
