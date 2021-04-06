# SymbolicPy

SymbolicPy is a lightweight symbolic execution engine for Python, using Python's Abstract Syntax Tree and outputting a PDF graph of possible Symbolic States using GraphViz.
This is a learning tool which only supports integers. See the compatibility section for additional details. It is built using Python 3.9's syntax.
It uses Z3 as an SMT solver.

## Installation

Install `docker` and `docker-compose` locally, and run `docker-compose build` to build the SymbolicPy container.

## Compatibility

SymbolicPy currently only supports operations on integer values, and simple arithmetic operators (e.g. if x > 3).
It only parses function definitions when the entire file is a function definition.
Note that complex conditionals are also not currently supported (e.g. if x > y and y % 2 != 1:)

## Usage

* Write python code to the `input.py` file.
* Run `docker-compose up`.
* Retrieve the PDF from the `output` directory.

## Contributing
Pull requests are welcome. For major changes, please open an issue first to discuss what you would like to change.

Please make sure to update tests as appropriate.

## License
[MIT](https://choosealicense.com/licenses/mit/)
