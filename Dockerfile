FROM python:3.9

RUN pip install --no-cache-dir --upgrade pip z3-solver graphviz
RUN apt-get update
RUN apt-get install -y python-pydot python-pydot-ng graphviz xdg-utils

WORKDIR /multiverse
