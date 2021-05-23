from pysmt.shortcuts import *
from pysmt.typing import INT
from pysmt.simplifier import BddSimplifier
x = Symbol("x", INT)
y = Symbol("y", INT)
z = Symbol("z", INT)
a = LT(x, y)
b = LT(y, z)
bdd = BddSimplifier()
s = bdd.simplify(And(a,b))
print(s)