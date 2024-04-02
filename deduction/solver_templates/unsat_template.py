"""
"hypothesis_formula": "\u00ac{C}{b}"
"context_formula": sent1: (x): ({A}x v {B}x) -> {C}{b} 
sent2: {C}{go} 
sent3: (x): {B}x -> {C}{b} 
sent4: {C}{id} 
sent5: {BD}{b} 
sent6: (x): ({B}x v {A}x) -> {C}{a}

^ this is unsatisfied

variables: b, x, go, id, a, 
predicates: C, A, B, BD
"""

from z3 import *

s = Solver() 

_Object = DeclareSort('Object')

b = Const('b', _Object)
x = Const('x', _Object)
go = Const('go', _Object)
id = Const('id', _Object)
a = Const('a', _Object)

C = Function('C', _Object, BoolSort())
A = Function('A', _Object, BoolSort())
B = Function('B', _Object, BoolSort())
BD = Function('BD', _Object, BoolSort())

s.add(ForAll([x], Implies(Or(A(x), B(x)), C(b))))
s.add(C(go))
s.add(ForAll([x], Implies(B(x), C(b))))
s.add(C(id))
s.add(BD(b))
s.add(ForAll([x], Implies(Or(B(x), A(x)), C(a))))

s.add(Not(Not(C(b))))

if s.check() == unsat: 
    print(s.model())
    print("PROVED")

else:
    print("UNPROVED")