"""
A(a), B(a) -> C(a)
A(a)
B(a)
"""
from z3 import * 

s = Solver() 

_Object = DeclareSort('Object')

a = Const('a', _Object)
A = Function('A', _Object, BoolSort())
B = Function('B', _Object, BoolSort())
C = Function('C', _Object, BoolSort())

clauses = [] 
clauses.append(Implies(And(A(a), B(a)), C(a)))
clauses.append(A(a))
clauses.append(B(a))

s.add(clauses)

if s.check() == sat: 
    print(s.model())

else:
    print("Unsat")