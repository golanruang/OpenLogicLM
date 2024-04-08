"""
"hypothesis_formula": "(\u00ac{C}{c} & {D}{c})"
sent1: (\u00ac{AA}{a} & \u00ac{AB}{a}) -> {B}{b}
sent2: (x): \u00ac({B}x & {D}x) -> \u00ac{D}x
sent3: {D}{c}
sent4: \u00ac{A}{c} -> \u00ac{C}{c}
sent5: \u00ac{B}{b}
sent6: \u00ac(\u00ac{AA}{a} & \u00ac{AB}{a}) -> \u00ac{A}{c}

variables: x {a} {b} {c} ¬{A} ¬{AA} ¬{AB} {B} ¬{B} ¬{C} {D} ¬{D}

"proofs_formula": ["void -> assump1: (\u00ac{AA}{a} & \u00ac{AB}{a}); sent1 & assump1 -> int1: {B}{b}; int1 & sent5 -> int2: #F#; [assump1] & int2 -> int3: \u00ac(\u00ac{AA}{a} & \u00ac{AB}{a}); int3 & sent6 -> int4: \u00ac{A}{c}; int4 & sent4 -> int5: \u00ac{C}{c}; int5 & sent3 -> hypothesis;"]
"""
from z3 import *

s = Solver()

_Object = DeclareSort('Object')

x = Const('x', _Object)
a = Const('a', _Object)
b = Const('b', _Object)
c = Const('c', _Object)

A = Function('A', _Object, BoolSort())
AA = Function('AA', _Object, BoolSort())
AB = Function('AB', _Object, BoolSort())
B = Function('B', _Object, BoolSort())
C = Function('C', _Object, BoolSort())
D = Function('D', _Object, BoolSort())

clauses = [] 
clauses.append(Implies(And(Not(AA(a)), Not(AB(a))), B(b)))
# # clauses.append(ForAll([x], Implies(Not(And(B(x), D(x))), Not(D(x)))))
# clauses.append(D(c))
# clauses.append(Implies(Not(A(c)), Not(C(c))))
clauses.append(Not(B(b)))
clauses.append(Implies(Not(And(Not(AA(a), Not(AB(a))))), Not(A(c))))

clauses.append(A(c))


# clauses.append(Not(B(b)))
# clauses.append(Implies(And(Not(AA(a)), Not(AB(a))), B(b)))
# Not(And(Not(AA(a)), Not(AB(a))))


# clauses.append(Not(Or(AA(a), AB(b))))


# clauses.append(Not(B(b)))
# clauses.append(Implies(A(a), B(b)))
# clauses.append(A(a))


# clauses.append(Not(A(c)))

# not (hypothesis)
# clauses.append(Not(And(Not(C(c)), D(c))))
# clauses.append(Not(D(c)))

s.add(clauses)

if s.check() == unsat: 
    # print(s.model())
    print("PROVED")

else:
    print("UNPROVED")