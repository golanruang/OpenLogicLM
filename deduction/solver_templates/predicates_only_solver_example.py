"""
"hypothesis_formula": "({A} & {C})" 
"sent1": "\u00ac{DN}"
"sent2": "\u00ac{B}"
"sent3": "(\u00ac{A} & {B}) -> \u00ac{DD}"
"sent4": "{C}" 
"sent5": "\u00ac{JI} -> \u00ac({AJ} & {GF})"
"sent6": "\u00ac({AA} & \u00ac{AB}) -> {B}"
"sent7": "\u00ac{A} -> \u00ac({AA} & \u00ac{AB})"
"sent8": "{DH}"
"sent9": "{AS}"

variables: A, B, C, DN, DD, JI, AJ, GF, AA, AB, DH, AS
"""

from z3 import *

s = Solver() 

_Object = DeclareSort('Object')

A = Function('A', _Object, BoolSort())
B = Function('B', _Object, BoolSort())
C = Function('C', _Object, BoolSort())
DN = Function('DN', _Object, BoolSort())
DD = Function('DD', _Object, BoolSort())
JI = Function('JI', _Object, BoolSort())
AJ = Function('AJ', _Object, BoolSort())
GF = Function('GF', _Object, BoolSort())
AA = Function('AA', _Object, BoolSort())
AB = Function('AB', _Object, BoolSort())
DH = Function('DH', _Object, BoolSort())
AS = Function('AS', _Object, BoolSort())

y = Const('y', _Object)

s.add(Not(DN(y)))
s.add(Not(B(y)))
s.add(Implies(And(Not(A(y)), B(y)), Not(DD(y))))
s.add(C(y))
s.add(Implies(Not(JI(y)), Not(And(AJ(y), GF(y)))))
s.add(Implies(Not(And(AA(y), Not(AB(y)))), B(y)))
s.add(Implies(Not(A(y)), Not(And(AA(y), Not(AB(y))))))
s.add(DH(y))
s.add(AS(y))

s.add(Not(And(A(y), C(y))))

if s.check() == unsat: 
    print("PROVED")

else:
    print("UNPROVED")