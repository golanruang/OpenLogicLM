from z3 import *
from itertools import combinations

position = Function("pos", IntSort(), IntSort())
clauses = []

for i in range(1, 8):
	clauses.append(Or(position(i)==1, position(i)==2, position(i)==3, position(i)==4, position(i)==5, position(i)==6, position(i)==7))

for comb in combinations(range(1, 8), 2):
	clauses.append(position(comb[0])!= position(comb[1]))

clauses.append(position(1) < position(3))
clauses.append(position(2) > position(5))
clauses.append(position(4) < position(6))
clauses.append(position(7) > position(3))
clauses.append(position(5) == 2)
clauses.append(position(1) == 1)
clauses.append(position(7) == 7)

conclusion = Not(position(1) == 1)

def is_valid(clauses, conclusion):
    solver = Solver()
    solver.add(clauses)
    solver.add(Not(conclusion))
    return solver.check() == unsat

ans = is_valid(clauses, conclusion)