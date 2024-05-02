from z3 import *
from itertools import combinations
def solve_arrangement():
	constraints = []
	position = Function("pos", IntSort(), IntSort())
	for i in range(1, 8):
		constraints.append(Or(position(i)==1, position(i)==2, position(i)==3, position(i)==4, position(i)==5, position(i)==6, position(i)==7))
	for comb in combinations(range(1, 8), 2):
		constraints.append(position(comb[0])!= position(comb[1]))
	constraints.append(position(1) < position(3))
	constraints.append(position(2) > position(5))
	constraints.append(position(4) < position(6))
	constraints.append(position(7) > position(3))
	constraints.append(position(5) == 2)
	constraints.append(position(1) == 1)
	constraints.append(position(7) == 7)
	constraints.append(Not(position(1) == 1))
	s = Solver()
	for c in constraints: s.add(c)
	if s.check() == unsat: return True
	else: return False
