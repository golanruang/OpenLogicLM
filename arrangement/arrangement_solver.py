from z3 import *
from itertools import combinations
def solve_arrangement():
	s = Solver()
	position = Function("pos", IntSort(), IntSort())
	for i in range(1, 6):
		s.add(Or(position(i)==1, position(i)==2, position(i)==3, position(i)==4, position(i)==5))
	for comb in combinations(range(1, 6), 2):
		s.add(position(comb[0])!= position(comb[1]))
	s.add(position(3) == 1)
	s.add(position(2) == 4)
	s.add(position(1) < position(2))
	s.add(position(5) < position(2))
	s.add(position(4) > position(2))
	models = []
	while s.check() == sat:
		m = s.model()
		models.append(m)
		clauses = []
		for i in range(1, 6):
			val_at_i = m.evaluate(position(i))
			clauses.append(position(i) == val_at_i)

		s.add(Not(And(clauses)))
	return models