from z3 import *
from itertools import combinations
def solve(constraint):
	s = Solver()
	position = Function("pos", IntSort(), IntSort())
	for i in range(1, 6):
		s.add(Or(position(i)==1, position(i)==2, position(i)==3, position(i)==4, position(i)==5))
	s.add(position(2) > position(5))
	s.add(position(3) < position(5))
	s.add(position(2) == 4)
	s.add(position(4) == 2)
	for comb in combinations(range(1, 6), 2):
		s.add(position(comb[0])!= position(comb[1]))
	s.add(constraint)
	if s.check() == z3.sat:
		print(s.model())
		return True
	else:
		print("Solution does not exist.")
		return False