from z3 import *
from itertools import combinations
def solve():
	s = Solver()
	position = Function("pos", IntSort(), IntSort())
	for i in range(1, 9):
		s.add(Or(position(i)==1, position(i)==2, position(i)==3, position(i)==4, position(i)==5, position(i)==6, position(i)==7, position(i)==8))
	for comb in combinations(range(1, 9), 2):
		s.add(position(comb[0])!= position(comb[1]))
	s.add(position(1) == 1)
	s.add(position(2) == 2)
	s.add(position(3) > position(1))
	s.add(position(4) > position(3))
	s.add(position(5) > position(4))
	s.add(position(6) > position(5))
	s.add(position(7) > position(6))
	s.add(position(8) == 8)
	s.add(position(7) == 7)
	s.add(position(3) < position(5))
	s.add(position(2) < position(4))
	if s.check() == z3.sat:
		print(s.model())
		return True
	else:
		print("Solution does not exist.")
		return False
solve()