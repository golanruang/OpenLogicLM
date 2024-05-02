from z3 import *
from itertools import combinations

def solve_arrangement():
    constraints = []

    position = Function("pos", IntSort(), IntSort())
    for i in range(1, 8):
        constraints.append(Or(position(i)==1, position(i)==2, position(i)==3, position(i)==4, position(i)==5, position(i)==6, position(i)==7))
    for comb in combinations(range(1, 8), 2):
        constraints.append(position(comb[0])!= position(comb[1]))

    constraints.append(position(2) > position(5))
    constraints.append(position(3) < position(1))
    constraints.append(position(4) < position(7))
    constraints.append(position(6) > position(1))
    constraints.append(position(7) > position(3))
    constraints.append(position(1) > position(7))
    constraints.append(position(2) < position(6))
    constraints.append(position(1) == 4)

    # check answer A)
    constraints.append(Not(position(2) == 6))
    s = Solver()
    for c in constraints: s.add(c)
    if s.check() == unsat: return "A"
    constraints.pop()

    # check answer B)
    constraints.append(Not(position(3) < position(1)))
    s = Solver()
    for c in constraints: s.add(c)
    if s.check() == unsat: return "B"
    s.pop()

    # check answer C)
    constraints.append(Not(position(5) == 3))
    s = Solver()
    for c in constraints: s.add(c)
    if s.check() == unsat: return "C"
    s.pop()

    # check answer D)
    constraints.append(Not(position(6) == 6))
    s = Solver()
    for c in constraints: s.add(c)
    if s.check() == unsat: return "D"
    s.pop()

    # check answer E)
    constraints.append(Not(position(4) < position(2)))
    s = Solver()
    for c in constraints: s.add(c)
    if s.check() == unsat: return "E"
    s.pop()

a = solve_arrangement()
print(f"a: {a}")