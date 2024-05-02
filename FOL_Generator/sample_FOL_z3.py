from z3 import *

_Object = DeclareSort('Object')
x = Const('x', _Object)

Penguins = Const('Penguins', _Object)

HasWings = Function('HasWings', _Object, BoolSort())
Bird = Function('Bird', _Object, BoolSort())
Fly = Function('Fly', _Object, BoolSort())
Animal = Function('Animal', _Object, BoolSort())

clauses = []
clauses.append(Bird(Penguins))
clauses.append(Not(Fly(Penguins)))
clauses.append(ForAll([x], Implies(And(Animal(x), Fly(x)), HasWings(x))))

conclusion = HasWings(Penguins)

def is_valid(clauses, conclusion):
    solver = Solver()
    solver.add(clauses)
    solver.add(Not(conclusion))
    return solver.check() == unsat

ans = is_valid(clauses, conclusion)
