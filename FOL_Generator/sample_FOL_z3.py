from z3 import *

_Object = DeclareSort('Object')
x = Const('x', _Object)



HasWings = Function('HasWings', _Object, BoolSort())
Penguin = Function('Penguin', _Object, BoolSort())
Bird = Function('Bird', _Object, BoolSort())
Fly = Function('Fly', _Object, BoolSort())



clauses = []
clauses.append(ForAll([x], Implies(Penguin(x), Bird(x))))
clauses.append(ForAll([x], Implies(Penguin(x), Not(Fly(x)))))
clauses.append(ForAll([x], Implies(And(Bird(x), Fly(x)), HasWings(x))))


conclusion = ForAll([x], Implies(Penguin(x), HasWings(x)))


def is_valid(clauses, conclusion):
    solver = Solver()
    solver.add(clauses)
    solver.add(Not(conclusion))
    return solver.check() == unsat


ans = is_valid(clauses, conclusion)