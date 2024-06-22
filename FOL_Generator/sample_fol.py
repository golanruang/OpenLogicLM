from z3 import *

_Object = DeclareSort('Object')
x = Const('x', _Object)


Helen = Const('Helen', _Object)
DairyProducts = Const('DairyProducts', _Object)
Meat = Const('Meat', _Object)
AnimalProducts = Const('AnimalProducts', _Object)


Eat = Function('Eat', _Object, _Object, BoolSort())
Consume = Function('Consume', _Object, _Object, BoolSort())
Vegetarian = Function('Vegetarian', _Object, BoolSort())
Vegan = Function('Vegan', _Object, BoolSort())


clauses = []
clauses.append(And(Vegetarian(Helen), Not(Vegan(Helen))))
clauses.append(ForAll([x], Implies(Vegetarian(x), Not(Eat(x, Meat)))))
clauses.append(ForAll([x], Implies(Vegan(x), Not(Consume(x, AnimalProducts)))))
clauses.append(Consume(Helen, DairyProducts))
clauses.append(Exists([x], And(Vegetarian(x), Consume(x, DairyProducts))))


conclusion = And(Not(Eat(Helen, Meat)), Consume(Helen, DairyProducts))


def is_valid(clauses, conclusion):
        solver = Solver()
        solver.add(clauses)
        solver.add(Not(conclusion))
        return solver.check() == unsat


ans = is_valid(clauses, conclusion)