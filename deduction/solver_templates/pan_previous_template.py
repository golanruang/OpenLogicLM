"""
predicates:
    Movie(x)
    HappyEnding(x)
premises:
    ¬∀x (Movie(x) → HappyEnding(x))
    Movie(titanic)
    ¬HappyEnding(titanic)
    Movie(lionKing)
    HappyEnding(lionKing)
conclusion:
    ∃x (Movie(x) ∧ ¬HappyEnding(x))
label: TRUE
"""

from z3 import *

_Object = DeclareSort('Object')
x = Const('x', _Object)

LionKing = Const('LionKing', _Object)
Titanic = Const('Titanic', _Object)

Movie = Function('Movie', _Object, BoolSort())
HappyEnding = Function('HappyEnding', _Object, BoolSort())

clauses = []
clauses.append(Exists([x], Implies(Movie(x), Not(HappyEnding(x)))))
clauses.append(Movie(Titanic))
clauses.append(Not(HappyEnding(Titanic)))
clauses.append(Movie(LionKing))
clauses.append(HappyEnding(LionKing))

conclusion = Exists([x], And(Movie(x), Not(HappyEnding(x))))