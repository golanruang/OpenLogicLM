"""
https://microsoft.github.io/z3guide/docs/logic/propositional-logic

from z3 import *

p = Bool('p')
q = Bool('q')
r = Bool('r')

solve(Implies(p, q), r == Not(q), Or(Not(p), r))
$ python example5.py
[q = True, p = False, r = False]
Implies(p, q) is a constraint that means that if p is True, q is True, but if p is False, q can be True or False. It is the logical implication.

Z3 Python API also implements Distinct(x, y, z)

https://infosecadalid.com/2021/08/27/my-introduction-to-z3-and-solving-satisfiability-problems/

(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(define-fun conjecture () Bool
	(=> (and (=> p q) (=> q r))
		(=> p r)))
(assert (not conjecture))
(check-sat)

"hypothesis_formula": "{B}{bb}"            
"context_formula:": "sent1: \u00ac{AA}{aa} -> {B}{bb} sent2: \u00ac{AA}{aa}"
"proofs_formula: ["sent2 & sent1 -> int1: {B}{bb}; int1 -> hypothesis;"].

https://www.youtube.com/watch?v=e85YnbMDR8E&ab_channel=DG

If it is raining and Jane does not have her umbrella with her, then she will get wet. 
Jane is not wet. It is raining. 
Therefore, Jane has her umbrella with her. 

R = raining 
U = umbrella with her 
W = wet 
"""
from z3 import *

R, U, W = Bools('R U W')
solver = Solver() 

c1 = Implies(And(R, Not(U)), W)   # if it is raining and jane does not have her umbrella with her, then she will get wet. 
c2 = Not(W)
c3 = R
c4 = U

solver.add(c1)
solver.add(c2)
solver.add(c3)
solver.add(c4)

if solver.check() == sat: 
    print(solver.model())

else:
    print("Unsat")