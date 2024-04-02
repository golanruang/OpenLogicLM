"""
"hypothesis_formula": "{B}{bb}"            
"context_formula:": "sent1: \u00ac{AA}{aa} -> {B}{bb} sent2: \u00ac{AA}{aa}"
"proofs_formula: ["sent2 & sent1 -> int1: {B}{bb}; int1 -> hypothesis;"].

"hypothesis": "the car is new."
"context": "sent1: if the wheels are not flat, the car is new sent2: the wheels are not flat".
"proofs_formula": ["sent2 & sent1 -> int1: the car is new; int1 -> hypothesis;"].  

for x B(x) -> A{x}

ForAll()
Exists()
"""
from z3 import * 

AAaa, Bbb = Bools('AAaa Bbb')

solver = Solver() 

c1 = Implies(Not(AAaa), Bbb)
c2 = Not(AAaa)

solver.add(Bbb)                 # add hypothesis as clause 
solver.add(c1)
solver.add(c2)

if solver.check() == sat: 
    print(solver.model())

else:
    print("Unsat")