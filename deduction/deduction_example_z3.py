"""
https://microsoft.github.io/z3guide/docs/logic/propositional-logic

"hypothesis_formula": "{B}{bb}"            
"context_formula:": "sent1: \u00ac{AA}{aa} -> {B}{bb} sent2: \u00ac{AA}{aa}"
"proofs_formula: ["sent2 & sent1 -> int1: {B}{bb}; int1 -> hypothesis;"].

Output:
"hypothesis": "The city park is open and the lighting system is functional.",
"context": "sent1: The gate is not locked. sent2: The walkways are not cleared. sent3: If the park is not open and the walkways are cleared, then the fountains are not working. sent4: The lighting system is functional. sent5: If the night patrol is not active, it means that the safety measures and the visibility are not adequate. sent6: If the recreational areas are not accessible and the night patrol is active, the walkways are cleared. sent7: If the park is not open, it means that the recreational areas are not accessible and the night patrol is active. sent8: The garden areas are maintained. sent9: The emergency exits are accessible.",
"proofs": ["void -> assump1: The park is not open; sent7 & assump1 -> int1: The recreational areas are not accessible and the night patrol is active; int1 & sent6 -> int2: The walkways are cleared; int2 & sent2 -> int3: #F#; [assump1] & int3 -> int4: The park is open; int4 & sent4 -> hypothesis;"]
"proof_label": "PROVED"

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
"""
from z3 import *

# Define variables
CarIsNew = Bool('CarIsNew')
WheelsNotFlat = Bool('WheelsNotFlat')

# Solver setup
s = Solver()

# Context encoding
# sent2: The wheels are not flat
s.add(WheelsNotFlat == True)

# sent1: If the wheels are not flat, then the car is new
s.add(Implies(WheelsNotFlat, CarIsNew))
# https://stackoverflow.com/questions/11817007/how-to-use-implies-and-if-boolean-commands-in-z3-python-api

# Check if the hypothesis "the car is new" can be proven
if s.check() == sat:
    print("The hypothesis can be proven given the context.")
    model = s.model()
    print("Model:", model)
else:
    print("The hypothesis cannot be proven given the context.")

