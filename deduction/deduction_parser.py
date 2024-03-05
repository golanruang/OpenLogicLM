"""
"hypothesis_formula": "({A} & {C})"
"context_formula": "sent1: \u00ac{DN} sent2: \u00ac{B} sent3: (\u00ac{A} & {B}) -> \u00ac{DD} sent4: {C} sent5: \u00ac{JI} -> \u00ac({AJ} & {GF}) sent6: \u00ac({AA} & \u00ac{AB}) -> {B} sent7: \u00ac{A} -> \u00ac({AA} & \u00ac{AB}) sent8: {DH} sent9: {AS}"
"proofs_formula": ["void -> assump1: \u00ac{A}; sent7 & assump1 -> int1: \u00ac({AA} & \u00ac{AB}); int1 & sent6 -> int2: {B}; int2 & sent2 -> int3: #F#; [assump1] & int3 -> int4: {A}; int4 & sent4 -> hypothesis;"]
"proof_label": "PROVED"

Output:
"hypothesis": "The city park is open and the lighting system is functional.",
"context": "sent1: The gate is not locked. sent2: The walkways are not cleared. sent3: If the park is not open and the walkways are cleared, then the fountains are not working. sent4: The lighting system is functional. sent5: If the night patrol is not active, it means that the safety measures and the visibility are not adequate. sent6: If the recreational areas are not accessible and the night patrol is active, the walkways are cleared. sent7: If the park is not open, it means that the recreational areas are not accessible and the night patrol is active. sent8: The garden areas are maintained. sent9: The emergency exits are accessible.",
"proofs": ["void -> assump1: The park is not open; sent7 & assump1 -> int1: The recreational areas are not accessible and the night patrol is active; int1 & sent6 -> int2: The walkways are cleared; int2 & sent2 -> int3: #F#; [assump1] & int3 -> int4: The park is open; int4 & sent4 -> hypothesis;"]
"proof_label": "PROVED"

Define variables like {AA}{aa} as an individual bool

returns result + z3_program
"""
import z3 

class Deduction_Parser:
    def __init__(self, nl_logic) -> None:
        self.variables = []                 # {AA}{aa} => "AAaa"
        self.clauses = []                   # z3 clauses
        self.solver = z3.Solver()
        self.z3_program = ""
        self.result = ""
        self.output = {}                    # keys = variables, clauses, z3_program, result
        self.history = []                   # list of dicts 

    def reset(self):
        # reset parser for new formula 
        self.variables.clear() 
        self.clauses.clear() 
        self.z3_program = ""
        self.result = ""
        self.output.clear() 

    def solve(self):
        # "context_formula": "sent1: \u00ac{DN} sent2: \u00ac{B} sent3: (\u00ac{A} & {B}) -> \u00ac{DD} sent4: {C} sent5: \u00ac{JI} -> \u00ac({AJ} & {GF}) sent6: \u00ac({AA} & \u00ac{AB}) -> {B} sent7: \u00ac{A} -> \u00ac({AA} & \u00ac{AB}) sent8: {DH} sent9: {AS}"
        # go through normal statements first, handle for all + there exists cases later
        # 3 cases: 
        # simple -> {DN}, {B} 
        # implies -> (\u00ac{A} & {B}) -> \u00ac{DD}
        # exists -> (Ex): \u00ac(\u00ac{AA}x & \u00ac{AB}x) (not too sure how to represent this. Does it even matter? should I just represent this as a clause?)
        # for all -> (x): {A}x -> \u00ac(\u00ac{N}x & \u00ac{BF}x) (parse through all variables containing A and add additional clauses)
        pass

    def simple(self, clause):
        pass

    def implies(self, clause):
        pass

    def exists(self, clause):
        pass

    def forall(self, clause):
        pass
    