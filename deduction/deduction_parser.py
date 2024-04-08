"""
"hypothesis_formula": "¬{C}{a}"
"sent1": "(Ex): (¬{D}x & ¬{E}x)"
"sent2": "(¬{AI}{a} & {HN}{a}) -> {A}{a}"
"sent3": "(x): ¬(¬{D}x & ¬{E}x) -> {A}{a}" 
"sent4": "(Ex): ¬({D}x & ¬{E}x)"
"sent5": "(x): ¬{A}x -> (¬{B}{b} & {C}{b})"
"sent6": "({AA}{a} & {AB}{a}) -> ¬{B}{a}"
"sent7": "(x): (¬{B}x & {A}x) -> {C}x"
"sent8": "({AA}{a} & {AB}{a})"
"sent9": "(Ex): ¬(¬{D}x & ¬{E}x)" 
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

        # 3 cases: 
        # simple -> {DN}, {B} 
        # implies -> (\u00ac{A} & {B}) -> \u00ac{DD} 
        # exists -> (Ex): \u00ac(\u00ac{AA}x & \u00ac{AB}x) 
        # for all -> (x): {A}x -> \u00ac(\u00ac{N}x & \u00ac{BF}x) 
        pass 

    def simple(self, clause):
        pass

    def implies(self, clause):  
        pass

    def conj(self, clause):
        # \u00ac{A} & {B}
        # And(Not(A(y)), B(y))
        # Convert to not(A(y)), B(y) -> Not(A(y)) & B(y)
        # split based on &'s -> [Not(A(y)), B(y)]
        # separate by comma -> And()
        pass

    def exists(self, clause):
        pass

    def forall(self, clause):
        pass
    