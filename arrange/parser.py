from z3 import * 
from itertools import combinations 

class ArrangementParser:
    def __init__(self, data):
        self.s = Solver() 
        
        self.variables = {}
        self.domain = {}
        self.constraints = [] 
        self.num_variables = -1
        
        self.base_constraints = []
        self.symbolic_formulation = ""
        
    def init(self):
        self.s = Solver() 
        
        self.variables = {}
        self.domain = {}
        self.constraints = [] 
        self.num_variables = -1
        
        self.base_constraints = []

    def find_solutions(self, template):
        pass
    
    def solve(self, query):
        pass 
    
    def get_formulation(self):
        pass