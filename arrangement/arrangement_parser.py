from z3 import * 
from itertools import combinations 

import re 
import json 

class Arrangement_Parser:
    def __init__(self, data):
        self.data = data
        
        self.s = Solver() 
        self.z3_program = ""
        
        self.variables = {}     # 'racer_Alex' : racer_Alex -> z3 Function 
        self.domain = {}        # '1' : 'leftmost', '5': 'rightmost'
        self.constraints = []   # 'racer_Blake > racer_Erin'
        self.n = -1             # number of variables
        
        self.base_constraints = []
        self.solutions = []
        
    def get_z3_program(self):
        return self.z3_program
        
    def parse_data(self):
        data = self.data.split('\n')
        data = [x.strip().lstrip() for x in data if x]
        
        # print(f"data: \n{data}")
        curr_section = ""
        
        for section in data: 
            if section == 'Domain:':
                curr_section = 'Domain'
            elif section == 'Variables:':
                curr_section = 'Variables'
            elif section == 'Constraints:':
                curr_section = 'Constraints'
            else:
                if curr_section == 'Domain': self.parse_domain(section) 
                if curr_section == 'Variables': self.parse_vars(section)
                if curr_section == 'Constraints': self.parse_constraints(section)
                
        print(f"variables: \n{self.variables}")
        print(f"domain: \n{self.domain}")
        print(f"constraints: \n{self.constraints}")
                
    def parse_domain(self, section): 
        num, meaning = section.split(':')
        num = num.lstrip().strip()
        
        self.n = int(num)
        
        meaning = meaning.lstrip().strip()
        self.domain[num] = meaning
        
    def parse_vars(self, section):
        name, rge = section.split('[')
        name = name.lstrip().strip() 
        fcn = Function(name, IntSort())
        self.variables[name] = fcn 
        
    def parse_constraints(self, section):
        constraint, defn = section.split(':::')
        constraint = constraint.lstrip().strip() 
        self.constraints.append(constraint)
        
    def write_z3(self, conclusion):
        self.write_inits()
        self.write_functions()
        self.write_default_constraints()
        self.write_constraints()
        self.write_end(conclusion)
    
    def write_inits(self):
        self.z3_program+="from z3 import *\n"
        self.z3_program+="from itertools import combinations\n\n"
        self.z3_program+="constraints = []\n\n"

    def write_functions(self):
        for k, v in self.variables.items():
            self.z3_program += f"{k} = Function(\'{k}\', IntSort())\n"
            
        self.z3_program += '\n'
        obj_line = "objects = ["
        for k, v in self.variables.items():
            obj_line += f"{k}(), "
        
        obj_line = obj_line[:-2]
        obj_line += ']\n\n'
        self.z3_program += obj_line
    
    def write_constraints(self):
        self.create_default_constraints()
        
        self.z3_program += '\n'
        
        for constraint in self.constraints: 
            v1, sym, v2 = constraint.split(' ')
            var_1 = v1 in self.variables
            var_2 = v2 in self.variables
            
            s = 'constraints.append('
            if var_1: s += f"{v1}()"
            else: s += v1
            
            s += f" {sym} "
            
            if var_2: s += f"{v2}()"
            else: s += v2
            
            self.z3_program += f"{s})\n"
              
    def write_default_constraints(self):
        self.z3_program += "for obj in objects:\n"
        self.z3_program += "\tconstraints.append(obj >= 1)\n"
        self.z3_program += f"\tconstraints.append(obj <= {self.n})\n\n"
        
        self.z3_program += f"for i, j in combinations(range({self.n}), 2):\n"
        self.z3_program += "\tconstraints.append(objects[i] != objects[j])\n"
        
    def write_end(self, conclusion):
        for k, v in self.variables.items():
            conclusion = conclusion.replace(k, f"{k}()")
        
        self.z3_program += f'conclusion = {conclusion}\n\n'
        self.z3_program += 'def is_valid(constraints, conclusion):\n'
        self.z3_program += '\tsolver = Solver()\n'
        self.z3_program += '\tfor c in constraints: solver.add(constraints)\n'
        self.z3_program += '\tsolver.add(Not(conclusion))\n'
        self.z3_program += '\treturn solver.check() == unsat\n\n'
        self.z3_program += 'ans = is_valid(constraints, conclusion)'

    def create_base_constraints(self):
        self.create_default_constraints()
        self.create_constraints()
        
    def find_possible_solutions(self):
        s = Solver() 
        for c in self.base_constraints:
            s.add(c)
            
        models = []
        while s.check() == sat: 
            m = s.model()
            models.append(m)
            self.solutions.append(m)
            clauses = []
            for name, fcn in self.variables.items(): 
                val = m.evaluate(fcn())
                clauses.append(fcn() == val)
            
            s.add(Not(And(clauses)))
            
        return models
    
    def solve(self, query):
        print(f"query: {query}")
        print(f"self.variables: {self.variables}")
        s = Solver() 
        for c in self.base_constraints: s.add(c)
        
        c = self.str_to_constraint(query)

        s.add(Not(c))
        
        if s.check() == unsat: 
            return True 
        else: 
            return False
        
    def create_default_constraints(self):
        for name, fcn in self.variables.items():
            self.base_constraints.append(fcn() >= 1)
            self.base_constraints.append(fcn() <= self.n)
        
        variable_names = list(self.variables.keys())
        for i, j in combinations(range(self.n), 2):
            f1, f2 = variable_names[i], variable_names[j]
            self.base_constraints.append(self.variables[f1]() != self.variables[f2]())
               
    def create_constraints(self):
        for constraint in self.constraints:
            c = self.str_to_constraint(constraint)
            self.base_constraints.append(c)
    
    def str_to_constraint(self, s):
        v1, sym, v2 = s.split(' ')
        if v1 in self.variables: 
            v1 = self.variables[v1]()
        else: 
            v1 = int(v1)
            
        if v2 in self.variables: 
            v2 = self.variables[v2]()
        else:
            v2 = int(v2)
            
        if sym == ">=":
            
            return v1 >= v2
        elif sym == "<=":
            return(v1 <= v2)
        elif sym == "==":
            return(v1 == v2)
        elif sym == "!=":
            return(v1 != v2)
        elif sym == "<":
            return(v1 < v2)
        elif sym == ">":
            return(v1 > v2)
        else:
            print(f"symbol {sym} not understood")
        
    def write_to_file(self):
        f = open('new_solver.py', 'w')
        f.write(self.z3_program)
        
if __name__ == '__main__':
    data = """Domain:
1: leftmost
5: rightmost

Variables:
racer_Alex [1, 2, 3, 4, 5]
racer_Blake [1, 2, 3, 4, 5]
racer_Casey [1, 2, 3, 4, 5]
racer_Dana [1, 2, 3, 4, 5]
racer_Erin [1, 2, 3, 4, 5]

Constraints:
racer_Blake > racer_Erin ::: var_2 is to the right of var_5.
racer_Casey < racer_Erin ::: var_3 is to the left of var_5.
racer_Blake == 4 ::: var_2 is the second from the right. 
racer_Dana == 2 ::: var_4 is the second from the left. """
    conclusion = """racer_Alex >= racer_Blake"""
    a = Arrangement_Parser(data)
    a.parse_data()
    a.create_base_constraints() 
    models = a.find_possible_solutions()
    print(f"models: \n{models}")
    
    ans = a.solve(conclusion)
    print(f"ans: {ans}")
    
    a.write_z3(conclusion)
    a.write_to_file()