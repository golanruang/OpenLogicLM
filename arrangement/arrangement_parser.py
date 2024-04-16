from z3 import * 
from itertools import combinations
import re
import json

class Arrangement_Parser:
  def __init__(self, nl_logic):
    self.name_to_num = {}
    self.num_to_name = {}

    self.s = Solver()
    self.position = Function("pos", IntSort(), IntSort())
    self.f = open('arrangement_solver.py', 'w')
    self.z3_program = ""

    self.domain = {}
    self.variables = {} # var_name : list of possible values
    self.constraints = [] # list of strings representing the constraints
    self.query = {}
    self.var_num = 1
    self.solutions = []

    self.parse_logic(nl_logic)
    self.write_inits()
    self.create_variables()
    self.create_constraints()
    self.write_end()
    self.f.write(self.z3_program)
    
  def get_z3_program(self):
    return self.z3_program
  
  def get_solutions(self):
    return self.solutions

  def create_variables(self):
    """
    Variables:\ngreen_book [IN] [1, 2, 3, 4, 5]\nblue_book [IN] [1, 2, 3, 4, 5]\n
    white_book [IN] [1, 2, 3, 4, 5]\npurple_book [IN] [1, 2, 3, 4, 5]\n
    yellow_book [IN] [1, 2, 3, 4, 5]\n

    self.variables:  {'green_book': [1, 2, 3, 4, 5], 'blue_book': [1, 2, 3, 4, 5], 
                      'white_book': [1, 2, 3, 4, 5], 'purple_book': [1, 2, 3, 4, 5], 
                      'yellow_book': [1, 2, 3, 4, 5]}
    """
    min_num = min(self.num_to_name.keys())
    max_num = max(self.num_to_name.keys()) + 1
    
    for i in range(min_num, max_num):
      self.s.add(Or([self.position(i) == pos for pos in range(min_num, max_num)]))

    self.z3_program+="\tfor i in range(%d, %d):\n" % (min_num, max_num)

    
    s = ""
    min_val = min(self.num_to_name.keys())
    max_val = max(self.num_to_name.keys())
    for i in range(min_val, max_val + 1):
      s+="position(i)==%d, " % i

    s = s[:-2]
    self.z3_program += "\t\ts.add(Or(%s))\n" % s

  def create_constraints(self):
    """
    Constraints:\nblue_book > yellow_book ::: The blue book is to the right of the yellow book.\n
    white_book < yellow_book ::: The white book is to the left of the yellow book.\n
    blue_book == 4 ::: The blue book is the second from the right.\n
    purple_book == 2 ::: The purple book is the second from the left.\n

    self.constraints:  ['blue_book > yellow_book', 'white_book < yellow_book', 
                        'blue_book == 4', 'purple_book == 2', 
                        'AllDifferentConstraint([green_book, blue_book, white_book, purple_book, yellow_book])']
    """

    min_key = min(self.num_to_name.keys())
    max_key = max(self.num_to_name.keys()) + 1
    for comb in combinations(range(min_key, max_key), 2):
      self.s.add(self.position(comb[0])!= self.position(comb[1]))
      
    self.z3_program+="\tfor comb in combinations(range(%d, %d), 2):\n" % (min_key, max_key)
    self.z3_program+="\t\ts.add(position(comb[0])!= position(comb[1]))\n"

    for constraint in self.constraints:
      s1, sym, s2 = constraint.split(" ")
      self.write_constraint_helper(s1, s2, sym)

      converted = ""
      if s1 in self.name_to_num: 
        s1 = "position(%s)" % self.name_to_num[s1]
      
      if s2 in self.name_to_num:
        s2 = "position(%s)" % self.name_to_num[s2]

      converted+="%s %s %s" % (s1, sym, s2)
      self.z3_program+="\ts.add(%s)\n" % converted

  def write_constraint_helper(self, s1, s2, sym):
    s1_var, s2_var = False, False
    if s1 in self.name_to_num:
      s1_var = True
      s1 = self.name_to_num[s1]

    if s2 in self.name_to_num:
      s2_var = True
      s2 = self.name_to_num[s2]

    s1 = int(s1)
    s2 = int(s2)

    if sym == ">":
      if s1_var and s2_var: 
        self.s.add(self.position(s1) > self.position(s2))
      elif s2_var: 
        self.s.add(s1 > self.position(s2))
      elif s1_var:
        self.s.add(self.position(s1) > s2)
    elif sym == "<":
      if s1_var and s2_var: 
        self.s.add(self.position(s1) < self.position(s2))
      elif s2_var: 
        self.s.add(s1 < self.position(s2))
      elif s1_var:
        self.s.add(self.position(s1) < s2)
    elif sym == ">=":
      if s1_var and s2_var: 
        self.s.add(self.position(s1) >= self.position(s2))
      elif s2_var: 
        self.s.add(s1 >= self.position(s2))
      elif s1_var:
        self.s.add(self.position(s1) >= s2)
    elif sym == "<=":
      if s1_var and s2_var: 
        self.s.add(self.position(s1) <= self.position(s2))
      elif s2_var: 
        self.s.add(s1 <= self.position(s2))
      elif s1_var:
        self.s.add(self.position(s1) <= s2)
    elif sym == "==":
      if s1_var and s2_var: 
        self.s.add(self.position(s1) == self.position(s2))
      elif s2_var: 
        self.s.add(s1 == self.position(s2))
      elif s1_var:
        self.s.add(self.position(s1) == s2)
        
    elif sym == "!=": 
      if s1_var and s2_var:
        self.s.add(self.position(s1) != self.position(s2))
      elif s2_var: 
        self.s.add(s1 != self.position(s2))
      elif s1_var:
        self.s.add(self.position(s1) != s2)
    else:
      print(f"symbol {sym} not understood.")
  
  def find_possible_solutions(self):
    min_num = min(self.num_to_name.keys())
    max_num = max(self.num_to_name.keys()) + 1
    
    models = []
    while self.s.check() == sat:
      m = self.s.model()
      models.append(m)
      self.solutions.append(m)
      clauses = []
      for i in range(min_num, max_num):
        val_at_i = m.evaluate(self.position(i))
        clauses.append(self.position(i) == val_at_i)

      self.s.add(Not(And(clauses)))
    
    return models

  def parse_logic(self, nl_logic):
    """
    Domain: 
1: Shortest
4: Tallest
Variables: 
var_1 [1, 2, 3, 4]
var_2 [1, 2, 3, 4]
var_3 [1, 2, 3, 4]
var_4 [1, 2, 3, 4]
Constraints: 
var_1 < var_2 ::: var_1 is shorter than var_2
var_3 > var_4 ::: var_3 is taller than var_4
var_2 != 3 ::: var_2 is not the third tallest
var_4 != 1 ::: var_4 is not the shortest
"""
    curr_section = ""
    sections = [l.lstrip().strip() for l in nl_logic.split("\n") if l.strip()]

    for section in sections:
      if section == "Domain:":
        curr_section = "Domain:"
      elif section == "Variables:":
        curr_section = "Variables:"
      elif section == "Constraints:":
        curr_section = "Constraints:"
      elif section == "Query:":
        curr_section = "Query:"
      elif "Label:" in section:
        curr_section = "Label:"
      else:
        if curr_section == "Domain:":
          i, rep = section.split(":")
          self.domain[int(i)] = rep.strip()

        if curr_section == "Variables:":
          var_name, dom = section.split("[")
          var_name = var_name.strip()
          self.name_to_num[var_name] = self.var_num
          self.num_to_name[self.var_num] = var_name
          self.var_num+=1

          dom = dom.strip("]")
          pos_vals = [int(v.strip()) for v in dom.split(",")]

          self.variables[var_name] = pos_vals

        if curr_section == "Constraints:": 
          if ":::" in section:
            constraint = section.split(":::")[0]
          else:
            constraint = section
          self.constraints.append(constraint.strip())

  def write_inits(self):
    self.z3_program+="from z3 import *\n"
    self.z3_program+="from itertools import combinations\n"
    self.z3_program+="def solve_arrangement():\n"
    self.z3_program+="\ts = Solver()\n"
    self.z3_program+="\tposition = Function(\"pos\", IntSort(), IntSort())\n"
    
  def write_end(self):
    min_val = min(self.num_to_name.keys())
    max_val = max(self.num_to_name.keys())
    self.z3_program+="\tmodels = []\n"
    self.z3_program+="\twhile s.check() == sat:\n"
    self.z3_program+="\t\tm = s.model()\n"
    self.z3_program+="\t\tmodels.append(m)\n"
    self.z3_program+="\t\tclauses = []\n"
    self.z3_program+=f"\t\tfor i in range({min_val}, {max_val + 1}):\n"
    self.z3_program+="\t\t\tval_at_i = m.evaluate(position(i))\n"
    self.z3_program+="\t\t\tclauses.append(position(i) == val_at_i)\n\n"
    self.z3_program+="\t\ts.add(Not(And(clauses)))\n"
    self.z3_program+="\treturn models"
    
if __name__ == "__main__":
  s = """
Domain: 
1: Smallest 
7: Largest 

Variables: 
var_1 [1, 2, 3, 4, 5, 6, 7]
var_2 [1, 2, 3, 4, 5, 6, 7]
var_3 [1, 2, 3, 4, 5, 6, 7]
var_4 [1, 2, 3, 4, 5, 6, 7]
var_5 [1, 2, 3, 4, 5, 6, 7]
var_6 [1, 2, 3, 4, 5, 6, 7]
var_7 [1, 2, 3, 4, 5, 6, 7]

Constraints: 
var_2 > var_5 ::: var_2 is larger than var_5 
var_3 < var_1 ::: var_3 is smaller than var_1
var_4 < var_7 ::: var_4 is smaller than var_7
var_6 > var_1 ::: var_6 is larger than var_1
var_7 > var_3 ::: var_7 is larger than var_3
var_1 > var_7 ::: var_1 is larger than var_7
var_2 < var_6 ::: var_2 is smaller than var_6
var_1 == 4 ::: var_1 is the third smallest 
"""
  a = Arrangement_Parser(s)
  s = a.find_possible_solutions()
  print(f"possible solutions: {s}")
  
  
  # will LLAMA be able to generalize these to higher dimension arrangement problems?
  