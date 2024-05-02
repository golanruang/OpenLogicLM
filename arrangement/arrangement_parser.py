from z3 import * 
from itertools import combinations
import re
import json

"""
Create two solvers with question constraints 
Solver 1: Finds all possible solutions
Solver 2: Given the queries, checks which queries are correct 
  - Writes to z3_program to check all queries 
  
"""

class Arrangement_Parser:
  def __init__(self, nl_logic):
    self.name_to_num = {}
    self.num_to_name = {}

    self.s = Solver()       # solver to find all solutions 
    self.query_s = Solver() # solver to check all queries
    self.position = Function("pos", IntSort(), IntSort())
    self.f = open('arrangement_solver.py', 'w')
    self.z3_program = ""

    self.domain = {}
    self.variables = {} # var_name : list of possible values
    self.constraints = [] # list of strings representing the constraints
    self.query = {}
    self.var_num = 1
    self.solutions = []
    
    self.base_constraints = []

    self.parse_logic(nl_logic)
    self.write_inits()
    self.create_variables()
    self.create_constraints()
    
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
      self.base_constraints.append(Or([self.position(i) == pos for pos in range(min_num, max_num)]))

    self.z3_program+="for i in range(%d, %d):\n" % (min_num, max_num)

    
    s = ""
    min_val = min(self.num_to_name.keys())
    max_val = max(self.num_to_name.keys())
    for i in range(min_val, max_val + 1):
      s+="position(i)==%d, " % i

    s = s[:-2]
    self.z3_program += "\tclauses.append(Or(%s))\n\n" % s

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
      self.base_constraints.append(self.position(comb[0])!= self.position(comb[1]))
      # self.s.add(self.position(comb[0])!= self.position(comb[1]))
      # self.query_s.add(self.position(comb[0])!= self.position(comb[1]))
      
    self.z3_program+="for comb in combinations(range(%d, %d), 2):\n" % (min_key, max_key)
    self.z3_program+="\tclauses.append(position(comb[0])!= position(comb[1]))\n\n"

    for constraint in self.constraints:
      s1, sym, s2 = constraint.split(" ")
      self.write_constraint_helper(s1, s2, sym)

      converted = ""
      if s1 in self.name_to_num: 
        s1 = "position(%s)" % self.name_to_num[s1]
      
      if s2 in self.name_to_num:
        s2 = "position(%s)" % self.name_to_num[s2]

      converted+="%s %s %s" % (s1, sym, s2)
      self.z3_program+="clauses.append(%s)\n" % converted
      
    self.z3_program += "\n"

  def add_constraint(self, s1, s2, s1_var, s2_var, sym):
    """
    s1: integer
    s2: integer
    s1_var: T/F if s1 is a variable 
    s2_var: T/F if s2 is a variable
    sym: relationship symbol
    """
    if sym == ">":
      if s1_var and s2_var: 
        return self.position(s1) > self.position(s2)
      elif s2_var: 
        return s1 > self.position(s2)
      elif s1_var:
        return self.position(s1) > s2
    elif sym == "<":
      if s1_var and s2_var: 
        return self.position(s1) < self.position(s2)
      elif s2_var: 
        return s1 < self.position(s2)
      elif s1_var:
        return self.position(s1) < s2
    elif sym == ">=":
      if s1_var and s2_var: 
        return self.position(s1) >= self.position(s2)
      elif s2_var: 
        return s1 >= self.position(s2)
      elif s1_var:
        return self.position(s1) >= s2
    elif sym == "<=":
      if s1_var and s2_var: 
        return self.position(s1) <= self.position(s2)
      elif s2_var: 
        return s1 <= self.position(s2)
      elif s1_var:
        return self.position(s1) <= s2
    elif sym == "==":
      if s1_var and s2_var: 
        return self.position(s1) == self.position(s2)
      elif s2_var: 
        return s1 == self.position(s2)
      elif s1_var:
        return self.position(s1) == s2
    elif sym == "!=": 
      if s1_var and s2_var:
        return self.position(s1) != self.position(s2)
      elif s2_var: 
        return s1 != self.position(s2)
      elif s1_var:
        return self.position(s1) != s2
    else:
      print(f"symbol {sym} not understood.")
  
    
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
    
    c = self.add_constraint(s1, s2, s1_var, s2_var, sym)
    self.base_constraints.append(c)
    # self.s.add(c)
    
  def find_possible_solutions(self):
    # print(f"self.base_constraints: {self.base_constraints}")
    s = Solver() 
    for c in self.base_constraints: s.add(c)
    
    min_num = min(self.num_to_name.keys())
    max_num = max(self.num_to_name.keys()) + 1
    
    models = []
    while s.check() == sat:
      m = s.model()
      models.append(m)
      self.solutions.append(m)
      clauses = []
      for i in range(min_num, max_num):
        val_at_i = m.evaluate(self.position(i))
        clauses.append(self.position(i) == val_at_i)

      s.add(Not(And(clauses)))
    
    return models
  
  def check_answers(self, answers):
    """
    Statement (English): The first variety of pumpkin is the smallest. 

    Statement (Logic): position(1) == 1

    Analysis: 
    The statement is incorrect because in solution #2, the size of the first variety of pumpkin (2) is not the smallest. 

    To generate an incorrect query, find at least one solution where it is not satisfied. 
    To generate a correct query, make sure it is correct for ALL solutions.
    """
    # def find_second_occurence(string, substring):
    #     first_index = string.find(substring)
    #     if first_index != -1:  # If the substring is found at least once
    #         second_index = string.find(substring, first_index + 1)
    #         if second_index != -1:  # If the substring is found a second time
    #             return second_index
    #     return -1  # If the substring is not found a second time
    
    print("checking answers...")
    answers = answers.split('\n')
    
    for answer in answers: 
      if answer.find("(Logic):") == -1: 
        continue 
      
      logic = answer.split(':')[1].lstrip().strip()
      print(f"logic: {logic}")
      s1, sym, s2 = logic.split(" ")
      self.z3_program += f"conclusion = Not({s1} {sym} {s2})\n\n"
      
      pos_in_s1 = s1.find('position(')
      pos_in_s2 = s2.find('position(')
      s1_var, s2_var = False, False
      if pos_in_s1 != -1: 
        # if it's a pos(x)
        s1_var = True 
        paren = s1.find('position(') + 9
        s1 = s1[paren]
        
      if pos_in_s2 != -1: 
        s2_var = True 
        paren = s2.find('position(') + 9
        s2 = s2[paren]
        
      s1, s2 = int(s1), int(s2)
        
      print(f"s1: {s1}, s2: {s2}, s1_var: {s1_var}, s2_var: {s2_var}")
      
      s = Solver() 
      for c in self.base_constraints: s.add(c)
      c = self.add_constraint(s1, s2, s1_var, s2_var, sym)
      s.add(Not(c))
      
      if s.check() == unsat: 
        return True 
      else: 
        return False
    
    return None  
  
  def write_program_to_file(self):
    self.write_end()
    self.f.write(self.z3_program)
    return 

  def parse_logic(self, nl_logic):
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
    self.z3_program+="from itertools import combinations\n\n"
    self.z3_program+="position = Function(\"pos\", IntSort(), IntSort())\n"
    self.z3_program+="clauses = []\n\n"
    
  def write_end(self):
    self.z3_program+="""def is_valid(clauses, conclusion):
    solver = Solver()
    solver.add(clauses)
    solver.add(Not(conclusion))
    return solver.check() == unsat\n\n"""
    self.z3_program+="ans = is_valid(clauses, conclusion)"
    
if __name__ == "__main__":
  s = """
Domain: 
1: Lightest color
7: Darkest color

Variables: 
var_1 [1, 2, 3, 4, 5, 6, 7]
var_2 [1, 2, 3, 4, 5, 6, 7]
var_3 [1, 2, 3, 4, 5, 6, 7]
var_4 [1, 2, 3, 4, 5, 6, 7]
var_5 [1, 2, 3, 4, 5, 6, 7]
var_6 [1, 2, 3, 4, 5, 6, 7]
var_7 [1, 2, 3, 4, 5, 6, 7]

Constraints: 
var_1 < var_3 ::: var_1 is lighter than var_3
var_2 > var_5 ::: var_2 is darker than var_5
var_4 < var_6 ::: var_4 is lighter than var_6
var_7 > var_3 ::: var_7 is darker than var_3
var_5 == 2 ::: var_5 is the second lightest color
var_1 == 1 ::: var_1 is the lightest color
var_7 == 7 ::: var_7 is the darkest color
"""
  ans = """Statement (English): The first color is the lightest in the spectrum.

Statement (Logic): position(1) == 1

Analysis: 
The statement is correct because in all solutions, the lightness of the first color is 1, which is the lightest in the spectrum."""

  a = Arrangement_Parser(s)
  s = a.find_possible_solutions()

  print(f"ans: {a.check_answers(ans)}")
  a.write_program_to_file()  
  
  # will LLAMA be able to generalize these to higher dimension arrangement problems?
  