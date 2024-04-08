"""
"raw_logic_programs": [
      "Domain:\n1: leftmost\n5: rightmost\n
      Variables:\ngreen_book [IN] [1, 2, 3, 4, 5]\nblue_book [IN] [1, 2, 3, 4, 5]\nwhite_book [IN] [1, 2, 3, 4, 5]\npurple_book [IN] [1, 2, 3, 4, 5]\nyellow_book [IN] [1, 2, 3, 4, 5]\n
      Constraints:\nblue_book > yellow_book ::: The blue book is to the right of the yellow book.\nwhite_book < yellow_book ::: The white book is to the left of the yellow book.\nblue_book == 4 ::: The blue book is the second from the right.\npurple_book == 2 ::: The purple book is the second from the left.\n
      AllDifferentConstraint([green_book, blue_book, white_book, purple_book, yellow_book]) ::: All books have different values.\n
      Query:\nA) green_book == 2 ::: The green book is the second from the left.\nB) blue_book == 2 ::: The blue book is the second from the left.\nC) white_book == 2 ::: The white book is the second from the left.\nD) purple_book == 2 ::: The purple book is the second from the left.\nE) yellow_book == 2 ::: The yellow book is the second from the left."
    ]
"""
from z3 import * 
from itertools import combinations
import re
import json

class Arrangement_Parser:
  def __init__(self, nl_logic):
    print("initializing parser...")
    self.name_to_num = {}
    self.num_to_name = {}

    self.s = Solver()
    self.position = Function("pos", IntSort(), IntSort())
    self.f = open('arrangement_solver.py', 'w')
    self.z3_program = ""
    self.gpt_label = ""
    self.ans = ""

    self.domain = {}
    self.variables = {} # var_name : list of possible values
    self.constraints = [] # list of strings representing the constraints
    self.query = {}
    self.var_num = 1

    self.parse_logic(nl_logic)
    self.write_inits()
    self.create_variables()
    self.create_constraints()
    self.write_end()
    self.f.write(self.z3_program)

  def create_variables(self):
    """
    Variables:\ngreen_book [IN] [1, 2, 3, 4, 5]\nblue_book [IN] [1, 2, 3, 4, 5]\n
    white_book [IN] [1, 2, 3, 4, 5]\npurple_book [IN] [1, 2, 3, 4, 5]\n
    yellow_book [IN] [1, 2, 3, 4, 5]\n

    self.variables:  {'green_book': [1, 2, 3, 4, 5], 'blue_book': [1, 2, 3, 4, 5], 
                      'white_book': [1, 2, 3, 4, 5], 'purple_book': [1, 2, 3, 4, 5], 
                      'yellow_book': [1, 2, 3, 4, 5]}
    """
    print("creating variables...")
    min_num = min(self.num_to_name.keys())
    max_num = max(self.num_to_name.keys()) + 1
    
    
    for i in range(min_num, max_num):
      # self.s.add(Or(self.position(i)==1, self.position(i)==2, self.position(i)==3, self.position(i)==4, self.position(i)==5))
      self.s.add(Or([self.position(i) == pos for pos in range(min_num, max_num)]))

    # self.f.write("\tfor i in range(%d, %d):\n" % (min_num, max_num))
    self.z3_program+="\tfor i in range(%d, %d):\n" % (min_num, max_num)

    
    s = ""
    min_val = min(self.num_to_name.keys())
    max_val = max(self.num_to_name.keys())
    for i in range(min_val, max_val + 1):
      s+="position(i)==%d, " % i

    s = s[:-2]
    # self.f.write("\t\ts.add(Or(%s))\n" % s)
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
    print("creating constraints...")

    min_key = min(self.num_to_name.keys())
    max_key = max(self.num_to_name.keys()) + 1
    for comb in combinations(range(min_key, max_key), 2):
      self.s.add(self.position(comb[0])!= self.position(comb[1]))
      
    self.z3_program+="\tfor comb in combinations(range(%d, %d), 2):\n" % (min_key, max_key)
    self.z3_program+="\t\ts.add(position(comb[0])!= position(comb[1]))\n"

    for constraint in self.constraints:
      # # print(f"constraint: {constraint}")
      # if "(" in constraint: # function, not boolean logic
      #   fcn = constraint.split("(")[0]
      #   if fcn == "AllDifferentConstraint":
      #     min_key = min(self.num_to_name.keys())
      #     max_key = max(self.num_to_name.keys()) + 1
      #     for comb in combinations(range(min_key, max_key), 2):
      #       self.s.add(self.position(comb[0])!= self.position(comb[1]))
      #     self.f.write("\tfor comb in combinations(range(%d, %d), 2):\n" % (min(self.num_to_name.keys()), max(self.num_to_name.keys()) + 1))
      #     self.f.write("\t\ts.add(position(comb[0])!= position(comb[1]))\n")
      #     self.z3_program+="\tfor comb in combinations(range(%d, %d), 2):\n" % (min(self.num_to_name.keys()), max(self.num_to_name.keys()) + 1)
      #     self.z3_program+="\t\ts.add(position(comb[0])!= position(comb[1]))\n"
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
    print("writing constraint helper...")
    print(f"s1: {s1}, s2: {s2}, sym: {sym}")
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
        print("self.s.add(self.position(s1) > self.position(s2))")
        self.s.add(self.position(s1) > self.position(s2))
      elif s2_var: 
        print("self.s.add(s1 > self.position(s2))")
        self.s.add(s1 > self.position(s2))
      elif s1_var:
        print("self.s.add(self.position(s1) > s2)")
        self.s.add(self.position(s1) > s2)
    elif sym == "<":
      if s1_var and s2_var: 
        print("self.s.add(self.position(s1) < self.position(s2))")
        self.s.add(self.position(s1) < self.position(s2))
      elif s2_var: 
        print("self.s.add(s1 < self.position(s2))")
        self.s.add(s1 < self.position(s2))
      elif s1_var:
        print("self.s.add(self.position(s1) < s2)")
        self.s.add(self.position(s1) < s2)
    elif sym == ">=":
      if s1_var and s2_var: 
        print("self.s.add(self.position(s1) >= self.position(s2))")
        self.s.add(self.position(s1) >= self.position(s2))
      elif s2_var: 
        print("self.s.add(s1 >= self.position(s2))")
        self.s.add(s1 >= self.position(s2))
      elif s1_var:
        print("self.s.add(self.position(s1) >= s2)")
        self.s.add(self.position(s1) >= s2)
    elif sym == "<=":
      if s1_var and s2_var: 
        print("self.s.add(self.position(s1) <= self.position(s2))")
        self.s.add(self.position(s1) <= self.position(s2))
      elif s2_var: 
        print("self.s.add(s1 <= self.position(s2))")
        self.s.add(s1 <= self.position(s2))
      elif s1_var:
        print("self.s.add(self.position(s1) <= s2)")
        self.s.add(self.position(s1) <= s2)
    elif sym == "==":
      if s1_var and s2_var: 
        print("self.s.add(self.position(s1) == self.position(s2))")
        self.s.add(self.position(s1) == self.position(s2))
      elif s2_var: 
        print("self.s.add(s1 == self.position(s2))")
        self.s.add(s1 == self.position(s2))
      elif s1_var:
        print("self.s.add(self.position(s1) == s2)")
        self.s.add(self.position(s1) == s2)
    else:
      print(f"symbol {sym} not understood.")

  def get_ans(self):
    return self.ans

  def get_z3_program(self):
    return self.z3_program
  
  def get_gpt_ans(self):
    return self.gpt_label
  
  def find_possible_solutions(self):
    print(f"finding possible solutions...")
    if self.s.check() == z3.sat:
      print(self.s.model())
      return True
    else:
      print("Solution does not exist.")
      return False

  def query_solver(self):
    print("querying solver...")
    for k in self.query.keys():
      pos_num, sym, pos = self.query[k].split(" ")
      if sym == ">":
        constraint = pos_num > pos
      if sym == "<":
        constraint = pos_num < pos
      if sym == "==":
        constraint = pos_num == pos
      self.s.push()
      self.s.add(constraint)
      if self.s.check() == sat:
        print(f"Answer {k} is possible.")

        model = self.s.model()
        print(f"Model: {model}")
        self.ans = k
        return k
      else:
        print(f"Answer {k} is not possible.")
      
      self.s.pop()
    
    return ""

  def parse_logic(self, nl_logic):

    curr_section = ""
    sections = [l.lstrip() for l in nl_logic.split("\n") if l.strip()]

    print("parsing logic...")

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
          # print("i: %s" % i)
          # print("rep: %s" % rep)
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
          constraint = section.split(":::")[0]
          self.constraints.append(constraint.strip())

        if curr_section == "Query:":
          letter = section.split(")")[0]
          query = section.split(":::")[0][3:].strip()
          if not letter or not query: 
            continue

          name = str(self.name_to_num[query.split(" ")[0]])
          symbol = query.split(" ")[1]
          pos = query.split(" ")[2]

          self.query[letter] = name + " " + symbol + " " + pos

  def write_inits(self):
    print("writing inits...")
    self.z3_program+="from z3 import *\n"
    self.z3_program+="from itertools import combinations\n"
    self.z3_program+="def solve():\n"
    self.z3_program+="\ts = Solver()\n"
    self.z3_program+="\tposition = Function(\"pos\", IntSort(), IntSort())\n"
    
  def write_end(self):
    print("writing ending...")
    self.z3_program+="\tif s.check() == z3.sat:\n"
    self.z3_program+="\t\tprint(s.model())\n"
    self.z3_program+="\t\treturn True\n"
    self.z3_program+="\telse:\n"
    self.z3_program+="\t\tprint(\"Solution does not exist.\")\n"
    self.z3_program+="\t\treturn False\n"
    self.z3_program+="solve()"
    
if __name__ == "__main__":
  print("in main...")
  # s = "Domain:\\n1: leftmost\\n5: rightmost\\nVariables:\\nrose [IN] [1, 2, 3, 4, 5]\\ntulip [IN] [1, 2, 3, 4, 5]\\ndaisy [IN] [1, 2, 3, 4, 5]\\nsunflower [IN] [1, 2, 3, 4, 5]\\nlily [IN] [1, 2, 3, 4, 5]\\nConstraints:\\ntulip > lily ::: The tulip is to the right of the lily.\\ndaisy < lily ::: The daisy is to the left of the lily.\\ntulip == 4 ::: The tulip is the second from the right.\\nsunflower == 2 ::: The sunflower is the second from the left.\\nAllDifferentConstraint([rose, tulip, daisy, sunflower, lily]) ::: All plants have different values.\\nQuery:\\nA) rose == 2 ::: The rose is the second from the left.\\nB) tulip == 2 ::: The tulip is the second from the left.\\nC) daisy == 2 ::: The daisy is the second from the left.\\nD) sunflower == 2 ::: The sunflower is the second from the left.\\nE) lily == 2 ::: The lily is the second from the left.\\n\\nLabel: D"
  s = """
Domain:
1: lightest
8: heaviest
Variables:
var_1 [1, 2, 3, 4, 5, 6, 7, 8]
var_2 [1, 2, 3, 4, 5, 6, 7, 8]
var_3 [1, 2, 3, 4, 5, 6, 7, 8]
var_4 [1, 2, 3, 4, 5, 6, 7, 8]
var_5 [1, 2, 3, 4, 5, 6, 7, 8]
var_6 [1, 2, 3, 4, 5, 6, 7, 8]
var_7 [1, 2, 3, 4, 5, 6, 7, 8]
var_8 [1, 2, 3, 4, 5, 6, 7, 8]
Constraints:
var_1 == 1 ::: var_1 is the lightest.
var_2 == 2 ::: var_2 is the second lightest.
var_3 > var_1 ::: var_3 is heavier than the lightest.
var_4 > var_3 ::: var_4 is heavier than var_3.
var_5 > var_4 ::: var_5 is heavier than var_4.
var_6 > var_5 ::: var_6 is heavier than var_5.
var_7 > var_6 ::: var_7 is heavier than var_6.
var_8 == 8 ::: var_8 is the heaviest.
var_7 == 7 ::: var_7 is the second heaviest.
var_3 < var_5 ::: var_3 is lighter than var_5.
var_2 < var_4 ::: var_2 is lighter than var_4.
  """
  a = Arrangement_Parser(s)
  a.find_possible_solutions()
  # z3_prog = a.get_z3_program()

  # print(f"z3 program: \n{z3_prog}")
  # help with data generation part for FOL 
  # generate the fol problems using data from seed_dataset and prompting GPT-4 
  # link it with fol_parser.py to make sure the logic is correct
  
  # will LLAMA be able to generalize these to higher dimension arrangement problems?
  