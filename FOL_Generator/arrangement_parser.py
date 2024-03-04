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
from arrangement_solver import solve

class Arrangement_Parser:
  def __init__(self, nl_logic):
    print("initializing arrangement parser")
    self.name_to_num = {}
    self.num_to_name = {}

    self.s = Solver()
    self.f = open('arrangement_solver.py', 'w')

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
    self.query_solver()

  def create_domain(self):
    """
    "Domain:\n1: leftmost\n5: rightmost\n

    self.domain:  {1: 'leftmost', 5: 'rightmost'}
    """
    pass

  def create_variables(self):
    """
    Variables:\ngreen_book [IN] [1, 2, 3, 4, 5]\nblue_book [IN] [1, 2, 3, 4, 5]\n
    white_book [IN] [1, 2, 3, 4, 5]\npurple_book [IN] [1, 2, 3, 4, 5]\n
    yellow_book [IN] [1, 2, 3, 4, 5]\n

    self.variables:  {'green_book': [1, 2, 3, 4, 5], 'blue_book': [1, 2, 3, 4, 5], 
                      'white_book': [1, 2, 3, 4, 5], 'purple_book': [1, 2, 3, 4, 5], 
                      'yellow_book': [1, 2, 3, 4, 5]}
    """
    print("num_to_name: ", self.num_to_name)
    self.f.write("\tfor i in range(%d, %d):\n" % (min(self.num_to_name.keys()), max(self.num_to_name.keys()) + 1))

    
    s = ""
    min_val = min(self.num_to_name.keys())
    max_val = max(self.num_to_name.keys())
    for i in range(min_val, max_val + 1):
      s+="position(i)==%d, " % i

    s = s[:-2]
    self.f.write("\t\ts.add(Or(%s))\n" % s)

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
    print(self.name_to_num)
    for constraint in self.constraints:
      if "(" in constraint: # function, not boolean logic
        fcn = constraint.split("(")[0]
        if fcn == "AllDifferentConstraint":
          self.f.write("\tfor comb in combinations(range(%d, %d), 2):\n" % (min(self.num_to_name.keys()), max(self.num_to_name.keys()) + 1))
          self.f.write("\t\ts.add(position(comb[0])!= position(comb[1]))\n")

      else:
        s1, sym, s2 = constraint.split(" ")
        print("s1: %s, sym: %s, s2: %s" % (s1, sym, s2))
        converted = ""
        if s1 in self.name_to_num: 
          s1 = "position(%s)" % self.name_to_num[s1]
        
        if s2 in self.name_to_num:
          s2 = "position(%s)" % self.name_to_num[s2]

        converted+="%s %s %s" % (s1, sym, s2)

        self.f.write("\ts.add(%s)\n" % converted)
    print("s.add(constraint)")
    self.f.write("\ts.add(constraint)\n")

  def query_solver(self):
    # for q in self.query.keys():
    print("in query")
    for k in self.query.keys():
      pos_num, sym, pos = self.query[k].split(" ")
      if sym == ">":
        constraint = pos_num > pos
      if sym == "<":
        constraint = pos_num < pos
      if sym == "==":
        constraint = pos_num == pos
      # constraint = pos_num sym pos
      solved= solve(constraint)
      if solved:
        print("Solution: %s" % k)
        break

  def parse_logic(self, nl_logic):
    # sections = re.split(r'\n+(?=\s+[A-Z])', nl_logic)
    # print(sections)

    curr_section = ""
    sections = nl_logic.split("\n")

    for section in sections:
      if section == "Domain:":
        curr_section = "Domain:"
      elif section == "Variables:":
        curr_section = "Variables:"
      elif section == "Constraints:":
        curr_section = "Constraints:"
      elif section == "Query:":
        curr_section = "Query:"
      else:
        if curr_section == "Domain:":
          i, rep = section.split(":")
          # print("i: %s" % i)
          # print("rep: %s" % rep)
          self.domain[int(i)] = rep.strip()

        if curr_section == "Variables:":
          var_name, _, dom = section.split("[")
          var_name = var_name.strip()
          # print("section var name: %s" % var_name)
          # print("section dom: %s" % dom)
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
          # "Query:\nA) green_book == 2 ::: The green book is the second from the left.\nB) blue_book == 2 ::: The blue book is the second from the left.\nC) white_book == 2 ::: The white book is the second from the left.\nD) purple_book == 2 ::: The purple book is the second from the left.\nE) yellow_book == 2 ::: The yellow book is the second from the left."
          letter = section.split(")")[0]
          query = section.split(":::")[0][3:].strip()

          name = str(self.name_to_num[query.split(" ")[0]])
          symbol = query.split(" ")[1]
          pos = query.split(" ")[2]

          self.query[letter] = name + " " + symbol + " " + pos

          print("letter: %s" % letter)
          print("query: %s" % query)
          print("in query section")

    print("self.domain: ", self.domain)
    print("self.variables: ", self.variables)
    print("self.constraints: ", self.constraints)
    print("self.query: ", self.query)


  def write_inits(self):
    self.f.write("from z3 import *\n")
    self.f.write("from itertools import combinations\n")
    self.f.write("def solve(constraint):\n")
    self.f.write("\ts = Solver()\n")
    self.f.write("\tposition = Function(\"pos\", IntSort(), IntSort())\n")
    
  def write_end(self):
    self.f.write("\tif s.check() == z3.sat:\n")
    self.f.write("\t\tprint(s.model())\n")
    self.f.write("\t\treturn True\n")
    self.f.write("\telse:\n")
    self.f.write("\t\tprint(\"Solution does not exist.\")\n")
    self.f.write("\t\treturn False")
    
if __name__ == "__main__":

  data_path = './data.json'
  with open(data_path, 'r') as json_file:
    data = json.load(json_file)

  json_file.close()

  print(data)

  s = """Domain:\n1: oldest\n5: newest\nVariables:\nconvertible [IN] [1, 2, 3, 4, 5]\nsedan [IN] [1, 2, 3, 4, 5]\ntractor [IN] [1, 2, 3, 4, 5]\nminivan [IN] [1, 2, 3, 4, 5]\nlimousine [IN] [1, 2, 3, 4, 5]\nConstraints:\ntractor > minivan ::: The tractor is newer than the minivan.\ntractor < limousine ::: The tractor is older than the limousine.\nconvertible < sedan ::: The convertible is older than the sedan.\nconvertible == 2 ::: The convertible is the second-newest.\nAllDifferentConstraint([convertible, sedan, tractor, minivan, limousine]) ::: All vehicles have different values.\nQuery:\nA) convertible == 2 ::: The convertible is the second-newest.\nB) sedan == 2 ::: The sedan is the second-newest.\nC) tractor == 2 ::: The tractor is the second-newest.\nD) minivan == 2 ::: The minivan is the second-newest.\nE) limousine == 2 ::: The limousine is the second-newest."""
  a = Arrangement_Parser(s)


  # include options parsing 
  # output correct answer 

  # help with data generation part for FOL 
  # generate the fol problems using data from seed_dataset and prompting GPT-4 
  # link it with fol_parser.py to make sure the logic is correct
  
  # will LLAMA be able to generalize these to higher dimension arrangement problems?
  