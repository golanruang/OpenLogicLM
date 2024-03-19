"""
"raw_logic_programs": [
      "Domain:\n1: leftmost\n5: rightmost\n
      Variables:\ngreen_book [IN] [1, 2, 3, 4, 5]\nblue_book [IN] [1, 2, 3, 4, 5]\nwhite_book [IN] [1, 2, 3, 4, 5]\npurple_book [IN] [1, 2, 3, 4, 5]\nyellow_book [IN] [1, 2, 3, 4, 5]\n
      Constraints:\nblue_book > yellow_book ::: The blue book is to the right of the yellow book.\nwhite_book < yellow_book ::: The white book is to the left of the yellow book.\nblue_book == 4 ::: The blue book is the second from the right.\npurple_book == 2 ::: The purple book is the second from the left.\nAllDifferentConstraint([green_book, blue_book, white_book, purple_book, yellow_book]) ::: All books have different values.\n
      Query:\nA) green_book == 2 ::: The green book is the second from the left.\nB) blue_book == 2 ::: The blue book is the second from the left.\nC) white_book == 2 ::: The white book is the second from the left.\nD) purple_book == 2 ::: The purple book is the second from the left.\nE) yellow_book == 2 ::: The yellow book is the second from the left."
    ]

"""

from z3 import * 
from itertools import combinations

s=Solver()

position = Function("pos", IntSort(), IntSort())

name_to_num = {"green_book": 0, "blue_book":1, "white_book": 2, "purple_book": 3, "yellow_book": 4}
num_to_name = {0: "green_book", 1: "blue_book", 2: "white_book", 3: "purple_book", 4: "yellow_book"}

# green_book = 1, blue_book = 2, white_book = 3, purple_book = 4, yellow_book = 5

for i in range(1,6):
    s.add(Or(position(i)==1, position(i)==2, position(i)==3, position(i)==4, position(i)==5))
    # s.add(position(i) >= 1)
    # s.add(position(i) < 6)

# different books in every place
for comb in combinations(range(1,6), 2):
    s.add(position(comb[0])!= position(comb[1]))

s.add(position(2) > position(5))
s.add(position(3) < position(5))
s.add(position(2) == 4)
s.add(position(4) == 2)

if s.check() == z3.sat:
    print(s.model())
else:
	print("Solution does not exist.")