"""
Generates a template like this one: 
Domain:
1: leftmost
5: rightmost
Variables:
var_1 integer [1, 2, 3, 4, 5]
var_2 integer [1, 2, 3, 4, 5]
var_3 integer [1, 2, 3, 4, 5]
var_4 integer [1, 2, 3, 4, 5]
var_5 integer [1, 2, 3, 4, 5]
Constraints:
var_2 > var_5 ::: var_2 is to the right of var_5.
var_3 < var_5 ::: var_2 is to the left of var_5.
var_2 == 4 ::: var_2 is the second from the right. 
var_4 == 2 ::: var_4 is the second from the left. 
"""
def get_hyperparams():
    """number of variables"""

def generate_template():
