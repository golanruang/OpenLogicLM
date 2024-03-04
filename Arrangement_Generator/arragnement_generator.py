import random
import json
# from FOL_Generator.arrangement_parser import Arrangement_Parser
# from arrangement_solver import solve
dict={
    1:"first",
    2:"second",
    3:"third",
    4:"fourth",
    5:"fifth",
    6:"sixth",
    7:"seventh"
}

def generate_random_text(domain_range, num_variables):
    variable_values = {f"{i}_var": list(range(1, num_variables + 1)) for i in range(1, num_variables + 1)}

    # Generate random variable names
    variable_names = list(variable_values.keys())

    # Determine the number of constraints
    num_constraints = num_variables

    # Generate random constraints
    constraints = []
    for i in range(num_constraints):
        choice=random.randint(1,3)
        var1, var2 = random.sample(variable_names, 2)
        if choice==1:
            constraint = f"{var1} > {var2} ::: {var1} is to the right of {var2}."
        elif choice==2:
            constraint = f"{var1} < {var2} ::: {var1} is to the left of {var2}."
        else:
            num=random.randint(1,num_variables)
            constraint = f"{var1} == {num} ::: {var1} is the {dict[num]} from {domain_range[0]}."

        constraints.append(constraint)

    # Generate 5 queries (A, B, C, D, E)
    query = []
    for i, var in enumerate(variable_names[:5]):
        value = random.choice(variable_values[var])

        query.append(f"{chr(65 + i)}) {var} == {value} ::: The {var[0]} var is the {dict[value]} from the left.")

    domain_text = f"Domain:\n1: {domain_range[0]}\n{num_variables}: {domain_range[1]}\n"

    variables_text = "Variables:\n"
    for name, values in variable_values.items():
        variables_text += f"{name} [IN] {values}\n"

    constraints_text = "Constraints:\n"
    for constraint in constraints:
        constraints_text += f"{constraint}\n"

    query_text = "Query:\n"
    for condition in query:
        query_text += f"{condition}\n"

    generated_text = domain_text + variables_text + constraints_text + query_text

    return generated_text, constraint



# Example: Generate random text with 5 variables (adjust as needed)
random_text,constraint = generate_random_text(("oldest", "newest"), 5)
print(random_text)
# a=Arrangement_Parser(random_text)
# a.query_solver()



