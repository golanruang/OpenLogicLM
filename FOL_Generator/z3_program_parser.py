from z3 import *
from z3_formula_parser import Z3_FOL_Formula
from z3_predicate_parser import Z3_FOL_Predicate
from Formula import FOL_Formula
import func_timeout

'''
Example program:
predicates:
    Movie(x)
    HappyEnding(x)
clauses (facts & rules):
    ¬∀x (Movie(x) → HappyEnding(x))
    Movie(titanic)
    ¬HappyEnding(titanic)
    Movie(lionKing)
    HappyEnding(lionKing)
conclusion:
    ∃x (Movie(x) ∧ ¬HappyEnding(x))
label: TRUE
'''

def safe_execute(code_string: str, keys=None):
    def execute(x):
        try:
            exec(x)
            locals_ = locals()
            if keys is None:
                return locals_.get('ans', None)
            else:
                return [locals_.get(k, None) for k in keys]
        except Exception as e:
            # print error message
            print(e)
            return None
    try:
        ans = func_timeout.func_timeout(5, execute, args=(code_string,))
    except func_timeout.FunctionTimedOut:
        ans = None

    return ans

class Z3_FOL_Program:
    def __init__(self, fol_program:dict) -> None:
        self.fol_program = fol_program
        self.header = ['from z3 import *', '\n', "_Object = DeclareSort('Object')"]
        self.tail = ['def is_valid(clauses, conclusion):', '\tsolver = Solver()', '\tsolver.add(clauses)', '\tsolver.add(Not(conclusion))', '\treturn solver.check() == unsat', '\n', 'ans = is_valid(clauses, conclusion)']
        self.parse_program()

    def _extract_all_variables(self) -> list:
        variables = set()
        for fol in self.clauses + [self.conclusion]:
            for variable in fol.variables:
                variables.add(variable)
        return list(variables)
    
    def _extract_all_constants(self) -> list:
        constants = set()
        for fol in self.clauses + [self.conclusion]:
            for constant in fol.constants:
                constants.add(constant)
        return list(constants)

    def _generate_z3_variables(self) -> list:
        z3_variables = []
        for variable in self.variables:
            z3_variable = f"{variable} = Const('{variable}', _Object)"
            z3_variables.append(z3_variable)
        return z3_variables
    
    def _generate_z3_constants(self) -> list:
        z3_constants = []
        for constant in self.constants:
            z3_constant = f"{constant} = Const('{constant}', _Object)"
            z3_constants.append(z3_constant)
        return z3_constants

    def parse_program(self):
        # parse each statement into FOL formula
        self.predicates = []
        for predicate in self.fol_program['predicates']:
            fol_predicate = FOL_Formula(predicate)
            self.predicates.append(fol_predicate)

        self.clauses = []
        for clause in self.fol_program['clauses']:
            fol_clause = FOL_Formula(clause)
            self.clauses.append(fol_clause)

        self.conclusion = FOL_Formula(self.fol_program['conclusion'])

        # extract all variables and constants
        self.variables = self._extract_all_variables()
        self.constants = self._extract_all_constants()

        # generate z3 variables and constants
        self.z3_variables = self._generate_z3_variables()
        self.z3_constants = self._generate_z3_constants()

        # parse each FOL formula into Z3 formula
        self.z3_predicates = []
        for predicate in self.predicates:
            z3_predicate = Z3_FOL_Predicate(predicate)
            self.z3_predicates.append(z3_predicate.z3_predicate)

        self.z3_clauses = []
        for clause in self.clauses:
            z3_clause = Z3_FOL_Formula(clause)
            self.z3_clauses.append(z3_clause.z3_formula)

        self.z3_conclusion = Z3_FOL_Formula(self.conclusion).z3_formula

        # generate z3 program
        self.z3_program = self.header
        self.z3_program += self.z3_variables
        self.z3_program += ['\n']
        self.z3_program += self.z3_constants
        self.z3_program += ['\n']
        self.z3_program += self.z3_predicates
        self.z3_program += ['\n', 'clauses = []']
        for clause in self.z3_clauses:
            self.z3_program.append(f'clauses.append({clause})')
        self.z3_program += ['\n']
        self.z3_program.append(f'conclusion = {self.z3_conclusion}')
        self.z3_program += ['\n']
        self.z3_program += self.tail

        self.z3_program = '\n'.join(self.z3_program)

    def execute(self):
        answer = safe_execute(self.z3_program)
        return answer

if __name__ == '__main__':
    # '∃x (Movie(x) → ¬HappyEnding(x))'
    # '¬∀x (Movie(x) → HappyEnding(x))'
    data_example = {
        'predicates': ['Movie(x)', 'HappyEnding(x)'],
        'clauses': ['∃x (Movie(x) → ¬HappyEnding(x))', 'Movie(titanic)', '¬HappyEnding(titanic)', 'Movie(lionKing)', 'HappyEnding(lionKing)'],
        'conclusion': '∃x (Movie(x) ∧ ¬HappyEnding(x))',
        'label': 'TRUE' 
    }

    data_example = {
        'predicates': ['HasWings(x)', 'Fly(x)', 'Penguin(x)', 'Bird(x)'], 
        'clauses': ['∀x (Penguin(x) → Bird(x))', '∀x (Penguin(x) → ¬Fly(x))', '∀x ((Bird(x) ∧ Fly(x)) → HasWings(x))'],
        'conclusion': '∀x (Penguin(x) → HasWings(x))',
        'label': 'TRUE',
    }


    z3_program = Z3_FOL_Program(data_example)
    print(z3_program.z3_program)

    answer = z3_program.execute()
    print(answer)