from z3 import *
from ply import lex, yacc
from Formula import FOL_Formula

'''
Parser for FOL predicate
For example: Author(x, y)
Grammar:
Expr -> PRED '(' TERMS ')'
TERMS -> VAR | VAR ',' TERMS
'''
class Z3_FOL_Predicate:
    def __init__(self, fol_predicate : FOL_Formula) -> None:
        self.tokens = ['VAR', 'LPAREN', 'RPAREN', 'PRED', 'COMMA']

        self.t_LPAREN = r'\('
        self.t_RPAREN = r'\)'
        self.t_COMMA = r','
        self.t_VAR = r'[a-z]'
        predicate_name = list(fol_predicate.predicates)[0]
        self.t_PRED = r'{}'.format(predicate_name)

        self.t_ignore = ' \t'
        self.lexer = lex.lex(module=self)
        self.parser = yacc.yacc(module=self, write_tables=False, debug=False)
        
        self.z3_predicate = self.parse(str(fol_predicate))

    # Expr -> PRED '(' TERMS ')'
    def p_L_pred(self, p):
        '''Expr : PRED LPAREN TERMS RPAREN'''
        # p[0] = f"{p[1]}({p[3]})"
        # Movie = Function('Movie', _Object, BoolSort())
        p[0] = f'''{p[1]} = Function('{p[1]}', {p[3]}, BoolSort())'''

    # TERMS -> VAR
    def p_terms_var(self, p):
        '''TERMS : VAR'''
        p[0] = '_Object'
    
    # TERMS -> VAR ',' TERMS
    def p_terms_var_terms(self, p):
        '''TERMS : VAR COMMA TERMS'''
        # p[0] = f"{p[1]}, {p[3]}"
        p[0] = f"_Object, {p[3]}"

    def t_error(self, t):
        print(f"Illegal character {t.value[0]}")
        t.lexer.skip(1)

    def p_error(self, p):
        print("Syntax error at '%s'" % p.value)

    def parse(self, s):
        return self.parser.parse(s, lexer=self.lexer)

if __name__ == "__main__":
    str_fol = 'Author(x, y)'
    str_fol = 'Movie(x)'
    str_fol = 'HappyEnding(x, y, z)'
    fol_predicate = FOL_Formula(str_fol)
    z3_predicate = Z3_FOL_Predicate(fol_predicate)
    print(z3_predicate.z3_predicate)