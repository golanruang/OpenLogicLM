from z3 import *
from ply import lex, yacc
from Formula import FOL_Formula
from z3_predicate_parser import Z3_FOL_Predicate

"""
Original grammar:
S -> F | Q F
Q -> QUANT VAR | QUANT VAR Q
F -> '¬' '(' F ')' | '(' F ')' | F OP F | L
OP -> '⊕' | '∨' | '∧' | '→' | '↔'
L -> '¬' PRED '(' TERMS ')' | PRED '(' TERMS ')'
TERMS -> TERM | TERM ',' TERMS
TERM -> CONST | VAR
QUANT -> '∀' | '∃'
"""

"""
Revised grammar:
S -> F | QUANT VAR S
F -> '¬' '(' F ')' | '(' F ')' | F OP F | L
OP -> '⊕' | '∨' | '∧' | '→' | '↔'
L -> '¬' PRED '(' TERMS ')' | PRED '(' TERMS ')'
TERMS -> TERM | TERM ',' TERMS
TERM -> CONST | VAR
QUANT -> '∀' | '∃'
"""

class Z3_FOL_Formula:
    def __init__(self, fol_formula : FOL_Formula) -> None:
        self.tokens = ['QUANT', 'VAR', 'NOT', 'LPAREN', 'RPAREN', 'OP', 'PRED', 'COMMA', 'CONST']

        self.t_QUANT = r'∀|∃'
        self.t_NOT = r'¬'
        self.t_LPAREN = r'\('
        self.t_RPAREN = r'\)'
        self.t_OP = r'⊕|∨|∧|→|↔'
        self.t_COMMA = r','

        if len(fol_formula.variables) > 0:
            self.t_VAR = r'|'.join(list(fol_formula.variables))
        else:
            self.t_VAR = r'x'
        
        if len(fol_formula.predicates) > 0:
            self.t_PRED = r'|'.join(list(fol_formula.predicates))
        else:
            self.t_PRED = r'PRED'

        if len(fol_formula.constants) > 0:
            self.t_CONST = r'|'.join(list(fol_formula.constants))
        else:
            self.t_CONST = r'0'

        self.precedence = (
            ('left', 'OP'),
            ('right', 'NOT'),
        )

        self.t_ignore = ' \t'
        self.lexer = lex.lex(module=self)
        self.parser = yacc.yacc(module=self, write_tables=False, debug=False)
        
        self.z3_formula = self.parse(str(fol_formula))

    def t_error(self, t):
        print(f"Illegal character {t.value[0]}")
        t.lexer.skip(1)

    # S -> F
    def p_S_F(self, p):
        '''expr : F'''
        p[0] = p[1]

    # S -> QUANT VAR S
    def p_S_quantified_S(self, p):
        '''expr : QUANT VAR expr'''
        # var = Const(p[2], IntSort())
        if p[1] == "∀":
            p[0] = f"ForAll([{p[2]}], {p[3]})"
        elif p[1] == "∃":
            p[0] = f"Exists([{p[2]}], {p[3]})"

    # F -> '¬' '(' F ')'
    def p_F_not(self, p):
        '''F : NOT LPAREN F RPAREN'''
        p[0] = f"Not({p[3]})"

    # F -> '(' F ')'
    def p_F_paren(self, p):
        '''F : LPAREN F RPAREN'''
        p[0] = p[2]

    # F -> Var
    def p_F_var(self, p):
        '''F : VAR'''
        p[0] = p[1]

    # F -> F OP F
    def p_F_op(self, p):
        '''F : F OP F'''
        if p[2] == "⊕":
            p[0] = f"Xor({p[1]}, {p[3]})"
        elif p[2] == "∨":
            p[0] = f"Or({p[1]}, {p[3]})"
        elif p[2] == "∧":
            p[0] = f"And({p[1]}, {p[3]})"
        elif p[2] == "→":
            p[0] = f"Implies({p[1]}, {p[3]})"
        elif p[2] == "↔":
            p[0] = f"Iff({p[1]}, {p[3]})"

    # F -> L
    def p_F_L(self, p):
        '''F : L'''
        p[0] = p[1]

    # L -> '¬' PRED '(' TERMS ')'
    def p_L_not(self, p):
        '''L : NOT PRED LPAREN TERMS RPAREN'''
        p[0] = f"Not({p[2]}({p[4]}))"

    # L -> PRED '(' TERMS ')'
    def p_L_pred(self, p):
        '''L : PRED LPAREN TERMS RPAREN'''
        p[0] = f"{p[1]}({p[3]})"

    # TERMS -> TERM
    def p_TERMS_TERM(self, p):
        '''TERMS : TERM'''
        p[0] = p[1]

    # TERMS -> TERM ',' TERMS
    def p_TERMS_TERM_TERMS(self, p):
        '''TERMS : TERM COMMA TERMS'''
        p[0] = f"{p[1]}, {p[3]}"

    # TERM -> CONST
    def p_TERM_CONST(self, p):
        '''TERM : CONST'''
        p[0] = p[1]

    # TERM -> VAR
    def p_TERM_VAR(self, p):
        '''TERM : VAR'''
        p[0] = p[1]

    def p_error(self, p):
        print("Syntax error at '%s'" % p.value)

    def parse(self, s):
        return self.parser.parse(s, lexer=self.lexer)

if __name__ == "__main__":
    str_fol = '\u2203x \u2203y (Czech(x) \u2227 Book(y) \u2227 Author(x, y) \u2227 Publish(y, year1946))'
    str_fol = '\u2200x (Documentary(x) \u2192 (Film(x) \u2227 \u2203y (RealLifeEvent(y) \u2228 RealLifePerson(y)) \u2227 Documents(x, y)))'
    # str_fol = "\u2200x (Conductor(x) \u2192 (Material(x) \u2227 AllowsElectricCurrent(x) \u2227 MinimalResistance(x)))"
    fol_rule = FOL_Formula(str_fol)
    print(fol_rule)
    z3_rule = Z3_FOL_Formula(fol_rule)
    print(z3_rule.z3_formula)

    str_fol = 'Author(x, y)'
    fol_predicate = FOL_Formula(str_fol)
    z3_predicate = Z3_FOL_Predicate(fol_predicate)
    print(z3_predicate.z3_predicate)