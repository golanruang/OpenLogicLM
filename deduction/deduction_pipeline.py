"""
Deduction Pipeline: 
1) Take a template generated by FLD-Generator (Morishita et al.)
2) Realize template using GPT-4
3) Parse formula into z3 
4) Output in format: [id, hypothesis_formula, context_formula, proofs_formula, hypothesis, context, proofs, proof_label, z3_program, ]

"hypothesis_formula": "{B}{a}"
"context_formula": "sent1: (\u00ac{AA}{aa} & {AB}{aa}) -> {B}{a} sent2: {AA}{b} -> \u00ac{A}{b} sent3: {BE}{b} sent4: \u00ac({AB}{b} & {D}{b}) sent5: \u00ac(\u00ac{A}{b} & {AA}{b}) sent6: {D}{aa} -> \u00ac{A}{aa} sent7: \u00ac(\u00ac{A}{aa} & {B}{aa}) -> {A}{a} sent8: \u00ac({D}{aa} & {A}{aa}) sent9: {B}{aa} sent10: (\u00ac{AA}{b} & {AB}{b}) -> {A}{aa} sent11: \u00ac{D}{cl} sent12: (\u00ac{A}{b} & {AA}{b}) -> {D}{aa} sent13: \u00ac(\u00ac{A}{b} & {D}{b}) sent14: ({C}{a} & {D}{a}) sent15: {D}{aa} -> (\u00ac{B}{aa} & {AA}{aa}) sent16: {B}{au} sent17: {A}{b} -> (\u00ac{AB}{b} & {AA}{b}) sent18: (x): {A}x -> (\u00ac{AA}x & {AB}x)"
"proofs_formula": ["sent18 -> int1: {A}{aa} -> (\u00ac{AA}{aa} & {AB}{aa});"]
"proof_label": "UNKNOWN"

"hypothesis_formula": "({A} & {C})"
"context_formula": "sent1: \u00ac{DN} sent2: \u00ac{B} sent3: (\u00ac{A} & {B}) -> \u00ac{DD} sent4: {C} sent5: \u00ac{JI} -> \u00ac({AJ} & {GF}) sent6: \u00ac({AA} & \u00ac{AB}) -> {B} sent7: \u00ac{A} -> \u00ac({AA} & \u00ac{AB}) sent8: {DH} sent9: {AS}"
"proofs_formula": ["void -> assump1: \u00ac{A}; sent7 & assump1 -> int1: \u00ac({AA} & \u00ac{AB}); int1 & sent6 -> int2: {B}; int2 & sent2 -> int3: #F#; [assump1] & int3 -> int4: {A}; int4 & sent4 -> hypothesis;"]
"proof_label": "PROVED"

Output:
"hypothesis": "The city park is open and the lighting system is functional.",
"context": "sent1: The gate is not locked. sent2: The walkways are not cleared. sent3: If the park is not open and the walkways are cleared, then the fountains are not working. sent4: The lighting system is functional. sent5: If the night patrol is not active, it means that the safety measures and the visibility are not adequate. sent6: If the recreational areas are not accessible and the night patrol is active, the walkways are cleared. sent7: If the park is not open, it means that the recreational areas are not accessible and the night patrol is active. sent8: The garden areas are maintained. sent9: The emergency exits are accessible.",
"proofs": ["void -> assump1: The park is not open; sent7 & assump1 -> int1: The recreational areas are not accessible and the night patrol is active; int1 & sent6 -> int2: The walkways are cleared; int2 & sent2 -> int3: #F#; [assump1] & int3 -> int4: The park is open; int4 & sent4 -> hypothesis;"]
"proof_label": "PROVED"
"""
class Deduction_Pipeline:
    def __init__(self) -> None:
        pass

    def get_corpus():
        pass

    def realize_prompt():
        pass

    def parse_to_z3():
        pass

if __name__ == "__main__":
    pass