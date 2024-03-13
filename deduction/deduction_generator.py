from collections import defaultdict 
import json

class DeductionGenerator: 
    """
    Take in a FLD-Corpus ({"version": "0.2", "hypothesis": "the noncom is not synchronic but it is Mongol.", "hypothesis_formula": "(\u00ac{C}{c} & {D}{c})", "context": "sent1: the bigamist is a compline if the dun does not spring-clean heated and does not deprecate snarer. sent2: if that something is a compline and it is a Mongol is not right it is not a kind of a Mongol. sent3: that the noncom is a kind of a Mongol is not false. sent4: the noncom is not synchronic if it is not a Cygnus. sent5: the bigamist is not a compline. sent6: if the fact that the dun does not spring-clean heated and it does not deprecate snarer is wrong then the noncom is not a kind of a Cygnus.", "context_formula": "sent1: (\u00ac{AA}{a} & \u00ac{AB}{a}) -> {B}{b} sent2: (x): \u00ac({B}x & {D}x) -> \u00ac{D}x sent3: {D}{c} sent4: \u00ac{A}{c} -> \u00ac{C}{c} sent5: \u00ac{B}{b} sent6: \u00ac(\u00ac{AA}{a} & \u00ac{AB}{a}) -> \u00ac{A}{c}", "proofs": ["void -> assump1: Let's assume that that the dun does not spring-clean heated and does not deprecate snarer hold.; sent1 & assump1 -> int1: the fact that the bigamist is a compline is not incorrect.; int1 & sent5 -> int2: this is contradiction.; [assump1] & int2 -> int3: that the dun does not spring-clean heated and does not deprecate snarer is not true.; int3 & sent6 -> int4: the noncom is not a Cygnus.; int4 & sent4 -> int5: the noncom is not synchronic.; int5 & sent3 -> hypothesis;"], "proofs_formula": ["void -> assump1: (\u00ac{AA}{a} & \u00ac{AB}{a}); sent1 & assump1 -> int1: {B}{b}; int1 & sent5 -> int2: #F#; [assump1] & int2 -> int3: \u00ac(\u00ac{AA}{a} & \u00ac{AB}{a}); int3 & sent6 -> int4: \u00ac{A}{c}; int4 & sent4 -> int5: \u00ac{C}{c}; int5 & sent3 -> hypothesis;"], "negative_hypothesis": "the Napoleon is not Mongol.", "negative_hypothesis_formula": "\u00ac{D}{ic}", "negative_proofs": ["sent2 -> int6: the Napoleon is not a kind of a Mongol if that it is a compline and it is a Mongol is wrong.;"], "negative_original_tree_depth": 4, "original_tree_depth": 6, "depth": 6, "num_formula_distractors": 1, "num_translation_distractors": 0, "num_all_distractors": 1, "proof_label": "PROVED", "negative_proof_label": "UNKNOWN", "world_assump_label": "PROVED", "negative_world_assump_label": "UNKNOWN"})
    and store the hypothesis formula, clause sentences, and variables 
    use the situation prompt to generate a meaning for every variable 
    use the realization prompt to generate a meaning for every sentence + hypothesis 
    return the nl interpretation of a corpus 
    """
    def __init__(self):
        self.corpus = {}
        self.hypothesis_sym  = ""
        self.hypothesis_nl = ""
        self.context_sym = {}               # sent2 (key): (x): \u00ac({B}x & {D}x) (val)
        self.context_nl = {}                # sent2 (key): "For any element in the garden, if it is not newly planted and blooming, then it is not blooming." (val)
        self.variables = set() 

    def get_hypothesis_sym(self): return self.hypothesis_sym
    def get_hypothesis_nl(self): return self.hypothesis_nl
    def get_context_sym(self): return self.context_sym
    def get_context_nl(self): return self.context_nl
    def get_variables(self): return self.variables

    def reset(self): 
        self.corpus = ""
        self.hypothesis_sym = ""
        self.hypothesis_nl = ""
        self.context_sym.clear() 
        self.context_nl.clear() 
        self.variables.clear() 

    def init_new_corpus(self, corpus):
        """
        input: corpus (str)
        clears saved stuff + initializes corpus
        """
        self.reset() 
        self.corpus = json.loads(corpus) 

    def parse_variables(self):
        """
        takes corpus and appends all variables (lowercase first) to self.variables
        """
        def find_variables(formula):
            # self.corpus["hypothesis_formula"] = (¬{C}{c} & {D}{c})
            while formula.find('{') != -1:
                start = formula.find('{')
                end = formula.find('}')
                if formula[start-1] == "¬":
                    start -= 1
                self.variables.add(formula[start:end+1])
                formula = formula[end+1:]
            
        find_variables(self.corpus['hypothesis_formula'])
        find_variables(self.corpus['context_formula'])

        def sort_key(s):
            start = s.find('{')
            end = s.find('}')
            if s == s.lower(): 
                return (0, s[start+1:end])
            else:
                return (1, s[start+1:end])

        self.variables = sorted(self.variables, key=sort_key)

        print(f"variables: {self.variables}")

    def parse_clauses(self):
        """
        takes corpus and appends all sentences in order (hypothesis first) to self.sentences
        """
        pass

    def realize_situation(self):
        """
        Use situation prompt and pass variables
        GPT-4 returns meaning of each variable -> save meaning in self.variables
        """
        with open('./prompts/realization_prompt.txt', 'r') as f: 
            prompt = f.read()
        
        print(f"prompt: {prompt}")
        

    def realize_clause(self):
        """
        Use realization prompt and realize the meaning of each sentence -> 
        """
        pass

if __name__ == "__main__":
    gen = DeductionGenerator()
    with open('test.txt', 'r') as f: 
        for line in f: 
            gen.init_new_corpus(line)
            gen.parse_variables()
            gen.realize_situation()
    # gen.realize_clause()
    
