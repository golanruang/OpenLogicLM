from collections import defaultdict 
import json

import sys 
sys.path.append('../')
from utils.openai_utils import OpenAIModel
from utils.config import api_key

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
        self.openai_api = OpenAIModel(api_key, model_name='gpt-4', stop_words='------', max_new_tokens=1024)
        self.realized_variables = ""

    def get_hypothesis_sym(self): return self.hypothesis_sym
    def get_hypothesis_nl(self): return self.hypothesis_nl
    def get_context_sym(self): return self.context_sym
    def get_context_nl(self): return self.context_nl
    def get_variables(self): return self.variables

    def reset(self): 
        self.corpus = ""
        self.hypothesis_sym = ""
        self.hypothesis_nl = ""
        self.context_sym = {}
        self.context_nl = {}
        self.variables = set() 

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

        def find_x(formula):
            # return true if formula contains x 
            if formula.find("(x)") != -1 or formula.find("Ex") != -1: 
                self.variables.add('x')
            
        find_variables(self.corpus['hypothesis_formula'])
        find_variables(self.corpus['context_formula'])
        find_x(self.corpus['hypothesis_formula'])
        find_x(self.corpus['context_formula'])

        def sort_key(s):
            start = s.find('{')
            end = s.find('}')
            if s == s.lower(): 
                return (0, s[start+1:end])
            else:
                return (1, s[start+1:end])

        self.variables = sorted(self.variables, key=sort_key)

        formatted = " ".join(self.variables)
        print(f"variables: {formatted}")

    def parse_clauses(self):
        """
        takes corpus and appends all sentences in order (hypothesis first) to self.sentences
        'context_formula': 
        'sent1: (¬{AA}{a} & ¬{AB}{a}) -> {B}{b} sent2: (x): ¬({B}x & {D}x) -> ¬{D}x sent3: {D}{c} sent4: ¬{A}{c} -> ¬{C}{c} sent5: ¬{B}{b} sent6: ¬(¬{AA}{a} & ¬{AB}{a}) -> ¬{A}{c}'
        """
        print("in parse_clauses...")
        self.hypothesis_sym = self.corpus['hypothesis_formula']

        def find_sentences(context_formula):
            while context_formula.find("sent") != -1:
                start = context_formula.find("sent")
                colon_idx = context_formula.find(":")
                end = context_formula.find("sent", colon_idx)

                if end == -1: end = len(context_formula) - 1

                sent_num = context_formula[start : colon_idx]
                sentence = context_formula[colon_idx + 1 : end]
                self.context_sym[sent_num] = sentence

                context_formula = context_formula[end:]

        context_formula = self.corpus['context_formula']
        find_sentences(context_formula)
        print(f"context_formula: {self.context_sym}")

        return self.context_sym
    
    def call_gpt(self, prompt):
        return self.openai_api.generate(prompt)

    def realize_situation(self):
        """
        Use situation prompt and pass variables
        GPT-4 returns meaning of each variable -> save meaning in self.variables
        """

        with open('./prompts/situation_prompt.txt', 'r') as f: 
            prompt = f.read()

        var_str = " ".join(self.variables)
        print(f"var_str: {var_str}")
        prompt = prompt.replace('[[TEMPLATE]]', var_str)
        output = self.call_gpt(prompt)

        self.realized_variables = output
        print(f"self.realized_variables: {self.realized_variables}")
        
        return self.realized_variables
        
    def realize_clause(self):
        """
        Use realization prompt and realize the meaning of each sentence -> 
        clauses: {'sent1': ': (¬{AA}{a} & ¬{AB}{a}) -> {B}{b} ', 'sent2': ': (x): ¬({B}x & {D}x) -> ¬{D}x ', 'sent3': ': {D}{c} ', 'sent4': ': ¬{A}{c} -> ¬{C}{c} ', 'sent5': ': ¬{B}{b} ', 'sent6': ': ¬(¬{AA}{a} & ¬{AB}{a}) -> ¬{A}{c}'}
        """
        with open('./prompts/realization_prompt.txt', 'r') as f: 
            prompt = f.read()

        template = ""
        template += self.realized_variables + "\n"

        template += f"\"hypothesis\": \"{self.hypothesis_sym}\"\n"

        for k, v in self.context_sym.items():
            template += f"\"{k}\": \"{v.strip()}\"\n"

        prompt = prompt.replace('[[TEMPLATE]]', template)
        print(f"prompt: {prompt}")

        output = self.call_gpt(prompt)

        print(f"{output}")
        return output

if __name__ == "__main__":
    gen = DeductionGenerator()
    with open('test.txt', 'r') as f: 
        for line in f: 
            gen.init_new_corpus(line)
            gen.parse_variables()
            situation = gen.realize_situation()
            # print(f"\n{situation}")
            clauses = gen.parse_clauses() 
            # print(f"clauses: {clauses}")
            gen.realize_clause()    
