from fol_generator import Direct_FOL_Problem_Generator, parse_args
from fol_parser import FOL_Parser
from config import api_key
from datetime import date
from z3_program_parser import Z3_FOL_Program
from collections import defaultdict

import json

class FOL_Pipeline:
    
    """
    call parse_args(), run the generator, verify generated problems
    {'id', 'premises', 'conclusion', 'fol_premises', 'fol_conclusion', 'z3_program', 'label'}
    premises could be a list to store all premises in natural language. fol_premises could be a list to save all premises in FOL forms.
    """

    def __init__(self):
        """
        generate, parse, convert to z3 to check if label is correct, write output
        """
        self.output = defaultdict(list)
        self.fol_parser = FOL_Parser()
        self.fol_generator = Direct_FOL_Problem_Generator(args)

    def generate(self, args):
        self.fol_generator.batch_logic_program_generation()

    def write(self, datapts):
        today = date.today()
        f_name = "./verified_FOL/%s_fol.json" % today

        with open(f_name, 'w') as json_file:
            json.dump(datapts, json_file, indent=4)

    def verify_and_write(self, file_path):
        with open(file_path, 'r') as json_file:
            data = json.load(json_file)

        processed_data = []
        for entry in data:
            self.output = defaultdict(list)
            self.verify(entry)
            processed_data.append(self.output)

        self.write(processed_data)

    def verify(self, datapt):
        """
        [
        {
            "id": "ae4ca0d8-22ae-45e3-9354-2e2c84900fe8",
            "seed_sent": "All birds have wings and feathers.",
            "seed_fol": "∀x (Bird(x) → (HasWings(x) ∧ HasFeathers(x)))",
            "raw_fol_problem": [
            "Sentence: Penguins are birds.\nFOL: ∀x (Penguin(x) → Bird(x))\n\nSentence: Penguins do not fly.\nFOL: ∀x (Penguin(x) → ¬Fly(x))\n\nSentence: If a bird can fly, it has wings.\nFOL: ∀x ((Bird(x) ∧ Fly(x)) → HasWings(x))\n\nQuery: Penguins have wings.\nFOL: ∀x (Penguin(x) → HasWings(x))\n\nLabel: TRUE"
            ]
        }
        ]

        id: "ae4ca0d8-22ae-45e3-9354-2e2c84900fe8"
        premises: All birds have wings and feathers. Penguins are birds. Penguins do not fly. If a bird can fly, it has wings.
        conclusion: Penguins have wings.
        fol_premises: ∀x (Bird(x) → (HasWings(x) ∧ HasFeathers(x))) ∀x (Penguin(x) → Bird(x)) ∀x (Penguin(x) → ¬Fly(x)) ∀x ((Bird(x) ∧ Fly(x)) → HasWings(x))
        fol_conclusion: ∀x (Penguin(x) → HasWings(x))
        z3_program: 'output z3 program from z3_program_parser here'
        label: "TRUE"

        Takes in one data point, checks if it's a valid FOL problem, converts it to z3, checks if labels matches z3 output. 
        If true, return {'id', 'premises', 'conclusion', 'query', 'fol_premises', 'fol_conclusion', 'z3_program', 'label'}
        NOTE: conclusion? Doesn't really exist. did not add. 
        Else, return None
        """
        # datapt = {
        #     "id": "ae4ca0d8-22ae-45e3-9354-2e2c84900fe8",
        #     "seed_sent": "All birds have wings and feathers.",
        #     "seed_fol": "∀x (Bird(x) → (HasWings(x) ∧ HasFeathers(x)))",
        #     "raw_fol_problem": [
        #     "Sentence: Penguins are birds.\nFOL: ∀x (Penguin(x) → Bird(x))\n\nSentence: Penguins do not fly.\nFOL: ∀x (Penguin(x) → ¬Fly(x))\n\nSentence: If a bird can fly, it has wings.\nFOL: ∀x ((Bird(x) ∧ Fly(x)) → HasWings(x))\n\nQuery: Penguins have wings.\nFOL: ∀x (Penguin(x) → HasWings(x))\n\nLabel: TRUE"
        #     ]
        # }

        print(f"datapt: {datapt}")
        self.output['id'] = datapt['id']
        # output['premises'].append(datapt["seed_sent"])
        # output['fol_premises'].append(datapt['seed_fol'])
        self.parse_raw_fol(datapt["raw_fol_problem"])

        self.parse_preds()

        pass_to_z3_parser = self.parse_for_z3_parser()

        z3_program = Z3_FOL_Program(pass_to_z3_parser)
        answer = z3_program.execute()
        self.output['label'] = answer
        self.output['z3_program'] = z3_program.z3_program

    def parse_raw_fol(self, raw_fol):
        """
        input: raw_fol_problem attribute of datapt
        "Sentence: Penguins are birds.\nFOL: ∀x (Penguin(x) → Bird(x))\n\n
        Sentence: Penguins do not fly.\nFOL: ∀x (Penguin(x) → ¬Fly(x))\n\n
        Sentence: If a bird can fly, it has wings.\nFOL: ∀x ((Bird(x) ∧ Fly(x)) → HasWings(x))\n\n
        Query: Penguins have wings.\nFOL: ∀x (Penguin(x) → HasWings(x))\n\n
        Label: TRUE"
        output: {
            D nl_premises: nl premises, 
            D fol_premises: fol_premises,
            D predicates: ['Movie(x)', 'HappyEnding(x)'], 
            clauses: ['∃x (Movie(x) → ¬HappyEnding(x))', 'Movie(titanic)', '¬HappyEnding(titanic)', 'Movie(lionKing)', 'HappyEnding(lionKing)']
            D nl_query: query,
            D fol_query: fol_query, 
            nl_conclusion: nl_conclusion
            fol_conclusion: '∃x (Movie(x) ∧ ¬HappyEnding(x))'
            D label: 'TRUE' (check if z3 program output matches existing label)
        }

        TODO: doesn't support clauses with more than one parameter
        """
        sections = raw_fol[0].split("\n")
        sections = list(filter(None, sections))
        predicates = set()

        QUERY_FOL = False

        # print("sections: %s" % sections)
        for section in sections:

            section_type, content = section.split(":")
            content = content.strip()

            if QUERY_FOL: 
                self.output["fol_query"] = content
                QUERY_FOL = False
            elif section_type.lower() == "sentence": 
                self.output["nl_premises"].append(content)
            elif section_type.lower() == "fol":
                self.output["fol_premises"].append(content)
                # predicate_parsed = content.split("x")
                # for entry in predicate_parsed: 
                #     if entry[-1] == "(":
                #         pred = ''.join(char for char in entry if char.isalpha())
                #         # print(f"pred: {pred}")
                #         formatted_pred = pred + "(x)"
                #         predicates.add(formatted_pred)
            elif section_type.lower() == "query":
                self.output["nl_query"] = content
                QUERY_FOL = True
            # NOTE: should output['label'] be the label of the gpt or z3 program? 
            elif section_type.lower() == "label":
                self.output["label"] = content
            else:
                print("section_title not recognized")
        
        self.output["predicates"] = list(predicates)
        # print("\noutput: %s" % output)

    def parse_preds(self):
        # use fol_parser to check if it's a valid FOL program
        predicates = set()

        for statement in self.output["fol_premises"]:
            tree = self.fol_parser.parse_text_FOL_to_tree(statement)
            isFOL, lvars, consts, preds = self.fol_parser.symbol_resolution(tree)
            # if not isFOL: 
            #     print(f"statement: {statement}")
            #     raise ValueError("isFOL is False. Ending the program.")
            
            for pred in preds:
                predicates.add(pred + "(x)")

        self.output['predicates'] = list(predicates)

    def parse_for_z3_parser(self):
        """
        input: "Sentence: Penguins are birds.\nFOL: ∀x (Penguin(x) → Bird(x))\n\nSentence: Penguins do not fly.\nFOL: ∀x (Penguin(x) → ¬Fly(x))\n\nSentence: If a bird can fly, it has wings.\nFOL: ∀x ((Bird(x) ∧ Fly(x)) → HasWings(x))\n\nQuery: Penguins have wings.\nFOL: ∀x (Penguin(x) → HasWings(x))\n\nLabel: TRUE"
        output: '\u2200x (Athlete(x) \u2227 WinsGold(x, olympics) \u2192 OlympicChampion(x))'
        '∀x (Penguin(x) → Bird(x)) ∀x (Penguin(x) → ¬Fly(x)) ∀x ((Bird(x) ∧ Fly(x)) → HasWings(x))'
        """
        pass_to_z3_parser = {}

        pass_to_z3_parser['predicates'] = self.output['predicates']
        pass_to_z3_parser['clauses'] = self.output['fol_premises']
        pass_to_z3_parser['conclusion'] = self.output['fol_query']
        
        return pass_to_z3_parser


if __name__ == "__main__":
    args = parse_args()

    args.num_of_examples = 2
    args.model_name = 'gpt-4'
    args.api_key = api_key

    p = FOL_Pipeline()
    p.generate(args)
    
    # file_path is data to read from 
    p.verify_and_write(file_path='./fol_programs/fol_direct_generation_gpt-4.json')