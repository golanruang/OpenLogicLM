import sys
sys.path.append('../')
from utils.openai_utils import OpenAIModel
from utils.config import api_key

from arrangement.arrangement_parser import Arrangement_Parser

import json
import os
import uuid

import argparse
import random

from datetime import date

class Arrangement_Pipeline:
    def __init__(self, args):
        self.templates = []
        self.num_data = 1

        self.datapoints = []
        self.data_per_template = 1 # for each template, generate n problems

        self.openai_api = OpenAIModel(api_key, args.model_name, args.stop_words, args.max_new_tokens)
        
        self.solutions = []

    def generate_template(self, n):
        template_path = "prompts/template_prompt.txt"
        try:
            with open(template_path, 'r') as file:
                contents = file.read()
                template = contents.replace('[[TEMPLATE]]', f'num_variables = {n}')
        except FileNotFoundError:
            print("File not found.")
        except Exception as e:
            print("An error occurred:", e)
            
        gpt_output = self.openai_api.generate(template, temperature=0.7)
        return gpt_output
    
    def generate_context(self, template):
        directory = 'prompts'
        file_path = os.path.join(directory, 'context_prompt.txt')

        file = open(file_path, 'r')
        prompt = file.read().replace('[[TEMPLATE]]', template)

        gpt_output = self.openai_api.generate(prompt, temperature=0.7, top_p=0.8)

        gpt_output=gpt_output.replace("Output:", "").strip()
        
        return gpt_output
    
    def prompt_parser(self, program):
        m = Arrangement_Parser(program)
        z3_program = m.get_z3_program()
        ans = m.get_ans()
        gpt_ans = m.get_gpt_ans()
        return z3_program, gpt_ans, ans
        
    def parse_domain(self, template):
        domain = {}
        lines = [line for line in template.split('\n') if line != '\n']
        
        for i in range(len(lines)): 
            if "Domain" not in lines[i]: 
                continue 
            
            for j in range(1, 3):
                val, desc = lines[i+j].split(':')
                val = val.lstrip().strip()
                desc = desc.lstrip().strip()
                domain[val] = desc 
        
        max_val = max(map(int, domain.keys()))
        return domain, max_val
    
    def parse_definitions(self, context):
        definitions = {}
        
        lines = [line.lstrip().strip() for line in context.split('\n') if line != '\n']
        
        for i in range(len(lines)):
            if lines[i][:4] != "var_":
                continue 
            
            var, defn = lines[i].split(':')
            var = var.lstrip().strip()
            defn = defn.lstrip().strip()
            definitions[var] = defn
            
        return definitions
        
    def convert_solutions(self, solutions, template, context, label):
        print("CONVERTING SOLUTIONS....")
        # get the domain 
        domain, num_variables = self.parse_domain(template)
        print(f"domain: {domain}")
        
        # get the definitions of the variables 
        definitions = self.parse_definitions(context)
        print(f"definitions: {definitions}")
                        
        context = [line for line in context.split('\n') if line.strip()]
        
        context, premises = context[0], context[1]
        
        n = len(solutions)
        
        solutions_input = ""
        solutions_input += f"{context}\n"
        solutions_input += f"{premises}\n\n"
        solutions_input += f"Domain:\n{1}: {domain['1']}\n{num_variables}: {domain[str(num_variables)]}\n\n"
        solutions_input += "Definitions:\n"
        for k, v in definitions.items(): 
            solutions_input += f"{k}: {v}\n"
        
        solutions_input += "\n"
        
        for i in range(n):
            solutions_input += f"Solution #{i+1}:\n"
            solution = str(solutions[i]).lstrip().strip()[1:][:-1]
            
            print(f"solution: {solution}")
            
            assignments = [assignment.lstrip().strip() for assignment in solution.split(',')]
                        
            for assignment in assignments: 
                var, pos = assignment.split('=')
                
                var = var.strip()
                pos = pos.lstrip()
                                
                solutions_input += f"{definitions[var]}: {pos}\n"
        
        solutions_input += f"\nLabel: {label}"
    
        return solutions_input      
    
    def parse_conclusion(self, conclusion):
        """Statement (English): Player Bella is the tallest among the three players.

        Statement (Logic): player_Bella == 3

        Analysis: 
        The statement is correct because in both solution #1 and solution #2, player_Bella is the tallest (3).
        """
        
        nl_conclusion = ""
        logic_conclusion = ""
        
        for line in conclusion.split('\n'):
            lowercase = line.lower()
            if lowercase.startswith('statement (english)'):
                nl_conclusion = line[21:]
                
            if lowercase.startswith('statement (logic)'):
                logic_conclusion = line[19:]
        
        return nl_conclusion, logic_conclusion
    
    def template_from_context(self, context):
        lower_context = context.lower() 
        s, e = lower_context.find('domain:'), lower_context.find('definitions:')
        return context[s:e].lstrip().strip()
    
    def generate_data(self, num_variables, label):
        query_path = 'prompts/query_prompt.txt'
        with open(query_path, 'r') as file: query_prompt = file.read()
        
        for i in range(self.num_data):
            while True: 
                # generate template until you get a template 
                print(f"GENERATING TEMPLATE...")
                template = self.generate_template(num_variables)

                a = Arrangement_Parser(template)
                a.parse_data() 
                a.create_base_constraints()
                solutions = a.find_possible_solutions()
                
                print(f"solutions: {solutions}")

                if 0 < len(solutions) < 20:
                    break 
                
            with open('template_test.txt', 'w') as file: file.write(template)
            
            print("GENERATING CONTEXT...")
            context = self.generate_context(template)
            # change context to be context and premises
            with open('context_test.txt', 'w') as file: file.write(context)
            
            # create new parser variable here
            new_template = self.template_from_context(context)
            
            a = Arrangement_Parser(new_template)
            a.parse_data()
            a.create_base_constraints()
            
            input_solutions = self.convert_solutions(solutions, template, context, label)
            
            query_prompt = query_prompt.replace('[[TEMPLATE]]', input_solutions)
            # print(f"query_prompt: {query_prompt}")
            with open('query_prompt_test.txt', 'w') as file: file.write(query_prompt)
            
            print("GENERATING QUERY...")
            conclusion = self.openai_api.generate(query_prompt)
            nl_conclusion, logic_conclusion = self.parse_conclusion(conclusion)
            
            with open('conclusion_test.txt', 'w') as file: file.write(logic_conclusion)
                                        
            answer = a.solve(logic_conclusion)
            print(f"statement: {logic_conclusion}")
            print(f"answer: {answer}")
            
            a.write_z3(logic_conclusion)
            
            z3_program = a.get_z3_program() 
            
            print(f"z3_program: \n{z3_program}")
        
            self.write_data(context, nl_conclusion, logic_conclusion, answer, z3_program)
        
        return
    
    def parse_template(self, template):
        """
        Domain: 
1: Least important 
7: Most important 

Variables: 
var_1 [1, 2, 3, 4, 5, 6, 7]
var_2 [1, 2, 3, 4, 5, 6, 7]
var_3 [1, 2, 3, 4, 5, 6, 7]
var_4 [1, 2, 3, 4, 5, 6, 7]
var_5 [1, 2, 3, 4, 5, 6, 7]
var_6 [1, 2, 3, 4, 5, 6, 7]
var_7 [1, 2, 3, 4, 5, 6, 7]

Constraints: 
var_2 > var_5 ::: var_2 is more important than var_5.
var_3 < var_1 ::: var_3 is less important than var_1.
var_6 == 4 ::: var_6 is the fourth most important.
var_7 == 7 ::: var_7 is the most important.
var_1 != 1 ::: var_1 is not the least important.
var_4 < var_6 ::: var_4 is less important than var_6.
var_5 > var_3 ::: var_5 is more important than var_3.
        """
        premises = []
        m = {'var_1': 'position(1)', 'var_2': 'position(2)', 'var_3': 'position(3)', 'var_4': 'position(4)',
            'var_5': 'position(5)', 'var_6': 'position(6)', 'var_7': 'position(7)', 'var_8': 'position(8)',
            'var_9': 'position(9)'}
        constraints = template.split('Constraints:')[1].lstrip().strip()

        constraints = constraints.split('\n')
        print(f"constraints: \n{constraints}")
        for constraint in constraints: 
            sym, desc = constraint.split(':::')
            for name in m.keys():
                if sym.find(name) != -1:
                    sym = sym.replace(name, m[name])
                    
            premises.append(f'{sym}')
            
        return premises
        
    def parse_context(self, context):
        # parse into context, premises, and constraints
        lower_context = context.lower()
        s, e = lower_context.find('constraints:'), lower_context.find('definitions')
        sym_premises = context[s:e]
        
        premise_list = sym_premises.split('\n')
        premise_list = list(filter(lambda x: x.strip(), premise_list))
        premise_list = premise_list[1:]
        output_premises = [] 
        
        for premise in premise_list: 
            statement = premise.split(':::')[0]
            output_premises.append(f"{statement}\n")
            
        sym_premises = ''.join(output_premises).lstrip().strip()
        # print(f"sym_premises: {sym_premises}")
        
        output_context = ""
        output_premise = ""
        
        # print(f"context: {context}")
        
        for line in context.split('\n'):
            lower_line = line.lower()
            if lower_line.startswith('context'):
                output_context = line[9:]
            if lower_line.startswith('premises'):
                output_premise = line[10:]
                
        return output_context, output_premise, sym_premises

    def parse_statement(self, statement):
        """
        Statement (English): The dish from the second food stall is spicier than the dish from the third food stall. 

        Statement (Logic): position(2) > position(3)
        """
        # print("PARSING STATEMENT")
        statement = statement.split('\n')
        statement = list(filter(lambda x: x.strip(), statement))
        english, logic = statement[0], statement[1]
        
        english = english.split(':')[1].lstrip().strip()
        logic = logic.split(':')[1].lstrip().strip()
        
        # print(f"english: {english}, logic: {logic}")
        
        return english, logic
    
    def write_data(self, context, nl_conclusion, logic_conclusion, label, z3):
        """
        id, type, context, nl_premises, sym_premises, nl_query, sym_query, label, z3_program
        """
        today = date.today()
        f = f'./data/{today}.json'
        
        output = {}
        output['id'] = str(uuid.uuid4())
        output['type'] = 'Arrangement'
        
        context, premises, sym_premises = self.parse_context(context)
        output['context'] = context
        output['nl_premises'] = premises
        output['sym_premises'] = sym_premises
        output['nl_query'] = nl_conclusion
        output['sym_query'] = logic_conclusion
        output['label'] = str(label)
        output['z3_program'] = z3
        
        if os.path.exists(f):
            # If the file exists, read existing JSON data from the file
            with open(f, "r") as file:
                data = json.load(file)
        else:
            # If the file doesn't exist, initialize with an empty list
            data = []
            
        data.append(output)
        
        with open(f, 'w') as file: 
            json.dump(data, file, indent=4)

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('--num_of_examples', type=int, default=5)
    parser.add_argument('--save_path', type=str, default='./fol_programs')
    parser.add_argument('--api_key', type=str)
    parser.add_argument('--model_name', type=str, default='text-davinci-003')
    parser.add_argument('--stop_words', type=str, default='------')
    parser.add_argument('--max_new_tokens', type=int, default=1024)
    parser.add_argument('--num_variables', type)                              # add arg for range of variables
    
    args = parser.parse_args()
    return args

if __name__ == '__main__':
    args = parse_args()
    args.model_name = 'gpt-4'
    args.api_key = api_key
    path = './gpt_generated_data/data.json'

    a = Arrangement_Pipeline(args)
    n = random.randint(3, 7)
    a.generate_data(n, True)