"""
This arrangement pipeline takes in a template and 
1) generates a context for the problem using gpt 
2) generates a program for the context using gpt 
3) generates the z3 program from the program

- Problem: gpt is not good at generating prompts with valid solution 
    - either the possible solutions are not valid or the question has no solution 

1) generate the template + constraints
2) solve the template using z3  
3) given the correct solution, realize the problem and create the queries

- we can check if there is only one solution using z3 -> model needs n constraints

- do we need the program prompt?
"""

import sys
sys.path.append('../')
from utils.openai_utils import OpenAIModel
from utils.config import api_key

from arrangement.arrangement_parser import Arrangement_Parser
from arrangement.arrangement_solver import * 

import json
import os
import uuid

import argparse

class Arrangement_Pipeline:
    def __init__(self, args):
        self.templates = []
        self.num_of_examples = 2

        self.datapoints = []
        self.data_per_template = 1 # for each template, generate n problems

        self.openai_api = OpenAIModel(api_key, args.model_name, args.stop_words, args.max_new_tokens)

    def generate_template(self):
        # call xinghan's class to generate template
        # I also need template in raw_logic_program format
        template = """
        Domain:
        1: youngest
        6: oldest
        Variables:
        var_1 [1, 2, 3, 4, 5, 6]
        var_2 [1, 2, 3, 4, 5, 6]
        var_3 [1, 2, 3, 4, 5, 6]
        var_4 [1, 2, 3, 4, 5, 6]
        var_5 [1, 2, 3, 4, 5, 6]
        var_6 [1, 2, 3, 4, 5, 6]
        Constraints:
        var_1 > var_3 ::: var_1 is older than var_3.
        var_6 < var_4 ::: var_6 is younger than var_4.
        var_5 > var_2 ::: var_5 is older than var_2.
        var_2 < var_1 ::: var_2 is younger than var_1.
        var_3 == 1 ::: var_3 is the youngest.
        var_4 == 5 ::: var_4 is second oldest.
        """
        return template
    
    def generate_context(self, template):
        directory = 'prompts'
        file_path = os.path.join(directory, 'context_prompt.txt')

        file = open(file_path, 'r')
        prompt = file.read().replace('[[TEMPLATE]]', template)

        gpt_output = self.openai_api.generate(prompt, temperature=0.7, top_p=0.8)

        gpt_output=gpt_output.replace("Output:", "").strip()
        print(f"context: \n{gpt_output}")
        
        return gpt_output
    
    def generate_program(self, context):
        directory = 'prompts'
        file_path = os.path.join(directory, 'program_prompt.txt')
        file = open(file_path, 'r')
        prompt = file.read().replace('[[CONTEXT]]', context)
        gpt_output = self.openai_api.generate(prompt)
        gpt_output=gpt_output.replace("Output:", "").strip()
        print(f"program: \n{gpt_output}")
        return gpt_output
    
    def prompt_parser(self, program):
        m = Arrangement_Parser(program)
        z3_program = m.get_z3_program()
        ans = m.get_ans()
        gpt_ans = m.get_gpt_ans()
        return z3_program, gpt_ans, ans
    
    def check_template(self, template): 
        # TODO: finish function
        m = Arrangement_Parser(template)
    
    def generate_data(self, path='./gpt_generated_data/data.json', n=1):
        existing_data = []

        if os.path.exists(path):
            try: 
                with open(path, 'r') as file:
                    for dp in json.load(file):
                        # print("dp: ", dp)
                        existing_data.append(dp)
            except: 
                existing_data = []

        for _ in range(n):
            datapoint = {}
            id = str(uuid.uuid4())
            template = self.generate_template()
            context = self.generate_context(template)
            raw_logic_program = str(self.generate_program(context))
            z3_program, gpt_ans, ans = self.prompt_parser(raw_logic_program)
            datapoint['id'] = id
            datapoint['context'] = context
            datapoint['raw_logic_program'] = raw_logic_program
            datapoint['gpt_ans'] = gpt_ans
            datapoint['ans'] = ans
            datapoint['z3_program'] = z3_program

            existing_data.append(datapoint)

        with open(path, 'w') as file:
            json.dump(existing_data, file, indent=4)

        return datapoint

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('--prompt_path', type=str, default='./prompts/direct_fol_problem_generation.txt')
    parser.add_argument('--num_of_examples', type=int, default=5)
    parser.add_argument('--save_path', type=str, default='./fol_programs')
    parser.add_argument('--api_key', type=str)
    parser.add_argument('--model_name', type=str, default='text-davinci-003')
    parser.add_argument('--stop_words', type=str, default='------')
    parser.add_argument('--max_new_tokens', type=int, default=1024)
    args = parser.parse_args()
    return args

if __name__ == '__main__':
    args = parse_args()
    args.model_name = 'gpt-4'
    args.api_key = api_key
    path = './gpt_generated_data/data.json'

    p = Arrangement_Pipeline(args)
    p.generate_data(path, 2)