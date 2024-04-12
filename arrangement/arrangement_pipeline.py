"""
This arrangement pipeline takes in a template and 
1) generates a context for the problem using gpt 
2) generates a program for the context using gpt 
3) generates the z3 program from the program

- Problem: gpt is not good at generating prompts with valid solution 
    - either the possible solutions are not valid or the question has no solution 

1) generate the template + constraints 
2) solve the template using z3 
3) given the correct template, realize the problem and create the queries

- we can check if there is only one solution using z3 

- do we need the program prompt?

Don't need to make the constraint such that we only have one answer 
1. ask llm to generate problem and constraints 
2. solve it using z3 
3. Generate the context 
4. Generate the queries based on the possible answers and context


(A B C)
(C B A)

-> 

1) B should always be in the middle. 
2)  

"""

import sys
sys.path.append('../')
from utils.openai_utils import OpenAIModel
from utils.config import api_key

from arrangement.arrangement_parser import Arrangement_Parser
# from arrangement.arrangement_solver import * 

import json
import os
import uuid

import argparse
import random

class Arrangement_Pipeline:
    def __init__(self, args):
        self.templates = []
        self.num_data = 1

        self.datapoints = []
        self.data_per_template = 1 # for each template, generate n problems

        self.openai_api = OpenAIModel(api_key, args.model_name, args.stop_words, args.max_new_tokens)
        
        self.solutions = []

    def generate_template(self):
        """generate template using """
        num_variables = random.randint(3, 8)
        template_path = "prompts/template_prompt.txt"
        try:
            with open(template_path, 'r') as file:
                contents = file.read()
                template = contents.replace('[[TEMPLATE]]', f'num_variables = {num_variables}')
        except FileNotFoundError:
            print("File not found.")
        except Exception as e:
            print("An error occurred:", e)
            
        gpt_output = self.openai_api.generate(template, temperature=0.7)
        print(gpt_output)
        return gpt_output
    
    def generate_context(self, template):
        directory = 'prompts'
        file_path = os.path.join(directory, 'context_prompt.txt')

        file = open(file_path, 'r')
        prompt = file.read().replace('[[TEMPLATE]]', template)

        gpt_output = self.openai_api.generate(prompt, temperature=0.7, top_p=0.8)

        gpt_output=gpt_output.replace("Output:", "").strip()
        print(f"context: \n{gpt_output}")
        
        return gpt_output
    
    def prompt_parser(self, program):
        m = Arrangement_Parser(program)
        z3_program = m.get_z3_program()
        ans = m.get_ans()
        gpt_ans = m.get_gpt_ans()
        return z3_program, gpt_ans, ans
    
    def check_template(self, template): 
        m = Arrangement_Parser(template)
    
    def generate_data(self, path='./gpt_generated_data/data.json', n=1):
        for i in range(self.num_data):
            while True: 
                template = self.generate_template()
                a = Arrangement_Parser(template)
                a.find_possible_solutions()
                solutions = a.get_solutions()
                z3 = a.get_z3_program()
                if solutions:
                    break 
                
            context = self.generate_context(template)
                
            print(f"solutions: {solutions}")
            print(f"z3: {z3}")
            print(f"context: {context}")
            
        return 
            

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('--num_of_examples', type=int, default=5)
    parser.add_argument('--save_path', type=str, default='./fol_programs')
    parser.add_argument('--api_key', type=str)
    parser.add_argument('--model_name', type=str, default='text-davinci-003')
    parser.add_argument('--stop_words', type=str, default='------')
    parser.add_argument('--max_new_tokens', type=int, default=1024)
    # parser.add_argument('--num_variables', type)                              # add arg for range of variables
    args = parser.parse_args()
    return args

if __name__ == '__main__':
    args = parse_args()
    args.model_name = 'gpt-4'
    args.api_key = api_key
    path = './gpt_generated_data/data.json'

    p = Arrangement_Pipeline(args)
    p.generate_template()
    # p.generate_data()
    
    # p.generate_data(path, 2)