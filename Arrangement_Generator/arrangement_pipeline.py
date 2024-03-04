from arrangement_parser import Arrangement_Parser
from arrangement_solver import *
from openai_utils import OpenAIModel
import json
import os
import uuid

import argparse

from config import api_key

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
        1: leftmost
        5: rightmost
        Variables:
        var_1 integer [1, 2, 3, 4, 5]
        var_2 integer [1, 2, 3, 4, 5]
        var_3 integer [1, 2, 3, 4, 5]
        var_4 integer [1, 2, 3, 4, 5]
        var_5 integer [1, 2, 3, 4, 5]
        Constraints:
        var_2 > var_5 ::: var_2 is to the right of var_5.
        var_3 < var_5 ::: var_2 is to the left of var_5.
        var_2 == 4 ::: var_2 is the second from the right. 
        var_4 == 2 ::: var_4 is the second from the left. 
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

def main():
    args = parse_args()
    args.model_name = 'gpt-4'
    args.api_key = api_key
    path = './gpt_generated_data/data.json'

    p = Arrangement_Pipeline(args)
    p.generate_data(path, 2)

main()