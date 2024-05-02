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
import re

from datetime import date

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
        num_variables = random.randint(3, 7)
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
        
        # print(f"domain: {domain}")
        max_val = max(map(int, domain.keys()))
        # print(f"max_val: {max_val}")
        return domain, max_val
    
    def parse_definitions(self, context):
        definitions = {}
        
        lines = [line.lstrip().strip() for line in context.split('\n') if line != '\n']
        for i in range(len(lines)):
            print(f"lines[i]: {lines[i]}")
            if lines[i][:9] != "position(":
                continue 
            
            var, defn = lines[i].split(':')
            print(f"var: {var}, defn: {defn}")
            var = var.lstrip().strip()
            defn = defn.lstrip().strip()
            underscore_pos = var.find('_')
            definitions[var[underscore_pos+1:]] = defn
            
        return definitions
        
    def convert_solutions(self, solutions, template, context):
        """
        convert solutions to text that makes sense given 
        [[pos = [2 -> 5, 3 -> 1, 5 -> 3, 4 -> 2, else -> 4]], [pos = [2 -> 5, 3 -> 1, 4 -> 2, 5 -> 4, else -> 3]], [pos = [2 -> 4, 3 -> 1, 4 -> 2, 5 -> 3, else -> 5]], [pos = [2 -> 5, 3 -> 3, 4 -> 2, 5 -> 4, else -> 1]]]
        
        Question: 
        In a high-stakes national car race, five racers are lined up on a five-lane track, each eager to clinch the title. The track lanes are numbered from 1 to 5 from left to right. Each racer's initial lane assignment directly impacts their strategy and ability to maneuver during the race. Racer Blake, known for their quick starts, is strategically positioned in lane 4, second from the right, allowing them a clear path along the outside. Meanwhile, racer Dana, recognized for their defensive driving, is placed in lane 2, second from the left, giving them a good vantage point to control the center of the race. Racer Casey is somewhere to the left of racer Erin, suggesting they might be in a more central or leftward position, while racer Erin, known for a strong finish, finds themselves leftward of Blake, which sets up an interesting dynamic as the race progresses. The positions of the racers dictate their initial tactics and the unfolding drama on the track, each aiming to leverage their lane to gain the upper hand.
        
        If we were to order the variables on a scale from 1 - 5, with 1 being the leftmost and 5 being the rightmost, here are all the possible solutions.
        Solution 1:  
        Position of racer Blake = 5 
        Position of racer Casey = 1 
        Position of racer Erin = 3 
        Position of racer Dana = 2 
        Position of racer Alex = 4 
        
        ...
        """
        """
        Domain:
        1: leftmost
        5: rightmost
        
        var_1: Position of racer Alex
        var_2: Position of racer Blake
        var_3: Position of racer Casey
        var_4: Position of racer Dana
        var_5: Position of racer Erin
        """
        # get the domain 
        domain, num_variables = self.parse_domain(template)
        print(f"domain: {domain}")
        print(f"num_variables: {num_variables}")
        
        # get the definitions of the variables 
        definitions = self.parse_definitions(context)
        print(f"definitions: {definitions}")
        
        print(f"solutions: {solutions}")
        
        context = context.split('\n')[0]
        
        n = len(solutions)
        
        solutions_input = ""
        solutions_input += f"Question: {context}\n"
        solutions_input += f"Domain:\n{1}: {domain['1']}\n{num_variables}: {domain[str(num_variables)]}\n"
        solutions_input += "Definitions:\n"
        for k, v in definitions.items(): 
            solutions_input += f"{k}: {v}\n"
        
        solutions_input += "\n"
        
        for i in range(n):
            solutions_input += f"Solution #{i+1}:\n"
            solution = str(solutions[i]).lstrip().strip()[1:][:-2]
            _, solution = solution.split('[')
            print(f"solution: {solution}")
            assignments = [assignment.lstrip().strip() for assignment in solution.split(',')]
            print(f"assignments: {assignments}")
            
            variables = set(range(1, num_variables+1))
            
            for assignment in assignments: 
                print(f"assignment: {assignment}")
                var, pos = assignment.split('->')
                
                var = var.strip()
                pos = pos.lstrip()
                if var == 'else': 
                    var = str(list(variables)[0])
                
                print(f"var: {var}, pos: {pos}")
                
                solutions_input += f"{definitions[f'position({var})']}: {pos}\n"
                variables.remove(int(var))
                
        print(f"solutions_input: \n{solutions_input}")
        return solutions_input            
    
    def generate_data(self, path='./gpt_generated_data/data.json', n=1):
        query_path = 'prompts/query_prompt.txt'
        with open(query_path, 'r') as file: query_prompt = file.read()
        
        for i in range(self.num_data):
            while True: 
                # generate template until you get a template 
                print(f"GENERATING TEMPLATE...")
                template = self.generate_template()

                a = Arrangement_Parser(template)
                a.find_possible_solutions()
                solutions = a.get_solutions()

                if solutions and len(solutions) < 20:
                    break 
                
            print(f"template: {template}")
                
            context = self.generate_context(template)
            # print(f"context: {context}")
            
            input_solutions = self.convert_solutions(solutions, template, context)
            
            query_prompt = query_prompt.replace('[[TEMPLATE]]', input_solutions)
            # print(f"query_prompt: {query_prompt}")
            
            while True: 
                print("GENERATING QUERIES...")
                # check if only one query is correct 
                statement = self.openai_api.generate(query_prompt)
                
                print(f"")
                                
                valid = a.check_answers(statement)
            
                if valid: 
                    break 
        
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
#     a = Arrangement_Parser(template)
    # s = a.find_possible_solutions()
    # p.convert_solutions(s, template, context)
    # p.generate_template()
    p.generate_data()
    
    today = date.today()
    
    p.write_output(f'/arrangement/data/{today}')
    
    # p.generate_data(path, 2)