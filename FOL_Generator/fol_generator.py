import sys
sys.path.append('../')

import json
from utils.openai_utils import OpenAIModel
import os
import random
from tqdm import tqdm
import uuid
import argparse
from utils.config import api_key

class Direct_FOL_Problem_Generator:
    def __init__(self, args):
        self.args = args
        self.model_name = args.model_name
        self.save_path = args.save_path
        self.seed_data_path = args.seed_data_path
        self.prompt_path = args.prompt_path
        self.num_of_examples = args.num_of_examples

        self.openai_api = OpenAIModel(args.api_key, args.model_name, args.stop_words, args.max_new_tokens)
        self.prompt_template = self.load_prompt_template()
        self.seed_dataset = self.load_seed_dataset()

    def load_prompt_template(self):
        with open(self.prompt_path, 'r') as f:
            prompt_template = f.read()
        return prompt_template
        
    def load_seed_dataset(self):
        with open(self.seed_data_path, 'r') as f:
            seed_dataset = json.load(f)
        return seed_dataset
    
    def prompt_creator(self, seed_nl, seed_fol):
        full_prompt = self.prompt_template.replace('[[SEED_SENTENCE]]', seed_nl.strip())
        full_prompt = full_prompt.replace('[[SEED_FOL]]', seed_fol.strip())
        return full_prompt
    
    '''
    Speed up the generation process by batching
    '''
    def batch_logic_program_generation(self, batch_size = 10):
        # randomly choose N examples from the seed dataset
        random.seed(0)
        seed_fols = random.sample(self.seed_dataset, self.num_of_examples)
        # split dataset into chunks
        dataset_chunks = [seed_fols[i:i + batch_size] for i in range(0, len(seed_fols), batch_size)]

        outputs = []
        for chunk in tqdm(dataset_chunks):
            # create prompt
            full_prompts = [self.prompt_creator(example['NL'], example['FOL']) for example in chunk]
            try:
                batch_outputs = self.openai_api.batch_generate(full_prompts)
                # create output
                for sample, output in zip(chunk, batch_outputs):
                    programs = [output]
                    print(f"programs: {programs}")
                    output = {'id': str(uuid.uuid4()), 
                            'seed_sent': sample['NL'],
                            'seed_fol': sample['FOL'],
                            'raw_fol_problem': programs}
                    outputs.append(output)
            except:
                # generate one by one if batch generation fails
                for sample, full_prompt in zip(chunk, full_prompts):
                    try:
                        output = self.openai_api.generate(full_prompt)
                        programs = [output]
                        print(f"programs: {programs}")
                        outputs.append({'id': str(uuid.uuid4()), 
                                'seed_sent': sample['NL'],
                                'seed_fol': sample['FOL'],
                                'raw_fol_problem': programs})
                    except:
                        print('Error in generating logic problems for example: ', sample['id'])

        # remove examples with duplicate ids from the result
        outputs = list({output['id']: output for output in outputs}.values())
        print(f"Generated {len(outputs)} examples.")
        
        # save outputs
        if not os.path.exists(self.save_path):
            os.makedirs(self.save_path)
        
        with open(os.path.join(self.save_path, f'fol_direct_generation_{self.model_name}.json'), 'w') as f:
            json.dump(outputs, f, indent=2, ensure_ascii=False)

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seed_data_path', type=str, default='./MALLs_data/MALLS-v0.json')
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
    args.num_of_examples = 10
    args.model_name = 'gpt-4'
    args.api_key = api_key

    fol_problem_generator = Direct_FOL_Problem_Generator(args)
    fol_problem_generator.batch_logic_program_generation(batch_size=1)