import sys 
sys.path.append('../')
from utils.openai_utils import OpenAIModel
from utils.config import api_key

class ArrangementGenerator:
    def __init__(self, args):
        self.openai_api = OpenAIModel(api_key, args.model_name, args.stop_words, args.max_new_tokens)
    
    def generate_template(self, num_variables, operators):
        template_path = 'prompts/template_prompt.txt'
        try: 
            with open(template_path, 'r') as file: 
                contents = file.read() 
                template_prompt = contents.replace('[[TEMPLATE]]', f'num_variables = {num_variables}\noperators = {"".join(operators)}')
        except FileNotFoundError:
            print(f"File not found at {template_path}")
            
        except Exception as e: 
            print('An error occured: ', e)
            
        template = self.openai_api.generate(template_prompt, temperature=0.7)
        return template
    
    def generate_context(self, template, prev_topics):
        # read in prev_topics and generate context 
        pass 
    
    def generate_query(self, context, label):
        pass