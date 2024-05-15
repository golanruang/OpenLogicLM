import sys
sys.path.append('../')

from utils.config import api_key

from arrangement.arrangement_pipeline import parse_args, Arrangement_Pipeline
import random

args_list = [
    '--num_of_examples', f'{num_examples}',
    '--save_path', './arrangement_data',
    '--model_name', 'gpt-4',
    '--max_new_tokens', f'{max_new_tokens}',
    '--num_variables', f'{n}',
    '--label', f'{label}'
]

args = parse_args(args_list)
args.api_key = api_key
a = Arrangement_Pipeline(args)
a.generate_data()