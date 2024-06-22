"""
1. Generate problem with correct params 
	- verify its solvable 
2. Generate context with topic 
3. Generate a query 
	- make sure to ensure query comparison operator distribution too 
4. Calculate label using z3 
"""
import sys 
sys.path.append("../")
import random
from arrange.generator import ArrangementGenerator
from arrange.parser import ArrangementParser

class ArrangementPipeline: 
    def __init__(self):
        # n = number of examples to generate 
        self.operators = ["==", "!=", ">", "<", "<=", ">="]
        self.topics = []
        self.parser = ArrangementParser() 
        self.generator = ArrangementGenerator() 
        
    def generate_template(self):
        def sample_n_operators(num_variables):
            operators = []
            for _ in range(num_variables):
                operator_idx = random.randint(0, 5)
                operators.append(self.operators[operator_idx])
                
        num_variables = random.randint(1, 8)
        operators = sample_n_operators(num_variables)
        
        template = self.generator.generate_template(num_variables, operators)
        return template
        
    def check_valid_template(self, template):
        solutions = self.parser.find_solutions(template)
        if len(solutions) == 0:
            return False 
        
        return True 
    
    def generate_context(self, template):
        context = self.generator.generate_context(template, prev_topics=self.topics)
        return context 
    
    def generate_query(self, context):
        label = random.randint(0, 1)
        while True: 
            query = self.generator.generate_query(context, label)
            solution = self.parser.solve(query)
            if solution == label: return query
    
    def generate(self, n):
        # n is number of pieces of data to generate 
        for _ in range(n):
            # get template 
            while True: 
                template = self.generate_template()
                if self.check_valid_template(template): break 
                
            context = self.generate_context(template)
            query, label = self.generate_query(context)
            symbolic_formulation = self.parser.get_formulation()
            
            self.write(context, query, label, symbolic_formulation)

    def write(self, context, query, label, symbolic_formulation):
        # write data 
        # id, type, context, natural_language_premises, symbolic_premises, natural_language_query, symbolic_query, label, symbolic_formulation
        pass 
            
        
        