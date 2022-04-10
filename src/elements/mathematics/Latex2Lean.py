import re

# TODO : add support for \cdot, \mod, ...
# TODO : add other latex functions

class LatexFunction:
    def __init__(self, pattern:str, string:str, n_args:int, intermediate:list[str]) -> None:
        self.pattern = pattern
        self.string = string
        self.n_args = n_args
        self.intermediate = intermediate

LATEX_SYMBOLS_COUNTERPARTS = {
    # operations
    r"\\mod": r"%",
    r"\\cdot": r"*",
}
LATEX_FUNCTIONS = [
    LatexFunction(r"\\frac", r"\frac", 2, ["(", ") / (", ")"]),
    LatexFunction(r"\\sqrt", r"\sqrt", 1, ["sqrt(", ")"]),
]
START_OF_FUNCTION = "{"
END_OF_FUNCTION = "}"


class Latex2Lean:
    def __init__(self, string:str) -> None:
        self.latex_string = string
        self.result_string = ""
        self.recursive_match(0)
    
    def recursive_match(self, position: int) -> int:
        next_function_start, next_function_end, next_function = self.get_next_function(position)
        next_start_start, next_start_end = self.get_next_start(position)
        next_end_start, next_end_end = self.get_next_end(position)
    
        # no function
        if next_function == None and next_start_start == None and next_end_start == None:
            self.result_string += self.latex_string[position:]
            return -1
    
        # function without end
        if next_end_start == None:
            raise Exception(f"LaTeX function without end" + 
                            f"\n        in \"{self.latex_string}\"" + 
                            f"\n        at \"{self.latex_string[next_function_start:]}\"")
        
        # end found before start
        if next_start_start == None or next_end_start < next_start_start:
            self.result_string += self.latex_string[position:next_end_start]
            return next_end_end
        
        # function found
        if next_start_start < next_end_start and next_function_start < next_start_start:
            # add part before function
            self.result_string += self.latex_string[position:next_function_start]

            for i in range(next_function.n_args):
                # go to next argument
                next_start_start, next_start_end = self.get_next_start(position)
                next_end_start, next_end_end = self.get_next_end(position)
                
                # if some argument is missing START_OF_FUNCTION
                if next_start_start == None:
                    raise Exception(f"LaTeX function with wrong number of arguments" + 
                                    f"\n        in \"{self.latex_string}\"" + 
                                    f"\n        at \"{self.latex_string[next_function_start:]}\"")

                # add intermediate elements (between args of function)
                self.result_string += next_function.intermediate[i]
                
                # add ith argument
                position = self.recursive_match(next_start_end)
                
                # if some argument is missing END_OF_FUNCTION
                if position == -1:
                    raise Exception(f"Missing argument for latex function" + 
                                    f"\n        in \"{self.latex_string}\"" + 
                                    f"\n        at \"{self.latex_string[next_function_start:]}\"")
            
            # add last element of function
            self.result_string += next_function.intermediate[i+1]
            
            position = self.recursive_match(next_end_end)
            return position
        
        raise Exception(f"Should not happen - Latex2Lean.recursive_match")

    def get_next_function(self, position: int) -> tuple[int, int, LatexFunction]:    
        starts = []
        
        for tex_fun in LATEX_FUNCTIONS:
            match_function = re.search(tex_fun.pattern, self.latex_string[position:])
            
            # no match for this latex function
            if match_function == None:
                continue
            
            # add to list
            next_function_start = match_function.start() + position
            next_function_end = match_function.end() + position
            starts.append((next_function_start, next_function_end, tex_fun))
            
        if len(starts) == 0:
            return None, None, None
        
        return min(starts)
    
    def get_next_end(self, position: int) -> int:
        # check for next end
        match_end = re.search(END_OF_FUNCTION, self.latex_string[position:])
        
        # no end found
        if match_end == None:
            return None, None
        
        next_end_start = match_end.start() + position
        next_end_end = match_end.end() + position
        
        return next_end_start, next_end_end
    
    def get_next_start(self, position: int) -> int:
        # check for next start
        match_start = re.search(START_OF_FUNCTION, self.latex_string[position:])
        
        # no start found
        if match_start == None:
            return None, None
        
        next_start_start = match_start.start() + position
        next_start_end = match_start.end() + position
        
        return next_start_start, next_start_end
    
        
examples = [r"\sqrt{2} + 3", r"\frac{\sqrt{2} + 3}{\sqrt{2}}", r"\frac{1}{2}", r"\sqrt{2}", ]
for ex in examples:
    print(f"{ex} : {Latex2Lean(ex).result_string}")

# TODO fractions, exponents with multiple things
# TODO what about 3x => 3 * x, but x1 = x1 => begins by a letter