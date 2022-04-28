import re

from .have import Have
from ..structure.matching import Matching, Translatable

# words that indicate that the case is not the first one
NOT_FIRST_CASE_WORDS = ["second", "third", "fourth", "fifth", "sixth", "last", "next"]

class Case(Matching):
    """Case class.
    The 'case' keyword is used to identify that we want to divide one hypothesis into multiple.
    """

    pattern: str = r"((.*)\s*case\s*(.*))"
    
    def set_contents(self):
        # rematch
        match = re.fullmatch(self.pattern, self.string)
        if not match:
            raise ValueError(
                f"Could not match {self.string} in {self.__class__.__name__}, should not use __init__ directly, but create instances using the match() method."
            )

        # plain text parts
        self.left_side = match.group(2).strip(" ,.;")
        self.right_side = match.group(3).strip(" ,.;")
        # definition
        
        self.sub_statement = self.get_sub_statement()
    
        # TODO change the "rcases h2 with h2 | h2 | h2" with a custom (or found) cases tactic (in lean)
    
    def get_sub_statement(self) -> Translatable:
        for cls in [Have,]:
            match = cls.match(self.string)
            if match is not None:
                return match
        
        return None
    
    def translate(self, hyp_list: list[str]=None, **kwargs) -> str:
        # for example, "for the second case" would not need the rcases tactic
        if any([w in self.string.lower() for w in NOT_FIRST_CASE_WORDS]):
            return self.sub_statement.translate(hyp_list=hyp_list, **kwargs)
        
        # get the (last) hypothesis that could be used to divide the case
        relevant_hyp = None
        if hyp_list is not None:
            for hyp in hyp_list[::-1]:
                if "∨" in hyp:
                    relevant_hyp = hyp
                    break
        
        # return only substatement if no relevant hyp
        if relevant_hyp is None:
            return self.sub_statement.translate(hyp_list=hyp_list, **kwargs)
        
        # rcases tactic
        hyp_name = relevant_hyp.split(":")[0].strip()
        hyp_count = relevant_hyp.count("∨")
        rcases = f"rcases {hyp_name} with " + " | ".join([hyp_name] * (hyp_count+1))
        return f"{rcases}\n\n{self.sub_statement.translate(hyp_list=hyp_list, **kwargs)}\n"
            
            