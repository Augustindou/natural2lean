# Natural2Lean

Translation of natural language proofs to lean4 for verification. The objective was to make a proof of concept, integrating a command line interface (CLI) to try out some proofs quickly.

Project developed for a master's thesis.
Advisor : François Glineur

# Installation

To use this project, you need `lean4` and the python packages mentioned in `requirements.txt`. You can go [here to install `lean4`](https://leanprover.github.io/lean4/doc/setup.html) and run `pip install -r requirements.txt`.

# How the system works

The system will try to understand the meaning of the natural language sentences by matching specific keywords.

## Keywords

### Specific keywords

- To close the CLI, you can use `quit` or `exit`.
- If you made a mistake, use `back` or `backtrack` to undo the last step.

### Theorem statements

- A theorem statement is simply an implication you want to prove. `if [...] then [...]` will be matched, and hypotheses / theses will be extracted from that.
- You can also define a theorem name, by writing `theorem [...] : if [...] then [...]`.

### Statements

- For now, most statements need the `have` keyword. The system will try to match a substatement on the right of the `have` keyword and will try to find the proof of that substatement in the sentence. Any equation should be solved automatically, and in addition to that, the keys in [`natural2lean.text.have.PROOFS`](src/natural2lean/text/have.py) will also be understood.
- You can also conclude a goal by simply stating it (for example, if your goal is to prove that $m^2$ is even, then stating `$m^2$ is even` will work).
- You can add words to make your proof more readable, such as `Hence, $m^2$ is even`, even though just writing `$m^2$ even` will have the same effect.

# Contributing

To install `natural2lean` along with the tools you need to develop and run the tests, run the following in your virtual environnment :
```bash
pip install -e .[dev]
``` 
Note that if you use `zsh`, you need to run the following instead :
```
pip install -e .'[dev]'
```

