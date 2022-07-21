# natural2lean

## Proof of concept of a natural language interactive theorem prover

This project was developed for my Master's Thesis at UCLouvain (under the supervision of Pr. François Glineur and T.A. Sébastien Mattenet). The problem this project attempts to solve is the feedback on exercice proofs written by students, as this feedback comes either in the form of one correct version of the proof (although a theorem can be proved in many different ways), or taking up valuable T.A. time to correct simple proofs. The aim is therefore to bring machine verification to natural language proofs. This is done by translating natural language to `lean4` and returning the feedback to the user.

<!-- TODO - Visual helper -->

## How this project works

The project consists of a python package, `natural2lean`, giving access to a `Translator` class. This class contains the following methods:
- `__init__(lean_project_directory: str = None)`; creates the object and makes sure that it has access to the needed [lean-project-template](https://github.com/Augustindou/natural2lean-lean-project-template). The optional `lean_project_directory` indicates to the program where to store the project.
- `new_theorem(string: str)`; parses the string into a new theorem and returns the state of the proof after the theorem was added.
- `new_statement(string: str)`; parses the string into a new statement and returns the state of the proof after the statement was added.
- `new(string: str)`; delegates to `new_theorem` or `new_statement` depending on the context (whether or not there is a goal to be solved).
- `interpretation_feedback()`; gives a feedback what parts of the `string` were used and what parts were ignored.
- `backtrack()`; removes the last theorem / statement added.

<!-- TODO - different statements -->

## How to install

You will need to first install `lean4` ([install guide](https://leanprover.github.io/lean4/doc/setup.html)).

For an end user, the easiest way to use it is to use the [natural2lean-cli](https://github.com/Augustindou/natural2lean-cli) package, gives access to an executable (`natural2lean`) containing an interactive program and a file reader.

## How to tweak this project for your own uses

This project is a proof of concept, feel free to fork and tweak it for your own uses.

<!-- # natural2lean

Translation of natural language proofs to lean4 for verification. The objective was to make a proof of concept of the translation system. This project is developed for a master's thesis under the supervision of François Glineur and Sébastien Mattenet.

The project consists of a python package, `natural2lean`, giving access to a `Translator` class. This class contains the following methods:
- `__init__(lean_project_directory: str = None)`; creates the object and makes sure that it has access to the needed [lean-project-template](https://github.com/Augustindou/natural2lean-lean-project-template). The optional `lean_project_directory` indicates to the program where to store the project template.
- `new_theorem(string: str)`; parses the string into a new theorem and returns the state of the proof after the theorem was added.
- `new_statement(string: str)`; parses the string into a new statement and returns the state of the proof after the statement was added.
- `new(string: str)`; delegates `new_theorem` or `new_statement` depending on the context (whether or not there is a goal to be solved).
- `backtrack()`; removes the last theorem / statement added

# Installation

1. Install `lean4` ([install guide](https://leanprover.github.io/lean4/doc/setup.html))
2. Install the project (`pip install .`)

# How the system works

The system will try to understand the meaning of the natural language sentences by matching specific keywords. Spaces are optional and the system will raise a `TranslationError` (`natural2lean.utils.exceptions`) if it could not parse the string, or a `LeanError` if the translated string was not accepted by lean.

### Theorem statements

- A theorem statement is simply an implication you want to prove. `if [...] then [...]` will be matched, and hypotheses / theses will be extracted from that.
- You can also define a theorem name, by writing `theorem [...] : if [...] then [...]`.

### Statements

- For now, most statements need the `have` keyword. The system will try to match a substatement on the right of the `have` keyword and will try to find the proof of that substatement in the sentence. Any equation should be solved automatically, and in addition to that, the keys in [`natural2lean.text.have.PROOFS`](src/natural2lean/proof_elements/statement/have.py) will also be understood.
- You can also conclude a goal by simply stating it (for example, if your goal is to prove that $m^2$ is even, then stating `$m^2$ is even` will work).
- You can add words to make your proof more readable, such as `Hence, $m^2$ is even`, even though just writing `$m^2$ even` will have the same effect.

### Working examples

- [if $m \in \mathbb{N}$ is even, then $m^2$ is even](https://github.com/Augustindou/natural2lean-lean-project-template/blob/master/examples/example-1-sqr_m-even/theorem.tex)
- [if $q \in \mathbb{N}$ is not divisible by $3$, then $q^2 \mod 3 = 1$](https://github.com/Augustindou/natural2lean-lean-project-template/blob/master/examples/example-2-sqr_q-mod-3/theorem.tex)

# Contributing

To install `natural2lean` along with the tools you need to develop and run the tests, run the following in your virtual environnment :
```bash
pip install -e .[dev]
``` 
Note that if you use `zsh`, you need to run the following instead :
```zsh
pip install -e .'[dev]'
```
 -->
