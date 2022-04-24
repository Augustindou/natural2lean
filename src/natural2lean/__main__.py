import sys
import PyInquirer
from natural2lean.interface.interactive import interactive_mode
from natural2lean.interface.full_proof import translate
import argparse

RED_COLOR = "\033[1;31m"

parser = argparse.ArgumentParser(description="Natural2Lean")
parser.add_argument(
    "mode",
    type=str,
    nargs="?",
    default="full_cli",
    help='Program mode. Can be either "interactive" or "file".',
)
parser.add_argument(
    "input_file",
    type=argparse.FileType("r"),
    nargs="?",
    default=None,
    help="Input file for file mode.",
)
parser.add_argument(
    "--output",
    "-o",
    type=argparse.FileType("w"),
    default=sys.stdout,
    help="Output file for file mode",
)
args = parser.parse_args()

# mode
mode = args.mode
input_file = args.input_file
output_file = args.output


def main():
    # interactive mode
    if mode == "interactive" or mode == "i":
        interactive_mode()
        return

    # file mode
    if mode == "file" or mode == "f":
        if input_file is None:
            print("No input file specified.")
            return
        translation = translate(input_file)
        print(translation, file=output_file)
        return

    # full cli mode
    if mode == "full_cli":
        ask_for_mode()
        return


# if run without arguments
def ask_for_mode():
    question = [
        {
            "type": "list",
            "name": "mode",
            "message": "What mode do you want to use?",
            "choices": ["interactive", "file"],
            "default": "interactive",
        }
    ]

    mode = PyInquirer.prompt(question)["mode"]
    if mode == "file":
        input_file = ask_for_input_file()
        output_file = ask_for_output_file()
        translation = translate(input_file.read())
        print(translation, file=output_file)
        return

    if mode == "interactive":
        interactive_mode()
        return

    raise Exception("Should be impossible to get here.")


# help functions
def open_file(filename: str, mode: str, default=None):
    if filename is None or filename.strip() == "":
        return default

    try:
        return open(filename, mode)
    except FileNotFoundError:
        if mode == "r":
            mode = "read"
        if mode == "w":
            mode = "write"
        print(f"{RED_COLOR}\nProblem opening {filename} in {mode} mode.\n")
        return None

def ask_for_input_file():
    question = [
        {
            "type": "input",
            "name": "input_file",
            "message": "Which file do you want to parse?",
        }
    ]
    input_file = open_file(PyInquirer.prompt(question)["input_file"], "r")
    if input_file is None:
        return ask_for_input_file()
    return input_file
        
def ask_for_output_file():
    question = {
        "type": "input",
        "name": "output_file",
        "message": "In which file do you want to write the output? (leave empty for stdout)",
    }
    output_file = open_file(
        PyInquirer.prompt(question)["output_file"], "w+", default=sys.stdout
    )
    return output_file

if __name__ == "__main__":
    main()
