import sys
from InquirerPy import inquirer
from InquirerPy.validator import PathValidator
from natural2lean.interface.interactive import interactive_mode
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
    mode = inquirer.select(
        message="What mode do you want to use?",
        choices=["interactive", "file"],
        default="interactive",
    ).execute()
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
    except IOError:
        if mode == "r":
            mode = "read"
        if mode == "w":
            mode = "write"
        print(f"{RED_COLOR}\n    Not finding file / invalid filename.\n")
        return None


def ask_for_input_file():
    filename = inquirer.filepath(
        message="Which file do you want to parse?",
        validate=PathValidator(is_file=True, message=f"Invalid path / filename."),
    ).execute()

    input_file = open_file(filename, "r")
    if input_file is None:
        return ask_for_input_file()
    return input_file


def ask_for_output_file():
    filename = inquirer.filepath(
        message="Where do you want to save the output? (leave blank for stdout)",
    ).execute()

    output_file = open_file(filename, "w+", default=sys.stdout)
    if output_file is None:
        return ask_for_output_file()
    return output_file


def translate(text: str) -> str:
    return "Full text translation is not implemented yet"


if __name__ == "__main__":
    main()
