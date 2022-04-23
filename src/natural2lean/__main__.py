import sys
import click
from natural2lean.interface.interactive import interactive_mode
from natural2lean.interface.from_file import translate_file


@click.group()
def main():
    pass


@main.command()
def interactive():
    interactive_mode()


@main.command()
@click.argument("input_file", type=click.File("r"))
@click.option("-o", "--output_file", type=click.File("w"), default=sys.stdout)
def file(input_file, output_file):
    translate_file(input_file)
    print("hello", file=output_file)


if __name__ == "__main__":
    main()
