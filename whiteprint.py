import argparse
import shlex
import subprocess
from pathlib import Path


def run(*args):
    argstrs = [str(arg) for arg in args]
    print(f"$ {shlex.join(argstrs)}")
    subprocess.run(
        argstrs,
        check=True,
    )


def run_with_output(*args):
    argstrs = [str(arg) for arg in args]
    print(f"$ {shlex.join(argstrs)}")
    return subprocess.run(
        argstrs,
        check=True,
        capture_output=True,
        encoding="utf-8",
    ).stdout


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("main", type=Path, nargs="?", default="main.typ")
    args = parser.parse_args()

    # Produce PDF
    print(f"Generating {args.main.with_suffix('.pdf')}")
    run(
        *("typst", "compile"),
        *("--root", "."),
        *("--features", "html"),
        args.main,
    )

    # Produce HTML
    print()
    print(f"Generating {args.main.with_suffix('.html')}")
    run(
        *("typst", "compile"),
        *("--root", "."),
        *("--features", "html"),
        *("--format", "html"),
        args.main,
    )

    # Produce JSON
    print()
    print(f"Generating {args.main.with_suffix('.json')}")
    json = run_with_output(
        *("typst", "query"),
        args.main,
        "<whiteprint-metadata>",
        *("--field", "value"),
    )
    with open(args.main.with_suffix(".json"), "w") as f:
        f.write(json)


if __name__ == "__main__":
    main()
