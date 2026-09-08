# kurt-lang

The Kurt programming language is an artificial language to write proofs in a form that is designed to be close to how humans write proofs.  The file `kurt.py` contains the whole implementation.  You can either call `./kurt.py` or `kurt` (after installation via `pip`).  Let's start proving:

    ~/git/kurt-lang (main ✗) kurt
    This is Kurt, v0.1 (made by Stefan Harmeling, 2025)
    ;[1] bool A, B
    ;[2] use A implies B
    use A implies B                           ; 2 without proof
    ;[3] use A
    use A                                     ; 3 without proof
    ;[4] B
    B                                         ; 4 by 3, 2
    ;[5] ^D
    Bye!

Alternatively, create a file `modus-ponens.kurt`:

    ; simple modus ponens proof
    bool A, B
    use A implies B
    use A
    B

Then just check it in the commandline:

    ~/git/kurt-lang (main ✗) kurt modus-ponens.kurt 
    This is Kurt, v0.1 (made by Stefan Harmeling, 2025)
    use A implies B                           ; 3 without proof
    use A                                     ; 4 without proof
    B                                         ; 5 by 4, 3
    Proof checked

Happy proving!

## Installing Kurt (for users)

The simplest way to use Kurt is to download a single self-contained `kurt.py` and run it with Python 3.10 or higher — no `theories/` directory, no other files, no install:

    python3 kurt.py
    ./kurt.py          # if you make it executable with `chmod +x kurt.py`

This standalone file has all the standard theories (`prop.kurt`, `logic.kurt`, `arith.kurt`, ...) embedded directly in it, so `load prop` and friends work immediately. It's built from this repo with:

    python3 scripts/build_standalone.py       # writes dist/kurt.py

This is useful if you would like to hand out the interpreter alongside exercises in a lecture or tutorial — copy just that one file anywhere.

If you'd rather keep the theories as separate, readable/editable `.kurt` files next to the interpreter (e.g. to modify a theory yourself), copy `src/kurt/kurt.py` and the `src/kurt/theories/` directory together instead — same usage, but you have to keep `theories/` alongside `kurt.py`.

Alternatively, Kurt is installable directly with pip from the GitHub repository (no cloning required)

Install the latest version:

    pip install git+https://github.com/harmeling/kurt-lang.git

Install a specific tag or branch:

    pip install git+https://github.com/harmeling/kurt-lang.git@v0.1.0

Or, install from a local clone:

    git clone https://github.com/harmeling/kurt-lang.git
    cd kurt-lang
    pip install .

## Installing Kurt Tools

The [Kurt language syntax repo](https://github.com/harmeling/kurt-syntax) includes both a Visual Studio Code extension (`kurt-syntax-<version>.vsix`) for syntax highlighting and snippets and indenting and an Emacs mode (`kurt-mode.el`).

### VS Code Extension Installation

1. **Download the Extension Package**

   You can download the latest VSIX package from the [kurt-syntax GitHub repository](https://github.com/harmeling/kurt-syntax).  
   Alternatively, if you have the repository cloned, you can build the package locally:

   ```sh
   cd path/to/kurt-syntax
   vsce package
   ```

2. **Install the VSIX Package**

   To install the extension, run the following command in your terminal:

   ```sh
   code --install-extension kurt-syntax-<version>.vsix
   ```

   Replace `<version>` with the appropriate version number or the actual package name of the generated file.

### Emacs Mode Installation

1. **Download `kurt-mode.el`**

   The Emacs mode file is hosted in the [kurt-syntax GitHub repository](https://github.com/harmeling/kurt-syntax/blob/main/kurt-mode.el). Download or clone the file to your local setup.

2. **Load the Mode in Your Emacs Configuration**

   Add the following lines to your Emacs configuration (e.g., in your `.emacs` or `init.el` file):

   ```elisp
   ;; Load kurt-mode from the local file
   (load "/path/to/kurt-mode.el")
   (add-to-list 'auto-mode-alist '("\\.kurt\\'" . kurt-mode))
   ```

   Replace `/path/to/kurt-mode.el` with the actual path where you saved the file.

That's it!

## Developer Setup

To work on Kurt locally, create a virtual environment and install the package in editable mode with development tools:

    python -m venv .venv
    source .venv/bin/activate
    pip install -e .[dev]

This installs Kurt in editable mode, meaning changes to the source code take effect immediately without reinstalling.
The [dev] extra installs optional development dependencies such as coverage.

Run the test suite:

    python -m unittest

Run test with coverage:

    coverage run -m unittest
    coverage report

## License

[MIT](./LICENSE) © 2025 Stefan Harmeling

## Attribution

This project is licensed under the [MIT License](LICENSE).  
When using or referencing it, please include a link back to this repository.  
A star on GitHub is also greatly appreciated!
