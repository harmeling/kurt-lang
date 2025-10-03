# kurt-lang

The Kurt programming language is an artificial language to write proofs in a form that is designed to be close to how humans write proofs.  The file `kurt.py` contains the whole implementation.  You can either call `./kurt.py` or `./kurt`.  For now, just clone the repository and start proving:

    ~/git/kurt-lang (main ✗) kurt
    This is Kurt, Version 0.1 (made by Stefan Harmeling, 2025)
    !!![1] bool A, B
    !!![2] use A implies B
    use A implies B                                             ; 2 axiom
    !!![3] use A
    use A                                                       ; 3 axiom
    !!![4] B
    B                                                           ; 4 by 3, 2
    !!![5] ^D
    Bye!

Alternatively, create a file `modus-ponens.kurt`:

    ; simple modus ponens proof
    bool A, B
    use A implies B
    use A
    B

Then just check it in the commandline:

    ~/git/kurt-lang (main ✗) kurt modus-ponens.kurt 
    This is Kurt, Version 0.1 (made by Stefan Harmeling, 2025)
    use A implies B                                             ; 3 axiom
    use A                                                       ; 4 axiom
    B                                                           ; 5 by 4, 3
    Proof checked.

Happy proving!

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

## License

[MIT](./LICENSE) © 2025 Stefan Harmeling

## Attribution

This project is licensed under the [MIT License](LICENSE).  
When using or referencing it, please include a link back to this repository.  
A star on GitHub is also greatly appreciated!
# CI test 2025-10-03T10:47:02+02:00
# CI test 2025-10-03T10:47:47+02:00
