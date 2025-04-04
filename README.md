# kurt-lang

The Kurt programming language is a simple language to write proofs in a form that is close to how humans write proofs.  The file `kurt.py` contains the whole implementation.  You can either call `./kurt.py` or `./kurt`.  For now, just clone the repository and start proving:

    ~/git/kurt-lang (main ✔) kurt
    This is Kurt, Version 0.1 (made by Stefan Harmeling, 2025)
    !!![1] load "propositional"
    !!![2] bool A, B
    !!![3] use A implies B
    use A implies B                                       ; 3 axiom
    !!![4] use A
    use A                                                 ; 4 axiom
    !!![5] B
    B                                                     ; 5 by 3
    !!![6] ^D
    Bye!

Alternatively, create a file `modus-ponens.kurt`:

    ; simple modus ponens proof
    load "propositional"
    bool A, B
    use A implies B
    use A
    B

Then just check it on the shell:

    ~/git/kurt-lang (main ✗) kurt modus-ponens.kurt 
    This is Kurt, Version 0.1 (made by Stefan Harmeling, 2025)
    use A implies B                                          ; 4 axiom
    use A                                                    ; 5 axiom
    B                                                        ; 6 by 4
    Proof checked.

Happy proving!

## License

[MIT](./LICENSE) © 2025 Stefan Harmeling