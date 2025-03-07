# kurt-lang

The Kurt programming language is a simple language to write proofs in a form that is close to how humans write proofs.  The file `kurt.py` contains the whole implementation.  For now, just clone the repository and start proving:

    ~/git/kurt-lang$ ./kurt.py                               
    This is Kurt, Version 0.1 (made by Stefan Harmeling, 2025)
    !!![1] load "propositional"
    !!![2] const "A"
    !!![3] const "B"
    !!![4] bool "A"
    !!![5] bool "B"
    !!![6] use A implies B
    use (A implies B)                               ; <stdin>:6 axiom
    !!![7] use A
    use A                                           ; <stdin>:7 axiom
    !!![8] B
    B                                               ; <stdin>:8 by <stdin>:6
    !!![9] ^D
    Bye!
    ~/git/kurt-lang$

Alternatively, create a file `modus-ponens.kurt`:

    ; simple modus ponens proof
    load "propositional"
    const "A"
    const "B"
    bool "A"
    bool "B"
    use A implies B
    use A
    B

Then just check it on the shell:

    ~/git/kurt-lang$ ./kurt.py modus-ponens.kurt 
    This is Kurt, Version 0.1 (made by Stefan Harmeling, 2025)
    use (A implies B)                               ; modus-ponens.kurt:7 axiom
    use A                                           ; modus-ponens.kurt:8 axiom
    B                                               ; modus-ponens.kurt:9 by modus-ponens.kurt:7
    Proof checked.
    ~/git/kurt-lang$

Happy proving!