# The Kurt Programming Language Documentation

**Author:** Stefan Harmeling
**Date:** 2025-02-25 (created)

---

The Kurt programming language is a made to write down and automatically check simple (and not so simple) mathematical proofs.  The motivation is to have a language that students can use while learning mathematics.  Similarly to automatic testing while learning programming, students can write down their proofs in Kurt and test them automatically to get immediate feedback.

## Symbols and terms and the grammar

- The alphabet contains letters, digits and special symbols.

- The atoms of Kurt are *symbols*, which are strings of the alphabet.

- Space is never part of a symbol.  Instead it can be used for function application.

- Comments follow after a semicolon `;`.  However, comments are stored with each formula, since they can help to refer to formulas.

- The grammar can be specified using the following keywords:

      infix    ; to declare infix symbols
      postfix  ; to declare postfix symbols
      prefix   ; to declare prefix symbols
      brackets ; to declare bracket symbols
      arity    ; to declare the arity of a symbol
      flat     ; to declare an infix operator to be flat
      sym      ; to declare an infix operator to be symmetric

- Examples:

      infix "+" 20 20
      a + b           ; (+ a b)
      postfix "!" 100
      a!              ; (! a)
      prefix "-" 100
      -a              ; (- a)
      brackets "(" ")" 100
      (a)             ; (a)
      arity f 2
      f 17 42         ; (f 17 42)
      flat "+"
      a + b + c       ; (+ a b c)
      sym "+"
      a + b           ; terms will be sorted

- Sequences of symbols form tree-structured *terms*.  The tree structure is determined syntactically by the binding power, fixity and arity of each symbol.  We do not distinguish terms from expressions.

## Constants and variables

- New symbols are by default *variables*.  That includes operators such as "+" after declaring them as infix.

- Q: Is the default a good idea?  Possibly we should enforce the user to declare a symbol as a variable or constant.

- If we assign a value to a new symbol, it will be a *constant*.

- Constants can be declared by the keyword `const`.

      const x   ; to declare constant symbols

- Variables can be declared by the keyword `var`.

      var x     ; to declare variable symbols

- Once a symbol is declared as constant, it can not be declared variable anymore.  A symbol that is constant inside a block, can be become variable again outside the block.

- If a symbol is not declare variable or constant than its first usage determines its role:

     x + y = 0      ; x and y are variables
     forall x F(x)  ; x is a variable
     let a = 17     ; a is a constant

- Symbols starting with a dollar sign `$` are always variables.

- Symbols starting with a at sign `@` are always boolean variables, that could contain whole formulas.a

## Variable binding operators

- The symbols `forall` and `exists` are examples of *variable binding operators*.

      forall x F
      exists x F

- The first input to a variable binding operator must be a variable that appears must appear free in F.  Some simple type checking has to ensure that!

- Variable binding operators must be declared to ensure that the first arg is checked to be a non-bound variable.

      bindop forall
      bindop exists

- Before declaring a symbol to be `bindop` it must have an arity.

- Syntactic sugar:  the variable can also be a boolean expression where the first part is the variable.

      forall x>0 F(x)   ; forall x (x > 0 implies F(x))

- More examples

      arity "lim" 3, "sum" 4, "prod" 4, "integral" 4
      bindop "lim"  ; limit, e.g., lim x 0 F(x)
      bindop "sum"  ; sum, e.g., sum x 0 1 F(x)
      bindop "prod" ; product, e.g., prod x 0 1 F(x)
      bindop "int"  ; integration, e.g., int x 0 1 F(x)

## Free and bound variables

- A variable is *free* in a term if it is not bound by a variable binding operator.

To be continued!

## 2025-04-17

### difference between prefix and function

    !!![2] prefix f 17
    !!![3] arity g 1
    !!![4] parse g 1 8
    g 1 8
    !!![5] format sexpr
    !!![6] parse g 1 8
    ((g 1) 8)
    !!![7] parse f 1 8
    (f (1 8))
    !!![8] prefix h 25
    !!![9] parse h 1 8
    ((h 1) 8)

- so `arity` defines a function with a fixed lbp and rbp, while `prefix` allows us to choose the `rbp`.

- use `prefix` if you want stronger or weaker rbp than space

### definitions via 'def' (how are they different from `use` and `alias`?

- `alias` is replaced in the scanner, i.e., they do not require an inference step
- `def` is replaced in the parser, i.e., they require an inference step
- definitions are equalities or equivalences (which is equality on bool)
- how can we have definitions without equalities? no!
- 'def' are very much 'use'

### indentation

- an equation chain like

    x = 17
      = 42
      = 13

- desugars to

    x = 17
    x = 42
    x = 13

- for a chain we have an order of operations

    chain =, <=, <
    chain =, >=, >
    chain iff, if
    chain iff, implies

- so, e.g.

    x < y
      = z

  desugars to

    x < y
    x < z

- so if there is at least `<` in the chain we get `<` for the remaining ones.

### line continuation (2025-04-18)

- an unfinished line can be automatically continued in the next line

### chains

- chains do require indentation!  You can not do this:

    x = 18
    = 20       ; that's wrong!
    = 30

- but they can have:

    x = 18
      = 20
      = 30

- so if we have a line starting with an infix operator it creates a chain with the previous

- when a chain starts we have to check whether the infix operator is compatible with the other operators of the chain

- chains must start with an indent token

### impl-elim

- The RHS of an implication can be an conjunction

- i.e.

    A and B  implies  C and D

  will automatically split `C` and `D` into `C` and `D`

- this is useful stuff like

    a = b = c

  which gets parsed as

    a = b and b = c

- we can then also:

    a = b
      = c
