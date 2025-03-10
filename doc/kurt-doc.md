# The Kurt Programming Language Documentation

**Author:** Stefan Harmeling
**Date:** 2025-02-25 (created)

---

The Kurt programming language is a made to write down and automatically check simple (and not so simple) mathematical proofs.  The motivation is to have a language that students can use while learning mathematics.  Similarly to automatic testing while learning programming, students can write down their proofs in Kurt and test them automatically to get immediate feedback.

## Alternatives using Higher-Order Type Theory

Isabelle, Coq, Lean4

## Alternatives using First-Order Logic

- Mizar     <https://mizar.uwb.edu.pl>
- Metamath  <https://us.metamath.org>

## Formalizing 100 proofs in mathematics

<https://www.cs.ru.nl/~freek/100/>

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

- Once a symbol is declared as a variable or constant, it can not be switched back.

- If a symbol is not declare variable or constant than its first usage determines its role:

     x + y = 0      ; x and y are variables
     forall x F(x)  ; x is a variable
     a := 17        ; a is a constant

- Symbols starting with a dollar sign `$` are always variables.

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

## Types

- There are only two types: boolean and non-booleans.  We need this distinction since we have to treat them differently in proofs.

- A good foundation is the Neumann-Bernays-Gödel set theory <https://de.wikipedia.org/wiki/Neumann-Bernays-Gödel-Mengenlehre>.

- The non-booleans are class, some of which are sets.  If we define variables, they have to be elements of some class, e.g.

     const G             ; some set or class
     var x,y,z in G      ; this declares x, y, z to be elements of G
     forall x forall y  x+y = y+x  ; now they can be quantified over

- Functions are also builtin.  Actually functions are sets as well.

     const f : G -> G    ; a function from G to G

- Defining a groups with some axioms, defines the class of all groups.

     def G : Group = { G, *, inv, e | ... }

## Sets and classes

- All objects are *classes* following Neumann-Bernays-Gödel set theory.

- Objects that are also elements of some class are called *sets*.

- The class of all groups can be defined.  Can we quantify over it?

- Variables can be declared to be elements of some set, e.g.,

     var x : Nat
     forall x  x>=0

- We use "∈" and ":" as aliases for the relation "in".

- Following the axioms of NBG, we have set constructors:

     var x : Nat
     def A = { x | Phi }     ; where Phi is some formula

     def emptyset = { x | false }
     def $A cap $B = { x | x:A and x:B }
     def $A cup $B = { x | x:A or x:B }
     def $A \ $B   = { x | x:A and not x:B }
     def $A subset $B = forall x:A x:B
     def Power($A) = { x | x subset A }

## Functions

- Functions are also sets, but we have special notation to define functions:

     var f : Real -> Real    ; this define the arity of `f` to be 1

## Equality

- insight: `iff` is `=` for boolean

## Formulas

- A *formula* is a term of type `Bool`.

- Let `E`, `F`, `G`, `H` be formulas.  Then there are four ways
  to state them in a line of a Kurt program:

        use E    ; unproven, but can be used from now on
        F        ; must be derivable from the previous lines
        assume G ; unproven, but can be used from now on
        show H   ; to be proven, but can not yet be used, only after a proof

  The keyword `show` announces a new fact, that gets pushed onto the
  `show-stack`, which collects unproven statements.  After the next
  proof, the fact is checked whether it has been proven.  If yes, it
  is popped from the stack, if not, we get an error.

- We can start blocks or local sections that allow us to have local
  definitions and local assumptions.  Statements from inside a block
  are valid outside as an implication of the assumptions.

        proof
           assume A
           B
           assume C
           D

  Outside the proof we can use now the expressions (w/o explicitly stating them):

        A implies B
        A and C imply D

## Case distinction

- A disjunction like

        x >= 0  or  x < 0

  is the basis of a case distinction.  To show `F(x)`, we prove

        x >= 0 implies F(x)
        x <  0 implies F(x)
        F(x)

  More abstractly, we have

        A or B                             # case distinction
        A implies C
        B implies C
        (A implies C) and (B implies C)
        (not A or C) and (not B or C)      # def of `implies`
        (not A and not B) or C             # distributive law
        not (A or B) or C                  # de morgan
        (A or B) implies C                 # def of `implies`
        C                                  # modus ponens

- To support case distinctions, we could have something like:

        x>=0 or x<0                        # case distinction
        case x>=0                          # block with assumption A
           F(x)
        x>=0 implies F(x)
        case x<0                           # block with assumption B
           F(x)
        x<0 implies F(x)
        (x>=0 or x<0) implies F(x)
        F(x)                               # thus

- So `case` is just syntactic sugar that is translated into a proof, i.e.

        case x>=0
           F(x)

  gets translated into

        proof
           assume x>=0
           F(x)

  which then implies

        x>=0 implies F(x)  ; by proof

- Question: do we need here a constant `x` or a variable `x`?
  Probably it should be a constant, since we are asking for `x>=0`,
  however, that might be confusing for the user.

- Thus, the `case` macro, e.g.

        case A
            B

  gets translated into

        assume A
            B
        A implies A
  
  which is then checked line by line.

## Comments label lines

- Everything after a semicolon is a comment.

- However, comments are not ignored.  Instead they provide some soft
  labels.

- What is a soft label?
  - It doesn't have to be unique.
  - We can measure the similarity between two labels by approximate
    string matching.
  - Similar labels will link those lines in a proof and give hints to
    the proof checker.
  - Also, the comments can be checked, whether the provided links make
    sense.

- Lines starting with a label labels either the next line or the
  previous line.

## Special formulas

- `x is y` is a special formula, where `y` is a predicate with one input, in this case `x`.

## Shell

- keywords for the shell

      help     ; show help
      parse    ; parse an expression (for debugging the grammar)
      format   ; determine the format of a parsed expression
      level    ; shows the current level
      load     ; load a file, Q: what is the difference to `use`
      syntax   ; prints the syntax of the language
      theory   ; prints the formulas of the theory
      rules    ; print all inference rules
      info     ; show information about a symbol (or about all symbols)

## Rules

- Inference rules or short *rules* define how to proof new lines from previous ones.  What is the minimal set of rules necessary?  

- Proved implications and proved equations create new rules.

- An inference rule like this

       A
       B
       -------
       C

   is written in Kurt like this:

       $$A and $$B implies $$C

   We use '$$' to have variables which do not appear elsewhere.

- I.e., any implication defines a rule.

- Some special rules are built-in:

         A
         ---
         B
         ----------- ; implies_intro
         A implies B

         ----------- ; equal_intro
         x = x

         ----------- ; top_intro
         true

         A
         ----------- ; identity
         A

- Rules without quantifier:

         (A implies B) and A implies B                            ; implies_elim (modus ponens)
         (true implies A) implies A                               ; top_elim
         A(x) and x==y implies A(y)                               ; equal_elim

         A and B implies A and B                                  ; and_intro
         A and B implies A                                        ; and_elim
         A and B implies B                                        ; and_elim

         A implies A or B                                         ; or_intro
         B implies A or B                                         ; or_intro
         (A or B) and (A implies C) and (B implies C) implies C   ; or_elim


         (A implies B) and (B implies A) implies (A iff B)        ; iff_intro
         A iff B implies A implies B                              ; iff_elim
         A iff B implies B implies A                              ; iff_elim

         A and not A implies false                                ; bottom_intro
         false implies A                                          ; bottom_elim

         (A implies false) implies not A                          ; not_intro
         not not A implies A                                      ; not_elim

- Rules with quantifier:

         (var x) and A(x) implies forall x A(x)                      ; forall_intro
         forall x A(x) implies A(t)                                  ; forall_elim
         A(t) implies exists x A(x)                                  ; exists_intro
         (exists x A(x)) and (var c) and (A(c) implies B) implies B  ; exists_elim

- Rules for induction:
         A(0) and (forall n in Nat  A(n) implies A(n+1)) implies forall n in Nat  A(n)  ; induction

- There is a challenge to be solved: how can we match a formula against `A(x)`?  The difficulty is that
  part of the formula should be matched against `A` and part against `x`.

- Also the notation `A(x)` is not really clear.  Notation suggestion:

         A // x=t     ; this is A where variable x is replaced by t

  It doesn't matter whether `x` is really appearing in `A` or not.

- Let's try again to rewrite the relevant formulas:

- "equal_elim" is easy to write:

         A and x=y implies (A // x=y)                                ; equal_elim

- "forall_intro"

         A implies forall x A                            ; forall_intro

  Here the `forall` on the RHS of the implication will ensure that `x` is a variable that is freely appearing in `A`.

- "forall_elim"

         forall x A implies (A // x=t)                               ; forall_elim

- "exists_intro"

         (A // x=t) implies exists x A                               ; exists_intro

- "exists_elim"

         (exists x A) and ((A // x=c) implies B) implies B  ; exists_elim

- "induction"

         (A // x=0) and (forall n in Nat  (A // x=n) implies (A // x=n+1)) implies forall n in Nat  A  ; induction

- Ok, this is much better! However, it remain unclear how we can match a formula against `A // x=t`.

## Definitions

- Definitions are written as follows:

       def x = 0      ; declares a constant with a value

- The formula following a definition must be an equation or an equivalence, i.e., it must have the form `x = y` or `x iff y`.

- The LHS of "=" or "iff" must contain exactly one constant symbol, but possibly several variables.

- Syntactic sugar:

       x := 17             ; declares a constant with a value
       def x = 17          ; same thing
       A(x) :iff B(x)      ; defines a predicate
       def A(x) iff B(x)   ; same thing

  I suggest that we do not allow this kind of syntactic sugar, since the ":" is already used for elements in sets.

## impl_intro and proof/qed

- Let's look at code!

    show A implies B
    proof
        assume A
        B
    qed

- How about:

    show A and B
    proof
        A
        B
        A and B
    qed

- In both cases for the qed, we have to collect all assumptions and create an implications.

- The premise is always a conjunction.  The empty conjunction is always true (the empty disjunction is always false).

- Thus `true implies A` is equivalent to `A`.  So far, so good!

## Constraints

- How can we express constraints on constants?

        exists x A
        def c with (A // x=c)

  Now `c` is a constant that satisfies the constraint `(A // x=c)`.

## Unification

Source: <https://en.wikipedia.org/wiki/Unification_(computer_science)>

- solve systems of equations with LHS and RHS
- if RHS has no free variables, this is *pattern matching*

- first-order: variables are not functions
- higher-order: variables can also be functions (syntactic unification)
- E-Unification: semantic unification

- we need higher-order unification, do we?  or is first-order enough?

## equal_elim

- let's look at some example and solve it by hand

        const "f"
        bool "f"
        use ($A and $x=$y) implies ($A // $x=$y)
        use a = 17
        use f(a)
        f(17)

- how to match "f(17)" against "$A // $x=$y"?

        ; matching "f(17)" against "$A // $x=$y"
        $y = 17
        $A = f($x)
        ; next match "$A" against "$f(a)"
        $x = a
        ; finally, "$x=$y" matches already against "a=17"
        ; BINGO

- however, the initial step is the most difficult:
  - why match "$A" to "f($x)" and not to "$x(a)"

- two approaches
  - approach 1: take "f(17)" and search for formulas that match up to a single spot, then search for the fitting equation
  - approach 2: take "f(17)" and search for equations that contain subterms, then search for the fitting formulas

- we implement approach 1

## Some rules have substitutions

- equal_elim

         ($A // $x=$s) and $s=$t implies ($A // $x=$t)         ; equal_elim

  plan:
  - search theory that matches the goal formula up to a single term (possibly appearing repeatedly)
  - then $x is non-matching term (might appear several times)

- "forall_intro"

         $A implies forall $x $A                            ; forall_intro

  - it doesn't matter, whether $x appears in $A or not
  plan:
  - match first RHS then LHS, this should work already!
  -

- "forall_elim"

         forall x A implies (A // x=t)                               ; forall_elim

- "exists_intro"

         (A // x=t) implies exists x A                               ; exists_intro

- "exists_elim"

         (exists x A) and ((A // x=c) implies B) implies B  ; exists_elim

- "induction"

         (A // x=0) and (forall n in Nat  (A // x=n) implies (A // x=n+1)) implies forall n in Nat  A  ; induction

## minimal rules (2025-03-08)

- In propositional logic we only need:

    use $A   implies   $A                                  ; restatement
    use ($A IMPLIES $B)   implies   ($A implies $B)        ; impl-intro
    use ($A implies $B) and $A   implies   $B              ; impl-elim

  These three inference are all implemented in `kurt.py`.  Note that `impl-intro` is called when we close a proof with `qed` and `IMPLIES` is shown by a `proof`-`qed`-block.

- Note on `restatement`: we do allow substitution of variables , so actually we have:

    use $A implies ($A // $x=$a)                       ; restatement

  I.e., we can substitute variables in `$A` with arbitrary terms.  That is how we implemented `restatement` in `kurt.py`.

- In substitutions like `$x=$a`, the LHS `$x` is variable that gets assigned, while the RHS is a term where we can plug in anything.  However, we denote this "anything" by `$a`

- If we add equality we additionally have:

    use ($A // $x=$a) and $a=$b implies ($A // $x=$b)  ; equal-elim
    use $x=$x                                          ; equal-intro

- So an expression like `17=17` is obtained from `equal-intro` using `restatement` with variable substitution `{$x=17}`.  We write a substitution as a python dictionary.

- Curiously, `restatement` is a special case of `equal-elim` if we set `$a` to `$x`.

## library mechanism

- We do not support loading libraries twice.  The main reason is that the knowledge we are building should be constructed but never deconstructed, i.e., if we load libraries twice, we would have to remove the old syntax and old axioms and invalidate all formulas that used those and the ones that used the those, etc.