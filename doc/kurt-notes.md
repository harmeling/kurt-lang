# The Kurt Programming Language Notes

**Author:** Stefan Harmeling
**Date:** 2025-02-25 (created)

---

This document collects notes while inventing the language.  There are many more older notes in the previous git repo.

## Alternatives using Higher-Order Type Theory

- Automath  <https://www.cs.ru.nl/F.Wiedijk/aut/index.html>
- Isabelle
- Coq
- Lean4  (the current champion)

## Alternatives using First-Order Logic

- Mizar     <https://mizar.uwb.edu.pl>
- Metamath  <https://us.metamath.org>

- people: Freek Wiedijk <https://www.cs.ru.nl/F.Wiedijk/>

## Formalizing 100 proofs in mathematics

<https://www.cs.ru.nl/~freek/100/>

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
         ----------- ; implies-intro
         A implies B

         ----------- ; equal-intro
         x = x

         ----------- ; top-intro
         true

         A
         ----------- ; identity
         A

- Rules without quantifier:

         (A implies B) and A implies B                            ; implies-elim (modus ponens)
         (true implies A) implies A                               ; top-elim
         A(x) and x==y implies A(y)                               ; equal-elim

         A and B implies A and B                                  ; and-intro
         A and B implies A                                        ; and-elim
         A and B implies B                                        ; and-elim

         A implies A or B                                         ; or-intro
         B implies A or B                                         ; or-intro
         (A or B) and (A implies C) and (B implies C) implies C   ; or-elim


         (A implies B) and (B implies A) implies (A iff B)        ; iff-intro
         A iff B implies A implies B                              ; iff-elim
         A iff B implies B implies A                              ; iff-elim

         A and not A implies false                                ; bottom-intro
         false implies A                                          ; bottom-elim

         (A implies false) implies not A                          ; not-intro
         not not A implies A                                      ; not-elim

- Rules with quantifier:

         (var x) and A(x) implies forall x A(x)                      ; forall-intro
         forall x A(x) implies A(t)                                  ; forall-elim
         A(t) implies exists x A(x)                                  ; exists-intro
         (exists x A(x)) and (var c) and (A(c) implies B) implies B  ; exists-elim

- Rules for induction:
         A(0) and (forall n in Nat  A(n) implies A(n+1)) implies forall n in Nat  A(n)  ; induction

- There is a challenge to be solved: how can we match a formula against `A(x)`?  The difficulty is that
  part of the formula should be matched against `A` and part against `x`.

- Also the notation `A(x)` is not really clear.  Notation suggestion:

         A // x=t     ; this is A where variable x is replaced by t

  It doesn't matter whether `x` is really appearing in `A` or not.

- Let's try again to rewrite the relevant formulas:

- "equal-elim" is easy to write:

         A and x=y implies (A // x=y)                                ; equal-elim

- "forall-intro"

         A implies forall x A                            ; forall-intro

  Here the `forall` on the RHS of the implication will ensure that `x` is a variable that is freely appearing in `A`.

- "forall-elim"

         forall x A implies (A // x=t)                               ; forall-elim

- "exists-intro"

         (A // x=t) implies exists x A                               ; exists-intro

- "exists-elim"

         (exists x A) and ((A // x=c) implies B) implies B  ; exists-elim

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

## impl-intro and proof/qed

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

## equal-elim

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

- equal-elim

         ($A // $x=$s) and $s=$t implies ($A // $x=$t)         ; equal-elim

  plan:
  - search theory that matches the goal formula up to a single term (possibly appearing repeatedly)
  - then $x is non-matching term (might appear several times)

- "forall-intro"

         $A implies forall $x $A                            ; forall-intro

  - it doesn't matter, whether $x appears in $A or not
  plan:
  - match first RHS then LHS, this should work already!
  -

- "forall-elim"

         forall x A implies (A // x=t)                               ; forall-elim

- "exists-intro"

         (A // x=t) implies exists x A                               ; exists-intro

- "exists-elim"

         (exists x A) and ((A // x=c) implies B) implies B  ; exists-elim

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

## library mechanism (2025-03-10)

- We do not support loading libraries twice.  The main reason is that the knowledge we are building should be constructed but never deconstructed, i.e., if we load libraries twice, we would have to remove the old syntax and old axioms and invalidate all formulas that used those and the ones that used the those, etc.

## implement a better `impl-elim` or `equal-elim`

- How do we match expressions with variables at head positions

- Example `equal-elim`:

    use ($A // $x=$a) and $a=$b implies ($A // $x=$b)

- how MATCH, first runterhangeln bis zu den variablen, dann variable ohne substitution match und schauen, wie viel substitutions man braucht, dann kann man schon so einiges ausschliessen.  unter denen dann alle combination wo die substituted variable vorkommt ausprobieren.

## assignment

- assignment `:=` could be useful for subs and definitions

      x := 18       ; an axiom
      use x = 18    ; same thing

## alpha conversion (aka gebundene Umbennung)

- this is already built-in and working

        use forall $x $A
        forall $y B

## substitutions (subs) (2025-03-12)

- `A // $x=a` is the formula that replaces all free occurrences of `$x` in `A` with `a`.

- notation
        $A // $x = $a         ; easy-to-read notation with equality
        $A // $x := $a        ; easy-to-read notation with assignment
        bindop sub            ; substitution is also a binding operator, however, the first arg must be a variable
        arity sub 3           ; three inputs, a variable, a term to substitute, a term where something is replaced
        sub $x $a $A          ; notation without equality

- i.e., only free occurrences of variables can be substituted

- in `$A // $x=$a`, only `$A` and `$a` are free, `$x` is bound, so subs is a binding operator.

- for `$A // $x=$a` there are two important requirements

    1. the expression assigned to `$a` does not contain any bound variables of `$A`
    2. the expression assigned to `$a` does not contain `$x`

- req 1 is good, since it avoid destroying the inner workings of `$A`

- req 2 is limiting the flexibility, but allows us to formulate `exist-elim`:  

  - by req 2 we can be sure that `$B // $x=$b` does not contain `$x` (because in `$B` potential appearance of `$x` are replaced by `$b` and `$b` does not contain `$x`.

  - however, req 2 makes it impossible to match `A//$x=$a` against the formula `A`, since we can not plug in `$x` for `$a`.

  - solution: use double-dollar variables for more flexibility:

         $A // $$x = $a           ; now we can sub `$x` for `$a` (but not `$$x`)

    let's reserve double-dollar variables for the most general inference rules.  the idea is similar to using `_x` variables in python

- subs ordering

        ((A // $x=a) // $x=b)    ; which one happens first: always from the inside out

    1. before outer subs, apply inner subs
    2. the inner subs variable `$x` can not be replaced, since it must be a variable

- `A // ($x=a, $y=b)` is an abbreviation of `(A // $x=a) // $y=b`

- see also <https://en.wikipedia.org/wiki/Lambda_calculus#Substitution> for a recursive definition of `sub`

- substitutions are only allowed in `use` lines, not in regular stuff, so they are designed to formulate axiom schemata.

## alternative notations that avoid equality

    A // $x=a          ; with equality, easy to understand
    A // $x:=a         ; with assignment, a special new infix operator, maybe
    A / $x / a         ; inspired by s/foo/bar, not so good
    A // $x // a       ; inspired by s/foo/bar, even worse
    subs $x a A        ; function styled, probably the best, since it is tenary

- however, before deciding on the most minimalistic notation, we should just use `A // $x = a`

## how to formulate the quantifier and equality inference rules

- equality

      use $x = $x                                                      "equal-intro"
      use ($A // $$x = $a) and $a = $b implies ($A // $$x = $b)        "equal-elim"

  the double-dollar ensures that `$a` can also be substituted also by all single-dollar variables, e.g. `$x` (but not by `$$x`)

- forall quantification

      use $A implies forall $x $A                                      "forall-intro"
      use forall $x ($A // $$x=$x) implies ($A // $$x=$a)              "forall-elim"    ; `$a` must not contain variables that are bound by `$A`

  here req 1 ensures that `$a` does not contain variables that are bound by `$A`.
  note that `forall $x $A implies ($A // $x=$a)` is not sufficient, since we can not match `$A//$x=$a` against `$A`

- exist quantification

      use ($A // $$x=$a) implies exists $x ($A // $$x=$x)              "exists-intro"   ; `$a` must not contain variables that are bound by `$A`

  here req 1 ensures that `$a` does not contain variables that are bound by `$A`

      use (exists $x ($A//$$x=$x)) and (forall $x (($A//$$x=$x) implies ($B//$x=$b))) implies ($B//$x=$b)    "exists-elim"    ; `$x` should not occur free in `$B`
      use (exists $x ($A//$$x=$x)) and (($A//$$x=$x) implies ($B//$x=$b)) implies ($B//$x=$b)                "exists-elim"    ; `$x` should not occur free in `$B`
      use (exists $x $A and ($A implies ($B//$x=$b)) implies ($B//$x=$b)                                     "exists-elim"    ; `$x` should not occur free in `$B`

  two variants: the difficulty is that `$x` must not appear in the conclusion.  This is ensured through req 2, since it ensures that `$b` does not contain `$x`.  The double dollars ensure that we can use this formula for any single dollar variables.

## how to implement matching against substitutions (2025-03-13)

- time for matching against substitutions, e.g. `$A // $x=$a`

- first of all: without outer substitutions the formula `$A // $x=$a` resolves to `$A` since there is no `$x` to replace.  however, for matching, we first assign `$A` and `a` and then apply the substitution `$x=$a`

- before we can apply the substitution, we have to assign `$A` to something that possibly contains `$x`.

- example:  match term `F x 17` against pattern `$A // $x=$a`

  - there are five possibilities:

        $A = F  x  17     $a = ?
        $A = $x x  17     $a = F
        $A = F  $x 17     $a = x
        $A = F  x  $x     $a = 17
        $A = $x           $a = F x 17

    without matching other parts of an implication, we can not decide which to use

  - however, we could iterate through all of them and try all other matchings of the other terms

- example: match term `F 17 17` against pattern `$A // $x=$a`

  - there are six possibilities:

        $A = F  17  17    $a = ?
        $A = $x 17  17    $a = F
        $A = F  $x  17    $a = 17
        $A = F  17  $x    $a = 17
        $A = F  $x  $x    $a = 17
        $A = $x           $a = F 17 17

- probably a slow but simple implementation will iterate through these possibilities and try all other formulas, that's it

- all rules, only `$A`, `$B`, `$a` and `$b` get assigned from the outside to any terms

      use $a = $a                                                                                     "equal-intro"
      use ($A // $$x=$a) and $a = $b implies            ($A // $$x=$b)                                "equal-elim"
      use ($A // $$x=$a)             implies  forall $x ($A // $$x=$x)                                "forall-intro"
      use forall $x ($A // $$x=$x)   implies            ($A // $$x=$a)                                "forall-elim"
      use ($A // $$x=$a)             implies  exists $x ($A // $$x=$x)                                "exists-intro"
      use (exists $$x ($B//$$y=$$x)) and (($B//$$y=$$x) implies ($A//$$x=$a)) implies ($A//$$x=$a)    "exists-elim"

      ; CAREFUL: the latter is still not fully general, what about matching with a `$B` that contains `$x`

- how to match:

      - match `$A // $$x = $a` against ...

      - example 1: put all nodes of `f 17 17` into a list, iterate over that list
        1.  `$A = f   17  17`
        2.  `$A = $$x 17  17`     look for more `f` down the list (none found)
        3.  `$A = f   $$x 17`     look for `17` down the list (one found)
        3.1 `$A = f   $$x $$x`    alternative
        4.  `$A = f   17  $$x`    look for more `17` down the list (none found)

      - example 2: put all nodes of `f 17 17 17` into a list, iterate over that list
        0.  `$A = f   17  17  17 `   without using `$$x` and `$a`
        1.  `$A = $$x`               `$a=f 17 17 17`, look for more `$$x` down the list (none found)
        2.  `$A = $$x 17  17  17`    `$a=f`         , look for more `f` down the list (none found)
        3.1 `$A = f   $$x 17  17`    `$a=17`        , look for `17` down the list (two found, iterate all 00, 01, 10, 11)
        3.2 `$A = f   $$x $$x 17`    `$a=17`        , alternative
        3.3 `$A = f   $$x 17  $$x`   `$a=17`        , alternative
        3.4 `$A = f   $$x $$x $$x`   `$a=17`        , alternative
        4.1 `$A = f   17  $$x 17`    `$a=17`        , look for more `17` down the list (one found)
        4.1 `$A = f   17  $$x $$x`   `$a=17`        , alternative
        5.  `$A = f   17  17  $$x`   `$a=17`        , look for more `17` down the list (none found)

      - to generate alternatives, call `find_next_along_the_tree` which yields twice if one is found (once with and once without)

## Alternatives (2025-03-26)

- Let's consider a simple axiom:

      use ($A // $$x=$a) and $a = $b implies ($A // $$x=$b)                                           "equal-elim"

- We first match the conclusion `($A // $$x=$b)`.

- Option 1: `yield` all possible assignments for `$A` and `$b`.  This might be wasteful, since there might be not matching premises.

- Option 2: Postpone the assignment of `$A` and first identify the other occurrences of `$A` among the premises.

- The semantics of `($A // $$x=$b)` is "any formula with some location replaced by `$b`".

## Again let's understand the formulas

- for `$A // $x=$a` there are two requirements

    1. the expression assigned to `$a` does not contain any bound variables of `$A`
    2. the expression assigned to `$a` does not contain `$x`

- two substitution operators:

      $A // $b       ;   substitute some occurrences of   a subterm of `$A`   in `$A` with `$b`
      $A // $a = $b  ;   substitute some occurrences of   term `$a`           in `$A` with `$b`

  - the location can appear once or several times depending on the needs of the matching formula.
  - again: `$b` must not contain any bound variable of `$A` (is this really necessary?)

- "equal-intro": easy, replace `$a` with any term

      use $a = $a                                         "equal-intro"

- "equal-elim": important, both `$a` and `$b` can be any term

      use ($A // $a = $b) and $a = $b implies  $A         "equal-elim"

  - note on LHS, we can replace *any* number of occurrences of `$a` by `$b`

- "forall-intro": how about

      use $A  implies  forall $x $A

   where we must match `$A` and `$x`.  then for matching `$A` we must allow renaming of the free variable `$x` and other free variables

- "forall-elim":  choose any subterm in `$A` for replacement by `$x`

      use forall $x ($A // $x)  implies  $A                                "forall-elim"

   note: all occurrences of the chosen subterm of `$A` must be replaced, otherwise, we could choose to replace `$y` in `$A` we get

      use forall $x $x=$x    implies $x=$y   ; wrong

- "exists-intro": replace `$A` with a boolean term and `$a` can be any term

      use ($A // $x=$a)             implies  exists $x $A                 "exists-intro"

  note:
        - `$x` is bound on both sides of the implication, this ensures that we replace the correct subterm
        - on the LHS we must replace all occurrences of `$x` in `$A`

- "exists-elim": replace `$A` and `$B` with boolean terms

      use (exists $$x $B) and ($B implies $A)  implies  $A         "exists-elim"

  the trick here is that double-dollar variables like `$$x` are only allowed in `use`, i.e.

      - `$A` does not contain `$$x`
      - also the corner cases where `$$x` does not appear in `$B` are fine

## 2025-03-29

- another attempt, only substitute variables

      use $a = $a                                                         "equal-intro"
      use ($A // $x = $a) and $a = $b          implies  ($A // $x = $b)   "equal-elim"
      use $A                                   implies  forall $x $A      "forall-intro"
      use forall $x $A                         implies  ($A // $x = $a)   "forall-elim"
      use ($A // $x = $a)                      implies  exists $x $A      "exists-intro"
      use (exists $$x $B) and ($B implies $A)  implies  $A                "exists-elim"

- this looks quite good, let's look into the details

      use $a = $a                                                         "equal-intro"
      ; substitute `$a`
      ; in other words: terms equal themselves

      use ($A // $x = $a) and $a = $b          implies  ($A // $x = $b)   "equal-elim"
      ; iterate over all possibilities of the RHS, possibly first look for equations
      ; in other words: look for a formula where one term (or more copies of it) have been substituted

      use $A                                   implies  forall $x $A      "forall-intro"
      ; substitute `$A` with renaming of the bound variable `$x`
      ; then match LHS where the free variables in `$A` can be adjusted
      ; in other words: look for a formula without the universal quantification

      use forall $x $A                         implies  ($A // $x = $a)   "forall-elim"
      ; iterate over all possibilities of the RHS
      ; in other words: look for a formula that universally quantifies one of the terms (the `$a`) in `$A`

      use ($A // $x = $a)                      implies  exists $x $A      "exists-intro"
      ; substitute `$A` with renaming of the bound variable `$x`
      ; in other words: look for a formula where the existentially bound variable `$x` is replaced by a term `$a`

      use (exists $$x $B) and ($B implies $A)  implies  $A                "exists-elim"
      ; note that `$$x` can not appear in `$A`
      ; in other words: look for other implications with premise that also appear elsewhere existentially quantified

- now we only have a single requirements for `$A // $x=$a`:

    1. the expression assigned to `$a` does not contain any bound variables of `$A`,
       more precisely:
       - only free occurrences of `$x` in `$A` are replaced
       - for each location of `$x` there is a certain set of bound variables in `$A`, that must not appear in `$a`
       - alternatively, we could be more strict, not to allow any bound variables in `$A` to appear in `$a`

- the axioms for quantifier

      use $A                                   implies  forall $x $A      "forall-intro"
      use forall $x $A                         implies  ($A // $x = $a)   "forall-elim"
      use ($A // $x = $a)                      implies  exists $x $A      "exists-intro"
      use (exists $$x $B) and ($B implies $A)  implies  $A                "exists-elim"

- the axioms for equality

      use $a = $a                                                         "equal-intro"
      use ($A // $x = $a) and $a = $b          implies  ($A // $x = $b)   "equal-elim"

- next topic: syntactic sugar

## 2025-04-02 matching against `sub`

- if the `expr` is some `sub` expression itself, we are not substituting, since we want to infer that exact expression with the `sub` operator

- let's assume that `pattern` is some `sub` expression

        expr    = anything
        pattern = sub $x $a $A
        pattern = sub $x expr_a $A
        pattern = sub $x $a expr_A
        pattern = sub $x expr_a expr_A

## 2025-04-04 example

        use x = 17
        use f x
        use ((sub $x $a $A) and ($a = $b)) implies (sub $x $b $A)
        f 17

- how to prove this?

- step 1:  match `f 17` against one of the conclusions of the theory
  - here we match against `sub $x $b $A`
  - this leads to substitution `subst` for `$b` and `$A`, e.g.,

        { $A=f $x, $b=17 }

- step 2:  take the premises and apply the `subst`
  - premises after substitution

       sub $x $a (f $x)
       $a = 17

- step 3: match theory against the premises (NOT the other way around) and extend the substitution
  - let's match the theory against the premises
  - match `x = 17` against `$a = 17` to extend `subst` with `$a=x`
  - apply `subst` to the remaining premise to obtain

       sub $x x (f $x)

- step 4: match theory against this
  - either find a theory formula with `sub` or transform it to `f x`

- current problem:  `kurt -dv tests/proofs/forall.kurt`

## 2025-04-10 sneaky cases

Working on `tests/proofs/forall.kurt` we have:

    use (forall $x $@var1) implies (sub $x $@var2 $@var1) "forall-elim"
    use forall $x B $x
    A $x

Now we can prove `A $x` just by the following substitution:

    {$@var1: $x, $@var2: A $x, $x: B $x}

which turns the formula above into:

    (forall $x (B $x)) implies (sub $x (A $x) $x)

which is by resolving the substitution:

    (forall $x (B $x)) implies (A $x)

However, we made some illegal substitutions!

Ok, the problem is already here:

     use f $z
     use f $x
     find sub $x $a $A

How should we match `f $z` against `sub $x $a $A`:

     { $A = f $z }
     { $A = $x, $a = f $z }
     { $A = f $x, $a = $z }
     { $A = $x $z, $a = f }

How should we match `f $x` against `sub $x $a $A`:

     { $A = f $x }
     { $A = $x, $a = f $x }

## 2025-04-12

- in formulas like

    forall $x $A
    sub $x $a $A

  we are not allowed to rename the bound variable `$x`, because it might appear in `$A` which could appear elsewhere as well.

- free variables can (and sometimes should) be renamed on a formula level, since they are implicitly universally quantified

- however bound variables must not be renamed, since they might appear in variables such as `$A` below:

    use $A                                   implies  forall $x $A      "forall-intro"
    use forall $x $A                         implies  sub $x $a $A      "forall-elim"
    use sub $x $a $A                         implies  exists $x $A      "exists-intro"
    use (exists $$x $B) and ($B implies $A)  implies  $A                "exists-elim"

- e.g. renaming `$x` in "exists-intro" in the LHS makes the whole formula wrong, since `$x` might appear in `$A` which appears also on the RHS.

## 2025-04-23 blocks

- we don't do an indentation based approach, but pascal style with `let`, `take`, `assume` blocks being ended with `thus`, and `proof` blocks with `qed`.  the basic form is `proof` and `qed`, the other blocks are syntactic sugar tailored to `forall-intro`, `exists-intro` and `impl-intro`.

- note that we do require newlines to separate expressions

- ideally, we get also some `macro` mechanism to extend the language

- `show`, `proof`, `qed` are built-in and the basis for the other blocks

        show p
        proof
          foo
          p
        qed               ; checks whether the announced formulas has been derived

- impl-intro

        assume p
          bla bla
          q
        thus p ⇒ q        ; impl-intro

  translates to

        show p ⇒ ___
        proof
          use p
          bla bla
          q
        qed               ; this checks whether `p ⇒ q` has been derived

- more details: the `thus p ⇒ q` matches the last `show` entry which is `p ⇒ $EXPR$` and checks whether it has been derived

- the `p ⇒ q` is actually already on the outer scope, since it doesn't need the `use p`

- forall-intro

        let ε>0
          bla bla
          F(ε)
        thus ∀ε>0 F(ε)    ; forall-intro

  which is short for the long version:

        show ∀ε>0 ___
        proof
          const ε         ; the first variable symbol in `ε>0`, on this level now `ε` is constant
          use ε>0
          bla bla
          F(ε)
          ε>0 ⇒ F(ε)
        qed               ; check whether `∀ε>0 F(ε)` was derived, `ε` being variable again

- exist-intro

        take δ=3*ε
          δ > 0
          bla bla
          G(δ)
        thus ∃ δ>0 G(δ)   ; exists-intro, same as `∃δ δ>0 ∧ G(δ)`

  translates to

        show ∃ δ>0 ___
        begin
          const δ         ; declare `δ` as constant
          use δ=3*ε       ; together with previous line same as `def`
          δ>0           ; follows from properties of `ε`
          bla bla
          G(δ)
          δ>0 ∧ G(δ)
        end               ; checks whether `∃δ>0 G(δ)` was derived, `δ` being variable again

- then we have another short block

        A by
          foo
          blo
        qed

  translates to

        show A
        proof
          foo
          blo
        end               ; checke whether `A` was derived

- equation sequences can be indented or not

## note on variables and constants

- variables can not be constrained, i.e., implicitly they are universally quantified for each formula

- variables can be declared to be `const` inside a block

- symbols are automatically declared to be variable through their usage in variable binding quantifiers
