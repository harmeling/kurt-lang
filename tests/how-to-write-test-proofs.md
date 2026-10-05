# How to write test-proofs?

1. Write the proof as a `.kurt`-file and store it inside `proofs/`.
2. That's it — the test suite checks that `kurt` runs the file to completion without raising.
3. If the file's point is an error, wrap the line (or the block) that raises it in
   `expect "KIND" "TEXT"` (see `doc/kurt-doc.md` §9.6): the error must be of that kind, and its
   message must contain the text (which is optional), e.g.

       expect "ProofError" "can not derive `q`"
           q

4. An error that only a whole file can make (a block still open at its end, `break` at its top
   level, a circular `load`, an export that `load` rejects, ...) goes into a helper file in a
   directory `helpers/` next to the test -- the test discovery skips those -- and the test loads
   it inside `expect`:

       expect "EvalError" "not all blocks closed"
           load "helpers/not-all-blocks-close.kurt"

   The same for something that is allowed inside `expect` (`use`, `load`, `def`, `chain` in a
   proof block: the content of `expect` is discarded anyway).

There are no `;;; ` markers on the last line any more (the test refuses them).
