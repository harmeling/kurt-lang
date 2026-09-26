# How to write test-proofs?

1. Write the proof as a `.kurt`-file and store it inside `proofs/`.
2. That's it — the test suite just checks that `kurt` runs the file to completion without
   raising. No marker needed for the common case (an ordinary proof that succeeds, or one
   that uses `expect "KIND"` internally — see `doc/kurt-doc.md` §9.6 — to check its own
   interesting condition and finishes cleanly either way).
3. If your file's whole point is a *specific* expected error message rather than clean
   success — typically because the failure happens while a block *closes* (a dedent, `qed`,
   `break`, ...), which `expect` can't wrap, since `expect` only ever observes an
   error raised by an ordinary statement directly inside its own body — add `;;; ` on the
   file's last line, followed by (the start of) the expected error message, e.g.
     ;;; ProofError: can not derive `q`
   This also works for a file whose point is specific non-error output text. The comparison
   only needs the first 17 characters to match if the full line doesn't, so you don't need to
   spell out the entire message, just enough to identify it.
