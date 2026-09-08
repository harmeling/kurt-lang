# How to write test-proofs?

1. Write the proof as a `.kurt`-file and store it inside `proofs/`.
2. The last line of that file should contain `;;; ` followed by the last line of the expected output, e.g.
     ;;; here comes the content that is used to check

   **Exception**: if the file already uses `expect "KIND"` to check its interesting condition
   internally (see `doc/kurt-doc.md` §9.6), you can skip the `;;; ` marker entirely — the file
   is assumed to just need to complete cleanly (`;;; Proof checked.`), which is what every
   `expect`-using file's marker said anyway before this was added. A file with *neither* a
   marker *nor* `expect` fails the test suite outright (on purpose — it isn't actually
   asserting anything), so this isn't a way to skip verification, just to skip retyping the
   same boilerplate line every time.
