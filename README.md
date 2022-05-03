# POSIX Lexing with Bitcoded Regular Expressions

Run the code with

```isabelle build -c -v -d . Posix```

Tested with Isabelle2021-1.


* RegLangs.thy (contains basic definitions for Regular Languages)

* PosixSpec.thy (contains values and POSIX definitions)

* Positions.thy (shows the equivalence of our POSIX spec and the definition by Okui & Suzuki)

* PDerivs.thy (Partial Derivatives according to Antimirov, size bounds of pderivs)

* Lexer.thy (first algorithm by Sulzmann & Lu without simplification)

* LexerSimp.thy (correctness for simple-minded simplification rules)

* Blexer.thy (second algorithm by Sulzmann & Lu without simplification)

* BlexerSimp.thy (correctness for aggressive simplification rules)

* Finite Bound Result: BasicIdentidies.thy, ClosedForms.thy, GeneralRegexBound, ClosedFormBounds.thy (formalises all resilts from Section 5 in the paper)