# LaTeX paper

The paper gives a reader-friendly exposition of the sharp answer to Aoki's Question 2.14, with a complete proof and a Lean source concordance.

- Main source: [aoki_cup_powers.tex](aoki_cup_powers.tex).
- Compiled paper: [aoki_cup_powers.pdf](output/pdf/aoki_cup_powers.pdf).
- Proof sections: `sections/`.
- Declaration locations: `lean_declarations.json`; the typeset concordance is `lean_sources.tex`.

Build with a standard TeX Live or MacTeX installation containing `latexmk`, `newpx`, and the packages listed in the preamble:

```sh
sh build.sh
```

The build keeps auxiliary files in `tmp/pdfs/` and writes the final PDF to `output/pdf/`. The paper deliberately has no author line pending the author's choice. The source concordance uses relative links to the accompanying Lean project, with printed declaration names and line numbers. Keep the paper and Lean directories together to retain those links.

The paper is an exposition of the existing checked development; producing it does not modify the Lean proofs. See [the verification record](../lean/verification.txt) for the earlier successful build and axiom audit.

The LaTeX-only source bundle builds independently. Its links to Lean files require the accompanying Lean directory from the complete project archive. The paper's own build, link, and layout checks are recorded in `verification.txt`.
