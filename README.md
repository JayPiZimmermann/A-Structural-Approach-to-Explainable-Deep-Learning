# A Structural Approach to Explainable Deep Learning

**From DC Decompositions to Two-Player Games**

Master's thesis by Jakob Zimmermann.

The thesis brings together two papers: *Hidden Monotonicity: Explaining Deep
Neural Networks via their DC Decomposition*
([CVPR 2026 Highlight](https://cvpr.thecvf.com/virtual/2026/poster/36564)) and
*Playing the Network Backward: A Game-Theoretic Attribution Framework*
([arXiv preprint](https://arxiv.org/abs/2605.06212)). It integrates their
theoretical and empirical results, extends the convex/monotone decomposition of
a network to smooth activations and Transformers, and adds a partial
formalization of the mathematics in Lean 4.

## Repository layout

- `formalization/thesis.pdf`: the compiled thesis. `formalization/draft-proofs/`
  holds rendered Lean files that the PDF links to.
- `tex/`: LaTeX sources of the thesis; the root file is `tex/main.tex`.
- `formalization/`: the Lean 4 / mathlib formalization (see
  `formalization/README.md`).

## Build the thesis

Requires a TeX Live installation with `latexmk` and Biber.

```sh
cd tex
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
makeindex main.nlo -s nomencl.ist -o main.nls
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

Then copy `tex/main.pdf` to `formalization/thesis.pdf`.

## Check the Lean proofs

Install [elan](https://github.com/leanprover/elan), then:

```sh
cd formalization
lake exe cache get
lake build All
```

`lean-toolchain` and `lake-manifest.json` pin the Lean version and mathlib.

## Lean links in the PDF

Statements in the thesis carry numbered Lean references. Each one links to the
corresponding declaration in this repository at a fixed revision.

## Code

The implementations accompanying the two papers are published separately:
[split-network implementation](https://github.com/JayPiZimmermann/DC-Decomposition-for-Explanability)
and [game-based attribution](https://github.com/JayPiZimmermann/Playing_The_Network_Backward_Official_Repository).
