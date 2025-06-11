> ⚠️ This repository is a mirror of `codeberg.org/emmabastas/proof-searching-for-ipc-in-agda`

# proof-searching-for-ipc-in-agda

Code/proofs in Agda for my bachelors thesis "A proof searching procedure for intuitionistic propositional logic in Agda"

**Version requirements**
- Agda `2.7.0.1`
- Agda stdlib `2.2`

## Contents
- `thesis.pdf` -- The thesis itself
- `slided.pdf` -- Some slides.
- `Prelude.agda` -- Various definitions and lemmas used throughout the thesis, but not integral parts of it.
- `LJ.agda` -- The formalization of `LJ` in Agda (section 3.3), the structural rules (section 3.4), and soundness (section 3.5).
- `LJf.agda` -- `LJf`, and the initial `isProvable` function that is not guaranteed by Agda to terminate (section 4).
- `Termination.agda` -- The version of `isProvable` using well-founded induction, guaranteed by Agda to terminate (section 5).
- `Translation.agda` -- Function to translate from proof trees in `LJf` to proof trees in `LJ` (section 6).
- `Examples.agda` -- Uses of `isProvable`a (section 7).

## Changelog
### 2025-06-11
  - Updated README with version information.
  - Added thesis pdf and slides.
