# Revision history for telomare

## Unreleased -- `agda` branch (denotational design, ConCat, HVM2)

* **Agda denotational design** (`telomare.agda`): typed syntax `_⇨S_` with three
  homomorphic interpretations — execution `⟦_⟧K`, cost `⟦_⟧C`, and parallel
  work/span `⟦_⟧WS` — and machine-checked adequacy/precision (exact, auto-computed
  tel cost per program). See `README-Agda.md`.
* Added to `_⇨S_`: `minS`/`maxS` (comparators, cost 1); sum types (`_⊕_`,
  `inlS`/`inrS`/`caseS`) for data-dependent branching; recursive lists (`listT`,
  `nilS`/`consS`/`unconsS`); the 8-input Batcher sorting network `mergeSortS`
  (sorts + cost 38, by `refl`); and `lengthS`, a recursive list function via `fixS`
  with a proved exact cost.
* **ConCat circuit diagrams** (`ctc/`): the `_⇨S_` morphisms compiled via Conal
  Elliott's ConCat into circuit SVGs (`nix run .#telomare-ctc-svg`). See
  `ctc/DIAGRAMS.md`.
* **ConCat → HVM2 backend** (`ctc/src/HVM.hs`): a new code-emitting CCC category;
  `toCcc f :: HVM a b` produces a runnable HVM2/Bend program
  (`nix run .#ctc-to-hvm`). See `ctc/HVM-BACKEND.md` and `PARALLEL.md`.
* **Bend/HVM2 apps**: `nix run .#bend-hello`, `nix run .#bend-sort`.

## 0.1.0.0 -- YYYY-mm-dd

* First version. Released on an unsuspecting world.
