# Dependent Multiplicities in Dependent Linear Type Theory — Agda artefact

This is the artefact for the POPL 2027 paper *Dependent Multiplicities in
Dependent Linear Type Theory* by Maximilian Doré.

The paper presents DLTT, a linear type theory embedded in a dependent type
theory (DTT). Supplies (objects of a symmetric monoidal closed category) and
productions (morphisms between supplies) are ordinary data types of the host
DTT, so Agda itself can be used to build objects and morphisms in any linear
Category with Families (lCwF). The artefact therefore acts as a prototype type
checker for the elaborated system. It contains:

* the elaboration of every rule of DLTT: all linear type formers, including
  dependent multiplicities, fractions, linear W-types and `!`;
* all example programs of the paper, e.g. `foldMaybe`, `map`, `quicksort` and
  capture-avoiding substitution `subst` for lambda terms.

Archived version: **TODO Zenodo DOI**.
Browsable HTML version (the links in the paper point here):
<https://maxdore.github.io/popldltt/html/DLTT.Everything.html>.
The archive also contains the same rendering under `html/`.

---

## 1. Getting started (≈ 10 minutes)

### Requirements

| Software | Version | Notes |
|---|---|---|
| Agda | **2.6.4.3, 2.7.0.1, 2.8.0 or 2.8.0.2** | the only dependency; no Agda libraries are needed |
| `make`, `bash`, `zip` | any | only for the helper scripts |

The full check (`make check`, see below) passes with each of these Agda
versions on macOS 26 (Apple Silicon), with no warnings:

| Agda | How it was obtained |
|---|---|
| 2.6.4.3 | Homebrew (built with GHC 9.12.1) |
| 2.7.0.1 | prebuilt release binary (with `Agda_datadir` set to the `data/` folder of the archive) |
| 2.8.0 | prebuilt release binary |
| 2.8.0.2 | prebuilt release binary |

The development uses nothing platform specific, so it should work wherever one
of these Agda versions runs (Linux, macOS, Windows/WSL). Older versions have
not been tested.

### Installing Agda

If `agda --version` already prints one of the versions above, skip this step.

**Recommended: prebuilt binary (a few minutes, nothing to compile).** Download
the archive for your platform from the Agda 2.8.0.2 release
<https://github.com/agda/agda/releases/tag/v2.8.0.2>:

| Platform | File |
|---|---|
| Linux (x86_64) | `Agda-v2.8.0.2-linux.tar.xz` |
| macOS, Apple Silicon | `Agda-v2.8.0.2-macOS-arm64.tar.xz` |
| macOS, Intel | `Agda-v2.8.0.2-macOS-x64.tar.xz` |
| Windows | `Agda-v2.8.0.2-win64.zip` |

Each archive contains a single self-contained `agda` executable. For example,
on Linux:

```sh
mkdir -p ~/agda-2.8.0.2 && cd ~/agda-2.8.0.2
curl -LO https://github.com/agda/agda/releases/download/v2.8.0.2/Agda-v2.8.0.2-linux.tar.xz
tar -xJf Agda-v2.8.0.2-linux.tar.xz
./agda --version        # Agda version 2.8.0.2
```

Either add this directory to your `PATH`, or pass the binary to the check
explicitly with `make check AGDA=~/agda-2.8.0.2/agda`. On macOS, if you
downloaded the archive with a browser and Gatekeeper blocks the binary, run
`xattr -d com.apple.quarantine agda` first; this is not needed when you
download with `curl`.

**Alternative: build from source with cabal (about 20–40 minutes).**

```sh
# install ghcup, ghc and cabal: https://www.haskell.org/ghcup/
cabal update
cabal install Agda-2.8.0.2      # or Agda-2.6.4.3
agda --version
```

See also <https://agda.readthedocs.io/en/v2.8.0/getting-started/installation.html>.

### Sanity check

Unpack the archive, preferably in your home directory, and run the check from
the artefact root:

```sh
cd DLTT-artefact-<version>
make check
```

`make check` (equivalently `./scripts/check.sh`) deletes all interface files
and typechecks `DLTT/Everything.agda`, which imports every module, from scratch.
This takes a few seconds on a recent laptop. It also checks that:

* every `.agda` file was typechecked, i.e. is (transitively) imported by
  `DLTT/Everything.agda`, so nothing is skipped;
* every file is checked with `--safe` (see [Section 3](#3-soundness-of-the-development));
* there are no postulates, holes (`{! !}`) or pragmas and flags that switch
  off a check (`NON_TERMINATING`, `NO_POSITIVITY_CHECK`, `--type-in-type`,
  `--allow-unsolved-metas`, `REWRITE`, …).

The output ends with

```
== Result
  ALL CHECKS PASSED
```

and the exit code is 0, without any warnings.

---

## 2. Claims of the paper and where they are checked

The paper marks every formalised lemma and example with an Agda logo that links
to the HTML rendering. The table below lists each of them. **Evaluation:** a
claim holds if `make check` succeeds. Agda then has typechecked the stated
definition against the type that corresponds to the statement in the paper.
To inspect a claim, open the file at the given identifier or follow the link
into `html/` (e.g. `html/DLTT.Base.html#SupplyExp`).

Paths are relative to `DLTT/`. Numbers refer to the final version of the paper.

### Section 1 (Introduction)

| Paper | Claim | Artefact |
|---|---|---|
| §1, "Agda artefact" | All rules of DLTT are elaborated, and all examples are built in the elaborated system | `Everything.agda` (imports every module) |

### Section 2 (DLTT as an embedding of linear logic into DTT)

| Paper | Claim | Artefact |
|---|---|---|
| §2.1 | Supplies and productions are data types of the host DTT | `Base.agda`: `sply`, `_⇒_` |
| §2.1 | The left unitor is derivable using `σ` (swap) | `Base.agda`: `unitl`, `unitl'` |
| Example 2.3 | Supply for a dependent pair of linear terms | `Examples/Structure.agda`: `ExpSupply` |
| Definition 2.4 | Exponentiation of supplies and productions by a natural number | `Base.agda`: module `SupplyExp` (`_^_`, …) |
| Lemma 2.5 | Coercions between exponentiated supplies (ℕ coercions) | `Examples/Structure.agda`: module `Coercions` |
| Lemma 2.6 | Derived structural rules | `Examples/Structure.agda`: module `LinearRules` |
| Example 2.7 | Linear function `snd` on pairs with multiplicity 0 on the first component | `Pair.agda`: module `snd` (`sndᵒ`) |
| Lemma 2.8 | ⊸β is admissible | `Function.agda`: module `FunBeta` (`⊸βLeft`, `⊸βRight`, `⊸βLeftRight≡`) |
| §2.2 | Computation rules for linear Booleans | `Bool.agda`: module `Beta` (`𝟚ᵒβtrue`, `𝟚ᵒβfalse`, …) |
| Example 2.9 | Internal choice `A ⊕ B` with constructors and eliminator | `Examples/Sum.agda`: `_⊕_`, `inl⊕`, `inr⊕`, `elim⊕` |
| Example 2.10 | `foldMaybe` | `Examples/Maybe.agda`: `foldMaybe` |
| §2.3 | A simple monoidal solver for coercions | `ProductionSolver.agda`: macro `solve`; examples in `Examples/Solver.agda` |
| Example 2.11 | Converting `Δ^(m+n)` into `Δ^m ⨾ Δ^n` in an open term | `Examples/Structure.agda`: module `ExpConv` |

### Section 3 (Semantics)

| Paper | Claim | Artefact |
|---|---|---|
| §3.3 | Linear types are interpreted by recursion on a type of linear types | `Base.agda`: module `ltypsemantics` (`ltyp`, `_⊩_`) |
| Lemma 3.5 | Any lCwF models `𝟘`, `𝟙` and `𝟚` | `Empty.agda`, `Unit.agda`, `Bool.agda` |
| Lemma 3.6 | Any lCwF models `⊗` | `Pair.agda` (`intro⊗`, `elim⊗`, `⊗β`, `⊗Cut`) |
| Lemma 3.7 | Any lCwF models `⊸` | `Function.agda` (`⊸I`, `⊸App`) |
| Theorem 3.8, Examples 3.9, 3.12 | Elaboration theorem, concrete models | *not formalised* (stated in §1) |

### Section 4 (Inductive types)

| Paper | Claim | Artefact |
|---|---|---|
| §4.1 | Dependent eliminator for linear lists | `Examples/List.agda`: module `elimList` |
| Lemma 4.1 | An lCwF models linear lists | `Examples/List.agda`: module `recList` |
| Example 4.2 | `map` | `Examples/List.agda`: `map` |
| Definition 4.3 | Fractions of lists | `Base.agda`: module `ListFraction` |
| Example 4.4 | `toFrac` and induction with fractional multiplicities | `Examples/List.agda`: module `ind` |
| Lemma 4.5 | An lCwF models fractional lists | `Examples/List.agda`: module `FractionElaboration` |
| Example 4.6 | `head` with a fractional multiplicity | `Examples/List.agda`: `headF` |
| Example 4.7 | Quicksort, and a sorting test | `Examples/Quicksort.agda`: `quicksort`, `quicksortF`, `test`; filter: `Examples/List.agda`: `filter` |
| §4.2 | Finite linear types | `Base.agda`: module `FinJoin` |
| Lemma 4.8 | An lCwF models linear W-types | `W.agda` (`introWᵒ`, `elimWᵒ`, `compWᵒLeft`, `compWᵒRight`) |
| Example 4.9 | Linear natural numbers as a W-type, and `double` | `Examples/Nat.agda`: `ℕᵒ`, `double`, `test` |
| Definition 4.10 | Fractions of W-types | `Base.agda`: `Fraction` |
| Example 4.11 | Lambda terms and substitution | `Examples/Lambda.agda`: `Lambda`, `except`, `subst` |

### Section 5 (Recovering intuitionistic logic with a bang)

| Paper | Claim | Artefact |
|---|---|---|
| Example 5.1 | `pairMaybe` | `Examples/Maybe.agda`: `pairMaybe` |
| §5 | Productions of the linear exponential comonad (`!ᶠ`, `χ`, `ξ`, `ζ₀…ζ₄`) | `Base.agda`: constructors `!ᶠ`, `dupl`, `erase`, `use`, `mult`, `coh◇`, `coh⨾`, `coh⨾'` of `_⇒_` |
| Corollary 5.2 | `!`-functions | `Function.agda`: `⊸!I`, `⊸!App` |
| Example 5.3 | `pairMaybe` using `!` | `Examples/Maybe.agda`: `pairMaybeBang` |

### Section 6 (DLTT as an extension of QTT)

Theorems 6.2, 6.4 and 6.5 are meta-theorems and are *not formalised*, as stated
in §1 of the paper.

### Computations

Some modules contain closed computations checked by `refl`. Typechecking them
runs the programs inside Agda's type checker:

* `Examples/Nat.agda`, `test`: doubling 2 gives 4.
* `Examples/Quicksort.agda`, `test`: quicksort sorts a list of 10 numbers.

---

## 3. Soundness of the development

* All files start with `{-# OPTIONS --safe #-}`. Agda then rejects postulates, `TERMINATING` and
  other pragmas that turn off a check. `scripts/check.sh` verifies this.
* `ProductionSolver.agda` is a reflection-based tactic that only *generates*
  productions: it flattens both supplies of a goal `Δ₀ ⇒ Δ₁` into lists of
  atoms, using structurally recursive functions which build the productions
  from `assoc`, `swap`, the unitors and functoriality of `⨾`, and permutes
  them. Any production it generates is still typechecked by Agda. Apart from
  `Everything.agda`, only `Examples/Solver.agda` imports it, so none of the
  other results depend on it.
* The equality of linear terms is Agda's intensional identity type (see §2 of
  the paper).

---

## 4. Additional description

### Layout

```
DLTT.agda-lib            Agda library file (no dependencies)
Makefile                 make check | html | zip | clean
scripts/check.sh         full check from scratch (see Section 1)
scripts/make-zip.sh      builds the archive uploaded to Zenodo
html/                    pre-generated HTML rendering (in the archive only)
DLTT/
  Everything.agda        entry point, imports all modules
  Prelude.agda           host DTT: Σ, W-types, lists, ℕ (built-ins only)
  Base.agda              supplies, productions, exponentiation, linear
                         types and their interpretation, fractions
  Function.agda          dependent linear functions ⊸ and !-functions
  Pair.agda              dependent linear pairs ⊗
  Empty.agda Unit.agda Bool.agda
                         linear 𝟘, 𝟙, 𝟚
  W.agda                 linear W-types
  ProductionSolver.agda  reflection-based solver for coercions (macro solve)
  Examples/
    Structure.agda       basic workings of the linear structure (§2)
    Sum.agda Maybe.agda  ⊕, Maybe, foldMaybe, pairMaybe
    List.agda            lists, map, fractions of lists, filter, head
    Quicksort.agda       quicksort
    Nat.agda             linear ℕ as a W-type
    Lambda.agda          lambda terms and substitution
    Solver.agda          coercions constructed by the solver
```

### Key definitions

* `sply` and `_⇒_` (`Base.agda`): supplies and productions. A production is a
  morphism of a symmetric monoidal closed category with a right adjoint to
  context extension (`Λ`) and a linear exponential comonad (`!`).
* `ltyp` and `_．` (`Base.agda`, module `ltypsemantics`): linear types and
  their underlying host types.
* `Δ ⊩ A` (`Base.agda`): a linear term of type `A` that uses supply `Δ`, i.e.
  a host term `a : A ．` together with a production `Δ ⇒ (a ∶ A)`.
* `Coerce` (`Base.agda`): precomposes a production. This is how the
  structural coercions of the surface syntax are elaborated.

### Writing your own programs

Create a file, e.g. `DLTT/Examples/MyExample.agda`:

```agda
{-# OPTIONS --safe #-}
module DLTT.Examples.MyExample where

open import DLTT.Base
open import DLTT.Function
open import DLTT.Examples.Maybe

-- your definitions here, following e.g. Examples/Maybe.agda
```

and typecheck it from the artefact root with `agda DLTT/Examples/MyExample.agda`,
or interactively in Emacs or VS Code (agda-mode). For a new linear program, the
usual pattern is:

1. state the type with `⊸` and dependent multiplicities `⟨ x ∈ A ⟩^ m ⊸ B x`;
2. build the body with the introduction and elimination rules (`⊸I`,
   `elim⊕`, `elimList`, …);
3. use `Coerce` with a production for any structural rearrangement of the
   supply.

A program that uses a resource the wrong number of times does not typecheck,
because the required production between supplies does not exist.

### Reuse

The core (`Prelude`, `Base`, and the type-former modules) is self-contained and
uses only Agda's built-in modules, so it can be added as a library by putting
`DLTT.agda-lib` in your Agda `libraries` file. New linear type formers can be
added by extending `ltyp` in `Base.agda` and giving their elaboration in a
separate module, following `Pair.agda` or `W.agda`.

### Rebuilding the archive

`make zip VERSION=<v>` copies only the sources and scripts into a fresh
directory and runs `make check` there. It then generates `html/` and writes
`dist/DLTT-artefact-<v>.zip`.

## Licence

TODO: add a `LICENSE` file (e.g. MIT or BSD-3-Clause).
