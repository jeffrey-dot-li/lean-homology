# Plan: Eilenberg–Zilber Homotopy Equivalence (`F₁ ≃ F₂`)

## Goal

Fill the two `sorry`s that complete `eilenbergZilber : HomotopyEquiv (F₁.obj X) (F₂.obj X)`
in `Bisimplicial.lean`:

```
homotopyShuffleAWId : Homotopy (shuffleMap X ≫ alexanderWhitney X) (𝟙 (F₁.obj X))
homotopyAWShuffleId : Homotopy (alexanderWhitney X ≫ shuffleMap X) (𝟙 (F₂.obj X))
```

Here `F₁` is the **total complex** of the double complex and `F₂` is
`alternatingFaceMapComplex ∘ diag`. **Both are unnormalized.**

## Reference

Matthias Franz, *Szczarba's twisting cochain and the Eilenberg–Zilber maps*
(`pdfs/Franz_EilenbergZilberMap.pdf`), **Section 3** (pp. 3–5). The relevant content is
the contraction identities, eq. (3.6):

```
AW ∇ = 1,    ∇ AW = 1 + d(H),    H ∇ = 0,    AW H = 0,    H H = 0.
```

with `AW` = Alexander–Whitney (3.1), `∇` = shuffle map (3.2), `H` = Eilenberg–Mac Lane
homotopy (explicit (3.3), recursive (3.4)), and `F = ∇AW` (3.5).

## CRITICAL CORRECTION: the original plan was unsound

The previous docstring proposed proving the **strict** equality
`shuffleMap ≫ alexanderWhitney = 𝟙 (F₁.obj X)` and wrapping it with `Homotopy.ofEq`,
via a shuffle-pairing argument (a component lemma `ezComponent ≫ awComponent = δ_{r,p}`).

**This is false on the unnormalized complex.** In Franz the chain complex `C(X)` is the
**normalized** complex (p. 2, "We denote the normalized chain complex … by `C(X)`"), and
all of (3.6) — including `AW∇ = 1` — is a normalized statement.

### Counterexample (unnormalized, `p = 1, q = 0, n = 1`)

Using Franz's own formulas (3.1)/(3.2), there is a single `(1,0)`-shuffle and

```
AW(∇(x ⊗ y)) = x ⊗ y  +  d₁ x ⊗ s₀ y       (x ∈ X₁, y ∈ Y₀)
```

The cross term `d₁ x ⊗ s₀ y` is the `(r,s) = (0,1) ≠ (1,0)` component. It is **degenerate**
(`s₀ y`), so it dies on the normalized complex but **survives unnormalized**. Hence:

- `AW∇ = 1` strictly only after normalization;
- the would-be lemma `ezComponent_comp_awComponent_ne` (`= 0` for `r ≠ p`) is false unnormalized;
- `Homotopy.ofEq` cannot be used for `homotopyShuffleAWId` on `F₁`.

(The scaffold built on these false lemmas has been reverted to a single `sorry`.)

## Direction map (Lean ↔ Franz)

| Lean | Franz | Identity (3.6) | Notes |
|------|-------|----------------|-------|
| `shuffleMap : F₁ → F₂` | `∇` (Tot → diag) | chain map | ✅ done (`comm'`) |
| `alexanderWhitney : F₂ → F₁` | `AW` (diag → Tot) | chain map | ✅ done (`comm'`) |
| `homotopyAWShuffleId`: `AW ≫ ∇ ≃ 𝟙 F₂` | `∇AW = 1 + d(H)` | genuine homotopy; needs `H` | ❌ `sorry` |
| `homotopyShuffleAWId`: `∇ ≫ AW ≃ 𝟙 F₁` | `AW∇ = 1` | strict on **normalized** only | ❌ `sorry` |

`Homotopy f g` encodes `f - g = d ∘ h + h ∘ d`, so `∇AW = 1 + d(H)` is exactly a
`Homotopy (AW ≫ ∇) (𝟙)` with homotopy operator `H`.

## Chosen approach: Route B (build the Eilenberg–Mac Lane homotopy)

### Out of scope — the 1–2–3 relations (Franz §5, eqs. (5.3)/(5.4))

An earlier draft included a "Phase 0" for the "1–2–3" compatibility
`∇_{X, Y×Z} (1 ⊗ AW_{Y,Z}) = AW_{X×Y, Z} ∇_{X, Y×Z}` (Shih's Lemme II.4.2) and the
propositions it feeds (Franz 3.1/3.2/3.4). **This is not needed for our goal.** Those
relations are about *triple* Cartesian products `X × Y × Z` and the interaction of `H`
with `AW`/`∇` for the twisting-cochain theory (Szczarba/Shih). The plain 2-fold EZ
homotopy equivalence `F₁ ≃ F₂` does not touch them.

The only prerequisites for `homotopyAWShuffleId` are the explicit operator `H` and the
single identity `∇AW = 1 + d(H)` (Phase 1). Note (3.6) is itself *cited* in Franz from
Eilenberg–Mac Lane [4, Thm 2.1a]; §3 does not reprove it, so there is no Franz proof that
would pull in (5.3)/(5.4). (If we ever extend to twisting cochains, revisit these.)

### Phase 1 — `homotopyAWShuffleId` via `H` (the core Route B work; valid unnormalized)

1. **✅ DONE — Define the operator `H`.** Transcribed the explicit formula (3.3) directly
   (no derived-operator machinery). Concretely, in `Bisimplicial.lean`:

   - `emFstHom n p q μ : ⦋n+1⦌ ⟶ ⦋n⦌` — the horizontal (`x`) operator `s_{β+m} s_{m-1} ∂ⁿ_{n-q+1}`.
   - `emSndHom n p q μ : ⦋n+1⦌ ⟶ ⦋n⦌` — the vertical (`y`) operator `s_{α+m} ∂^{n-q-1}_m`.

     Both are built as a **single explicit `SimplexCategory.mkHom` order-hom** (closed form),
     derived by factoring the operator word into codegeneracy `≫` coface and collapsing:
     - `emFstHom`: `φ(j) = j` for `j < m`, else `m-1 + (μ.1 (j-m)).1`  (`m = n-p-q`).
     - `emSndHom`: `ψ(j) = j` for `j < m`, else `(n-p-q) + p + (μ.1 (j-m)).2`.
       The value is **clamped with `min _ n`** for totality (a no-op on the valid range
       `p+q < n`, which is the only range hit by the sum). Sanity-checked at `p=q=0`
       (`emFstHom ↦ σ_{n-1}`, `emSndHom ↦ σ_n`).
   - `emHomotopy X n : (F₂.obj X).X n ⟶ (F₂.obj X).X (n+1)` — the signed double sum (3.3),
     indexed by `d = p+q ∈ {0,…,n-1}`, `p ∈ {0,…,d}`, `μ : Shuffle (p+1) (d-p)`, with sign
     `(-1)^{n-d+1} · μ.sign` (the `m+1 = n-d+1` exponent — Franz footnote 2 — is kept).
   - `emHomotopy_zero : emHomotopy X 0 = 0`  (`H₀ = 0`, empty outer sum).
   - `emHomotopyHom X i j` — `H` as a degree-`+1` `Homotopy.hom` family (`emHomotopy X i`
     transported along `j = i+1`, else `0`); `emHomotopyHom_zero` discharges `Homotopy.zero`.

2. **Key identity `awShuffle_eq_id_add_dH` (the main `sorry`, Route B).** Stated per degree
   `n` in the `dNext`/`prevD` form expected by `Homotopy.comm`:
   ```
   (alexanderWhitney X ≫ shuffleMap X).f n
     = dNext n (emHomotopyHom X) + prevD n (emHomotopyHom X) + (𝟙 (F₂.obj X)).f n
   ```
   With `ComplexShape.down ℕ`: `prevD n = H_n ≫ d` (the `dH` term) and
   `dNext n = d ≫ H_{n-1}` (the `Hd` term), so this is exactly `∇AW = 1 + d(H)` (Franz 3.6).
   See the **Route B proof breakdown** section below.

3. **✅ DONE — Package** `homotopyAWShuffleId : Homotopy (AW ≫ ∇) (𝟙 F₂)` is assembled as a
   structure with `hom := emHomotopyHom X`, `zero := emHomotopyHom_zero X`,
   `comm := awShuffle_eq_id_add_dH X`. So once step 2 is proved, Phase 1 is complete.

   Auxiliary identities `H∇ = 0`, `AW H = 0`, `HH = 0` (rest of (3.6)) are useful sanity
   checks but only `∇AW = 1 + dH` is strictly required for this `Homotopy`.

### Route B proof breakdown for `awShuffle_eq_id_add_dH`

Franz does **not** prove (3.6) — he cites Eilenberg–Mac Lane [4, Thm 2.1a]. So the content is
EM's theorem. In our abstract setting everything is `SimplexCategory` morphisms pushed through
the (contravariant) bisimplicial object plus `ℤ`-linear combinations, so the identity reduces
to a finite-sum identity of operator words governed by the simplicial identities + sign and
reindexing bookkeeping — the same style as the existing chain-map (`comm'`) proofs.

**Assets already available:**
- `F = alexanderWhitney ≫ shuffleMap` is a chain map *for free* (both factors proven chain
  maps), i.e. `d F = F d`.
- `HomologicalComplex₂.total.hom_ext`, `ι_totalDesc(_assoc)`, and the simplicial-identity
  lemmas `ι_front_comp_δ_*`, `ι_back_comp_δ_*`, `fstHom_insertLeftStep_comp_δ`, etc.

**Milestones (do in order):**

1. **Base case `n = 0`.** `prevD 0 = emHomotopy X 0 ≫ d = 0` (by `emHomotopy_zero`) and
   `dNext 0 = 0` (no differential out of degree 0), so the goal collapses to
   `(∇AW).f 0 = 𝟙`. At `n=0` only the `p=q=0` shuffle exists and the faces are trivial.
   Small, self-contained; locks down the `total.hom_ext` / `awComponent` / `ezComponent`
   unfolding plumbing at degree 0.

2. **Operator-composition sub-lemmas (the reusable combinatorial core).** How `emFstHom` /
   `emSndHom` compose with `SimplexCategory.δ` / `σ`, and with the diagonal face map
   `(diag X).δ k = (X.map δₖ) ≫ (X.obj _).map δₖ`. Mirror the `*_comp_δ` lemmas already
   proven for `shuffleFstHom` / `ι_front`, in the `ext ⟨i,hi⟩; dsimp; split_ifs; omega` style.
   These express `dH + Hd` and `∇AW` in a common normal form.

3. **Full degree-`n` identity.** Expand LHS `∇AW.f n` and RHS `dNext + prevD` as signed sums
   over shuffles/faces/degeneracies, reindex, and cancel pairwise to leave the identity term
   (à la `universalSimplexCrossProduct_boundary`). This is the bulk of the work.

**Rejected alternative (Route A):** induct via the recursion (3.4) `Hₙ = -H'ₙ₋₁ + F'ₙ₋₁ s₀`.
Faithful to EM/Franz but requires formalizing the **derived operator** `f ↦ f'` and its laws
(Franz (2.4), Lemma 2.1) — heavy machinery not in Mathlib, and proving our explicit (3.3)
satisfies (3.4) may be as hard as Route B itself.

### Phase 2 — `homotopyShuffleAWId` (subtle; defer)

`AW∇ = 1` is strict **only normalized**. Two honest sub-routes:

- **(2a) Normalized + transport (recommended).** On the normalized Moore complex `AW∇ = 1`
  holds strictly, and the shuffle-**pairing** argument (the idea behind the reverted
  scaffold) is *valid there*. Transport along the Dold–Kan homotopy equivalence `N ≃ C`
  (Mathlib `AlgebraicTopology.DoldKan` / `NormalizedMooreComplex`).
- **(2b) Explicit second homotopy.** Construct `K` with `AW∇ = 1 + d(K)` directly on
  unnormalized. The classical EM contraction does **not** supply this (it gives strict
  `AW∇ = 1` only post-normalization), so this essentially re-derives Dold–Kan's contracting
  homotopy of the degenerate subcomplex — more work than (2a).

**Plan: do Phase 1 first, keep Phase 2 as `sorry`, then pursue (2a).**

## Current scaffold state (compiling)

```lean
-- Phase 1 — operators DONE, identity is the remaining sorry
def emFstHom (n p q) (μ : Shuffle (p+1) q) : ⦋n+1⦌ ⟶ ⦋n⦌ := …    -- ✅ s_{β+m} s_{m-1} ∂ⁿ_{n-q+1}
def emSndHom (n p q) (μ : Shuffle (p+1) q) : ⦋n+1⦌ ⟶ ⦋n⦌ := …    -- ✅ s_{α+m} ∂^{n-q-1}_m
def emHomotopy (X) (n) : (F₂.obj X).X n ⟶ (F₂.obj X).X (n+1) := … -- ✅ formula (3.3)
lemma emHomotopy_zero (X) : emHomotopy X 0 = 0 := …               -- ✅ H₀ = 0
def emHomotopyHom (X) (i j) : (F₂.obj X).X i ⟶ (F₂.obj X).X j := … -- ✅ Homotopy.hom family
lemma emHomotopyHom_zero (X) … : emHomotopyHom X i j = 0 := …     -- ✅ Homotopy.zero

lemma awShuffle_eq_id_add_dH (X) (n) :                            -- ❌ sorry (Route B, main work)
    (alexanderWhitney X ≫ shuffleMap X).f n
      = dNext n (emHomotopyHom X) + prevD n (emHomotopyHom X) + (𝟙 (F₂.obj X)).f n := sorry

def homotopyAWShuffleId (X) : Homotopy (alexanderWhitney X ≫ shuffleMap X) (𝟙 (F₂.obj X)) := -- ✅ packaged
  { hom := emHomotopyHom X, zero := emHomotopyHom_zero X, comm := awShuffle_eq_id_add_dH X }

-- Phase 2 (deferred → route 2a)
def homotopyShuffleAWId (X) : Homotopy (shuffleMap X ≫ alexanderWhitney X) (𝟙 (F₁.obj X)) :=
  sorry
```

## Supporting lemmas / API

- `Homotopy.mk` (or appropriate constructor) for assembling a `Homotopy` from `H` and the
  `1 + dH` identity.
- `HomologicalComplex₂.total.hom_ext`, `ι_totalDesc(_assoc)` — used heavily in existing
  `comm'` proofs; reused for the `∇AW` computation on the total complex.
- Existing simplicial-identity lemmas: `ι_front_comp_δ_of_le/_gt`, `ι_back_comp_δ_of_le/_gt`
  (`Bisimplicial.lean:89`–`146`).
- For Phase 2 (2a): Mathlib `AlgebraicTopology.DoldKan`, `NormalizedMooreComplex`, and the
  chain homotopy equivalence between normalized and unnormalized complexes.

## Difficulty estimate

| Item | Difficulty | Notes |
|------|-----------|-------|
| Phase 1: define `emHomotopy` (+`emFstHom`/`emSndHom`) | Medium | ✅ done — direct (3.3) transcription |
| Phase 1: `awShuffle_eq_id_add_dH` — base case `n=0` | Medium | start here; locks down plumbing |
| Phase 1: `awShuffle_eq_id_add_dH` — `emFst/SndHom ≫ δ` lemmas | Medium–Hard | reusable combinatorial core |
| Phase 1: `awShuffle_eq_id_add_dH` — full degree-`n` | **Hard** | main identity, the bulk of the work |
| Phase 1: package `Homotopy` | Easy | ✅ done — `homotopyAWShuffleId` assembled |
| Phase 2 (2a normalize+transport) | Medium–Hard | depends on Mathlib Dold–Kan ergonomics |

## Files involved

- `HomologyLean/SingularHomology/Bisimplicial.lean` — all definitions and the two homotopies.
- `HomologyLean/SingularHomology/Shuffle.lean` — shuffle/sign lemmas, if Phase 1 needs more.
- (Phase 2) Mathlib `AlgebraicTopology.DoldKan.*`.
