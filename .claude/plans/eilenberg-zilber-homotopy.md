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

1. **Define `emHomotopy X : ∀ n, (F₂.obj X).X n ⟶ (F₂.obj X).X (n+1)`** — the operator `H`.
   On the diagonal `X_{n,n}`, transcribe the explicit formula (3.3): a signed double sum
   over `p + q < n` and `(p+1, q)`-shuffles of (horizontal degeneracies + one face) in the
   first variable and (vertical degeneracies + faces) in the second. Structurally analogous
   to `ezComponent` / `awComponent` (compositions `(X.map _).app _ ≫ (X.obj _).map _`).

   - **Recommended: explicit formula (1a)** — direct definition, no auxiliary machinery.
   - Alternative: recursion (3.4) `H₀ = 0`, `Hₙ = -H'ₙ₋₁ + F'ₙ₋₁ s₀`. Rejected: requires
     formalizing Eilenberg–Mac Lane's **derived operator** `f ↦ f'` ([3, p. 59]), a
     nontrivial new construction.

   **Sign warning** (Franz footnote 2, p. 3): the exponent `m + 1 = n − p − q + 1` in (3.3)
   is essential; dropping it makes `d(H) = 1 − ∇AW` fail. Track signs carefully.

2. **Key identity `awShuffle_eq_id_add_dH`**:
   ```
   alexanderWhitney X ≫ shuffleMap X = 𝟙 (F₂.obj X) + (d ∘ H + H ∘ d)
   ```
   i.e. `∇AW = 1 + d(H)`. This is the main combinatorial theorem (cf. the existing
   `comm'` proofs, which already manage alternating signed sums of faces).

3. **Package** as `homotopyAWShuffleId := Homotopy.mk … emHomotopy …` using step 2.

   Auxiliary identities `H∇ = 0`, `AW H = 0`, `HH = 0` (rest of (3.6)) are useful sanity
   checks but only `∇AW = 1 + dH` is strictly required for this `Homotopy`.

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

## Proposed sorry-scaffold (all `sorry`'d, compiling)

```lean
-- Phase 1
def emHomotopy (X : BisimplicialObject C) (n : ℕ) :
    (F₂.obj X).X n ⟶ (F₂.obj X).X (n + 1) := sorry          -- formula (3.3)
lemma emHomotopy_zero (X) : emHomotopy X 0 = 0 := sorry      -- H₀ = 0
lemma awShuffle_eq_id_add_dH (X) :
    alexanderWhitney X ≫ shuffleMap X = 𝟙 (F₂.obj X) + … := sorry   -- ∇AW = 1 + dH
def homotopyAWShuffleId (X) : Homotopy (alexanderWhitney X ≫ shuffleMap X) (𝟙 (F₂.obj X)) :=
  Homotopy.mk … (emHomotopy X) …                            -- uses awShuffle_eq_id_add_dH

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
| Phase 1: define `emHomotopy` | Medium | direct (3.3) transcription, sign-heavy |
| Phase 1: `awShuffle_eq_id_add_dH` | **Hard** | main combinatorial identity, the bulk of the work |
| Phase 1: package `Homotopy` | Easy | plumbing once the identity holds |
| Phase 2 (2a normalize+transport) | Medium–Hard | depends on Mathlib Dold–Kan ergonomics |

## Files involved

- `HomologyLean/SingularHomology/Bisimplicial.lean` — all definitions and the two homotopies.
- `HomologyLean/SingularHomology/Shuffle.lean` — shuffle/sign lemmas, if Phase 1 needs more.
- (Phase 2) Mathlib `AlgebraicTopology.DoldKan.*`.
