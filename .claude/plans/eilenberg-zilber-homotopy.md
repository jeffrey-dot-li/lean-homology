# Plan: Eilenberg–Zilber Homotopy Equivalence (`F₁ ≃ F₂`)

## Goal

Produce `eilenbergZilber : HomotopyEquiv (F₁.obj X) (F₂.obj X)` in `Bisimplicial.lean` (ideally
natural in `X`), as a Mathlib-PR-quality Eilenberg–Zilber theorem for bisimplicial objects. Here
`F₁` is the **total complex** of the double complex and `F₂` is `alternatingFaceMapComplex ∘ diag`;
**both are unnormalized.**

**Strategy (see ★ CURRENT APPROACH):** the maps need *not* be the literal unnormalized
`shuffleMap`/`alexanderWhitney`. Prove the EZ contraction on the **normalized** complexes (where
the literature, EM Thm 2.1a, applies and one direction is strict), then **transport** to the
unnormalized `F₁`/`F₂` along the Dold–Kan homotopy equivalences. This replaces the earlier attempt
to fill `homotopyShuffleAWId`/`homotopyAWShuffleId` by an *exact unnormalized* `∇AW = 1 + dH`
(Route B, below) — which the literature never does and EM's Thm 2.1 framing suggests is false
off the normalized complex.

## References

**Primary: Eilenberg–Mac Lane, *On the groups H(Π,n), II* (1954), Chapter I.** This is the
source of the Eilenberg–Zilber theorem (Thm 2.1 / 2.1a) and the explicit homotopy.

> ⚠️ **Read `pdfs/mcl2_sections_1_2.md`, NOT `pdfs/mcl2.pdf`.** The PDF is an image-only scan
> with **no text layer** — text extraction returns only blank page markers, so it is useless to
> the agent. Chapters 1–2 (the EZ theorem, Thm 2.1/2.1a, and the derived-operator machinery)
> have been transcribed to the markdown file `pdfs/mcl2_sections_1_2.md`; use that. (If you must
> see a figure/page, render a page to PNG with `uv run --with pymupdf` and read the image.)

Key EM facts (see `mcl2_sections_1_2.md`):
- **Theorem 2.1** (unnormalized `K × L ⇄ K ⊗ L`): `f, ∇` form a *chain equivalence* — both
  composites are merely chain-homotopic to the identity. No explicit homotopy.
- **Theorem 2.1a** (normalized `K ×_N L ⇄ K_N ⊗ L_N`): *explicitly* there is a homotopy `Φ` with
  `f∇ = i` (**strict**) and `∂Φ + Φ∂ = ∇f − i`; plus `Φ∇ = 0`, `fΦ = 0` (modulo norms).
- The proof of 2.1 is obtained **from** 2.1a via the normalization theorem I.4.1 — i.e. EM
  themselves prove it normalized, then transport. This is exactly our approach below.

**Secondary: Matthias Franz, *Szczarba's twisting cochain and the Eilenberg–Zilber maps***
(`pdfs/Franz_EilenbergZilberMap.pdf` — text-readable). Restates the contraction identities (3.6)
`AW∇ = 1, ∇AW = 1 + d(H), H∇ = 0, AW H = 0, HH = 0` and gives the **explicit** (Rubio–Morace)
homotopy formula (3.3) and the EM recursion (3.4). Franz's `C(X)` is the **normalized** complex,
and (3.6) is *cited* from EM [4, Thm 2.1a] — Franz does not reprove it.

**Survey finding on the hard half (`homotopyInvHomId`).** We looked specifically for a proof of
`AW ≫ ∇ ≃ 𝟙` (equivalently `∂Φ + Φ∂ = ∇f - i`) that starts from the **closed Rubio–Morace
formula** for `Φ` and verifies the homotopy identity directly. We did **not** find such a source.
What the literature supports is:
- **EM**: prove the identity by the **recursive** definition of `Φ` and an induction using
  derived operators (`pdfs/mcl2_sections_1_2.md:163`–`194`).
- **Franz**: states the explicit formula and the contraction identities, but cites EM for the
  latter; no direct closed-form proof.
- **Sergeraert** (`www-fourier.univ-grenoble-alpes.fr/~sergerar/Papers/EZ-submitted.pdf`): proves
  the **explicit** Rubio–Morace formula satisfies the **recursive** Eilenberg–Mac Lane definition,
  i.e. explicit ⇒ recursive ⇒ EM, not explicit ⇒ homotopy identity directly.

## ★ CURRENT APPROACH (chosen): prove EZ on normalized, transport to unnormalized

This **supersedes Route B** (the direct unnormalized construction below, kept for history).
Confirmed against EM directly (`mcl2_sections_1_2.md`, Thm 2.1/2.1a): the explicit homotopy is a
**normalized** statement, and even EM get the unnormalized equivalence by proving it normalized
and transporting. We do the same. We do **not** need the equivalence maps to be the literal
unnormalized `shuffleMap`/`alexanderWhitney`; an abstract `HomotopyEquiv` (eventually natural in
`X`) is acceptable for the Mathlib PR.

### Architecture (three pieces, composed by `HomotopyEquiv.trans`/`.symm`)

```
eilenbergZilber := bridge₁.symm.trans(eilenbergZilberNormalized.trans bridge₂)
   F₁  ≃[bridge₁]  N₁  ≃[EZ_norm]  N₂  ≃[bridge₂]  F₂
```

> **STATUS (2026-06):** `eilenbergZilber` is **assembled and compiling**
> (`BisimplicialNormalized.lean:757`). `bridge₁` ✅ (axiom-clean, `BisimplicialBridge1.lean`),
> `bridge₂` ✅ (inline Mathlib equiv), `eilenbergZilberNormalized.homotopyHomInvId` ✅ (strict).
> **The only remaining `sorry`** in the entire pipeline is
> `eilenbergZilberNormalized.homotopyInvHomId = homotopyNormalizedAlexanderWhitneyShuffle`
> (the EM `Φ` homotopy `AW ≫ ∇ ≃ 𝟙 N₂`). Naturality of `eilenbergZilber` in `X` is still TODO.
> See **Milestones** below for the full breakdown.

- **`N₂ = diag ⋙ normalizedMooreComplex C`** — normalized diagonal.
- **`N₁ = normalizedMooreComplex _ ⋙ (normalizedMooreComplex C).mapHomologicalComplex _ ⋙ totalFunctor`**
  — bi-normalized total complex (normalize both simplicial directions, then total).

**Ingredient 0 — `eilenbergZilberNormalized : HomotopyEquiv (N₁ X) (N₂ X)`** (the literature part,
EM Thm 2.1a). Asymmetric and that asymmetry is the whole point of going normalized:
  - `homotopyHomInvId` = `∇ ≫ AW = 𝟙 N₁` **strictly** (`Homotopy.ofEq`); the degenerate
    cross-term `∂₁x ⊗ s₀y` that blocks this unnormalized is zero modulo norms. **Cheap.**
  - `homotopyInvHomId` = `AW ≫ ∇ ≃ 𝟙 N₂` via the explicit EM homotopy `Φ`. **The real work**
    (EM induction with derived operators). **Important survey result:** the sources we found do
    **not** give a direct proof from the closed Rubio–Morace formula alone; the literature-backed
    routes are either EM's recursive proof, or proving the explicit formula satisfies EM's
    recursion first (Sergeraert), then inheriting the EM argument. On the normalized complex the
    "modulo norms" steps are literally `0`.

**Lean implementation plan for `homotopyInvHomId` (EM recursive route, working from
`BisimplicialNormalized.lean`).** Keep the proof **local** to the normalized file and reuse
existing Mathlib Dold–Kan API rather than building a general quotient/derived-operator library.

1. **Work on the unnormalized diagonal side first.**
   - Let `h := alexanderWhitney X ≫ shuffleMap X : F₂.obj X ⟶ F₂.obj X` (EM's `∇f`).
   - Define the recursive EM operator on the diagonal complex `F₂.obj X`, degreewise:
     `phiRaw X n : (F₂.obj X).X n ⟶ (F₂.obj X).X (n+1)`.
   - Package it as a `Homotopy.hom`-style family exactly as in
     `Bisimplicial.lean`'s `emHomotopyHom`, so we can reuse the `dNext` / `prevD` form of
     `Homotopy.comm`.

2. **Use `PInfty`, not an abstract “mod norms” quotient theory.**
   - EM's “maps norms into norms” / “equal modulo norms” should be represented by postcomposing
     with `retractionN₂ = PInftyToNormalizedMooreComplex (diag.obj X)`.
   - Reuse Mathlib lemmas already present in the project:
     `PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap`,
     `inclusionOfMooreComplexMap_comp_PInfty`,
     `HigherFacesVanish.comp_P_eq_self`,
     `degeneracy_comp_PInfty`,
     and the naturality/idempotence lemmas for `PInfty`.
   - So the “preserves norms” proofs become “this term is killed by `≫ retractionN₂`”.

3. **Create only a tiny local derived-operator API.**
   - No general Mathlib-quality framework; just enough to express EM `(2.13)` and the induction.
   - Definitions/lemmas needed locally:
     - the derived operator `prime` (EM's `M ↦ M'`) for the class of diagonal operators used here;
     - a `Frontal` predicate for those operators;
     - the identities EM uses:
       `prime_comp_D0`, interaction with the truncated boundary `∂'`,
       and the “higher faces are degenerate / killed by `PInfty`” consequence.
   - This layer should be tailored to `F₂.obj X`, not abstracted over arbitrary simplicial gadgets.

4. **Define the recursive homotopy operator following EM `(2.13)`.**
   - Base case: `phiRaw X 0 = 0`.
   - Recursive step for `q > 0`:
     `Φ_q = - Φ'_q + h'_q D₀`.
   - Prove the structural side facts EM needs:
     - `phiRaw` is frontal;
     - `phiRaw` is killed by `PInfty` on degenerate inputs (“preserves norms”);
     - the corresponding facts for `h'`.

5. **Prove the homotopy identity on `F₂` modulo norms, degreewise.**
   - Follow EM `pdfs/mcl2_sections_1_2.md:169`–`194`.
   - Use the same decomposition `∂ = F₀ - ∂'`.
   - Reuse the existing `dNext` / `prevD` notation from `Bisimplicial.lean`; do not invent a new
     boundary language.
   - Target statement: after postcomposing with `retractionN₂`,
     `(dNext n phiRawHom + prevD n phiRawHom + 𝟙.f n)` agrees with
     `(alexanderWhitney X ≫ shuffleMap X).f n`.
   - This is the Lean form of EM's “`∂Φ + Φ∂ = h - i` modulo norms”.

6. **Transfer the raw EM identity to the normalized diagonal.**
   - Define the normalized homotopy components by conjugation:
     `phiNorm X n := inclusionN₂ X.f n ≫ phiRaw X n ≫ retractionN₂ X.f (n+1)`.
   - Prove `Homotopy.zero` for the packaged family as in `emHomotopyHom_zero`.
   - Derive `Homotopy.comm` for
     `normalizedAlexanderWhitney X ≫ normalizedShuffleMap X`
     from the raw modulo-`PInfty` identity plus the normalization round-trip lemmas.
   - Package this as
     `homotopyNormalizedAlexanderWhitneyShuffle (X) :
        Homotopy (normalizedAlexanderWhitney X ≫ normalizedShuffleMap X) (𝟙 (N₂.obj X))`.

7. **Scope control: what we do *not* need initially.**
   - No general quotient formalization of “norms”.
   - No direct proof from the Rubio–Morace closed formula.
   - No side conditions `Φ∇ = 0`, `fΦ = 0`, `ΦΦ = 0` unless needed later.
   - No new file/module unless the tiny local derived-operator layer becomes too noisy.

This is the smallest plan that stays faithful to EM and avoids duplicating Mathlib's existing
normalization machinery.

**Ingredient 2 — `bridge₂ : HomotopyEquiv N₂ (F₂.obj X)`** — **FREE from Mathlib:**
`AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex` at
`Y := diag X` (`.lake/.../DoldKan/HomotopyEquivalence.lean:78`).

**Ingredient 1 — `bridge₁ : HomotopyEquiv N₁ (F₁.obj X)`** — **the main new plumbing** (not in
Mathlib). Lift the levelwise Dold–Kan equivalence through the total complex using
`HomologicalComplex.mapBifunctorMapHomotopy₁/₂` (`.lake/.../Algebra/Homology/BifunctorHomotopy.lean:175,185`):
a homotopy in one direction of a double complex lifts to the total complex. Sub-tasks:
  (a) relate our `totalFunctor ∘ mapHomologicalComplex` form of `F₁`/`N₁` to the `mapBifunctor`
      framework that `mapBifunctorMapHomotopy` is phrased in (iso, or re-derive for `totalFunctor`);
  (b) apply the inner-direction normalization equivalence (lift via `…₂`) and the outer (via `…₁`);
  (c) compose to `N₁ ≃ F₁`.

**Concrete construction of `bridge₁` (replace the vague "main plumbing" by a 2-step factorization):**

Introduce the intermediate total complex

```lean
noncomputable abbrev M₁ (X : BisimplicialObject C) : ChainComplex C ℕ :=
  (HomologicalComplex₂.totalFunctor _ _ _ _).obj
    (((normalizedMooreComplex C).mapHomologicalComplex _).obj
      ((alternatingFaceMapComplex (SimplicialObject C)).obj X))
```

This is "outer unnormalized, inner normalized": first take the outer alternating-face-map complex
of `X`, then normalize each resulting simplicial object in `C`, then totalize. With `M₁`, the
`N₁ → F₁` comparison splits cleanly into:

```text
N₁(X)  --bridge₁_outer-->  M₁(X)  --bridge₁_inner-->  F₁(X)
```

- **Outer step `bridge₁_outer : HomotopyEquiv (N₁.obj X) (M₁ X)`**
  - `hom` is `totalFunctor.map (((normalizedMooreComplex C).mapHomologicalComplex _).map
    (inclusionOfMooreComplexMap X))`
  - `inv` is `totalFunctor.map (((normalizedMooreComplex C).mapHomologicalComplex _).map
    (PInftyToNormalizedMooreComplex X))`
  - `hom ≫ inv = 𝟙` is strict by functoriality from
    `(splitMonoInclusionOfMooreComplexMap X).id`
  - `inv ≫ hom ≃ 𝟙` is the outer Dold–Kan homotopy
    `PInftyToNormalizedMooreComplex X ≫ inclusionOfMooreComplexMap X ≃ 𝟙`
    from `.lake/.../DoldKan/HomotopyEquivalence.lean:78`, pushed through
    `((normalizedMooreComplex C).mapHomologicalComplex _)` and then `totalFunctor`
    (this is the `…₁` lift)

- **Inner step `bridge₁_inner : HomotopyEquiv (M₁ X) (F₁.obj X)`**
  - let `Y := (alternatingFaceMapComplex (SimplicialObject C)).obj X`
  - `hom` is `totalFunctor.map ((NatTrans.mapHomologicalComplex mooreInclusion _).app Y)`
  - `inv` is `totalFunctor.map ((NatTrans.mapHomologicalComplex mooreRetraction _).app Y)`
  - `hom ≫ inv = 𝟙` is strict by functoriality from
    `mooreInclusion ≫ mooreRetraction = 𝟙`
  - `inv ≫ hom ≃ 𝟙` is the pointwise inner Dold–Kan homotopy
    `mooreRetraction.app _ ≫ mooreInclusion.app _ ≃ 𝟙`, lifted degreewise through the outer chain
    complex and then totalized (this is the `…₂` lift)

- **Assemble**
  - `bridge₁ := bridge₁_outer.trans bridge₁_inner`
  - check that `bridge₁.hom` simplifies to the already-defined `inclusionN₁ X`
  - check that `bridge₁.inv` simplifies to the already-defined `retractionN₁ X`

So the real missing work is **not** defining new chain maps: those are already present as
`inclusionN₁` / `retractionN₁`. The missing work is packaging the two Dold–Kan homotopies
(`PInfty ≃ 𝟙` in the outer direction and pointwise `PInfty ≃ 𝟙` in the inner direction) and
showing `totalFunctor` carries them to homotopies of the total complexes.

### Caveats / open decisions

- **General bisimplicial vs. external product.** EM/Franz state everything for `X × Y` (two
  simplicial sets); our `F₁`/`F₂` are for one **arbitrary** bisimplicial object `X`. EM is the
  special case `X_{p,q} = K_p × L_q`. The shuffle/AW *formulas* generalize (they touch the two
  directions independently); the contraction *proof* must be the general-bisimplicial one
  (or acyclic models — existence-only, fine for a `HomotopyEquiv`, but no Mathlib acyclic-models).
- **Typeclass bump:** the normalized side requires **`[Abelian C]`** (for `normalizedMooreComplex`
  and the Mathlib bridge). This is isolated in `BisimplicialNormalized.lean`; `Bisimplicial.lean`
  stays general `[Preadditive C] [HasFiniteCoproducts C]`.
- **Naturality:** target the *cleaner* form (natural `hom`/`inv`, or a natural iso in
  `HomotopyCategory`); each of the three pieces is natural, and `.trans`/`.symm` preserve it.
  Exact naturality data deferred until the pieces exist.
- **`normalizedMooreComplex` additivity** is currently a `sorry`'d instance (Mathlib has none;
  `cat_disch` can't push `map_add` through the subobject factorization). Fill or find a lemma.

### File layout (three files)

- **`Bisimplicial.lean`** — unnormalized constructions only; general
  `[Preadditive C] [HasFiniteCoproducts C]`. Contains `F₁`, `F₂`, `shuffleMap`,
  `alexanderWhitney`, the (historical/Route B) `emHomotopy` apparatus, and the target
  `eilenbergZilber : HomotopyEquiv (F₁.obj X) (F₂.obj X)`.
- **`BisimplicialNormalizedDefs.lean`** (new, **defs layer**) — everything requiring `[Abelian C]`
  that is a *definition*: the `Abelian (SimplicialObject C)` and `normalizedMooreComplex.Additive`
  instances, `N₁`/`N₂`, and the normalized maps `normalizedShuffleMap`/`normalizedAlexanderWhitney`.
  Imports `Bisimplicial`.
- **`BisimplicialNormalized.lean`** (**proofs layer**) — imports `…Defs`; holds the contraction
  lemmas (`normalizedShuffle_alexanderWhitney`, `homotopyNormalizedAlexanderWhitneyShuffle`) and the
  assembled `eilenbergZilberNormalized`. The `bridge₁`/`bridge₂`/transport assembly into the
  unnormalized `eilenbergZilber` will live here too (or in a further file).

### Map strategy: option 3 (`PInfty`)

The normalized maps are **not** written as explicit combinatorial formulas on the Moore subobjects
(awkward — subobjects, not levelwise), nor proved by an explicit unnormalized contraction (no
literature support). Instead they **transport the unnormalized `shuffleMap`/`alexanderWhitney`
through Dold–Kan normalization** (Moore inclusion/retraction, i.e. the idempotent `PInfty` on the
alternating-face-map complex). This keeps maps levelwise-concrete *and* makes degenerate cross-terms
vanish in the contraction proofs (`PInfty` kills degeneracies) — exactly the "modulo norms = 0" step
in EM Thm 2.1a. So the unnormalized `shuffleMap`/`AW` are reused as stepping stones; only the
unnormalized *homotopy* (Route B) is dropped.

### Current drafted scaffold (both files compile; all `sorry`'d)

`BisimplicialNormalizedDefs.lean` (defs layer):
```lean
noncomputable instance : Abelian (SimplicialObject C) := …                 -- ✅ (functorCategoryAbelian)
instance : (normalizedMooreComplex C).Additive where map_add := by sorry   -- ❌ sorry (additivity)

abbrev N₁ : BisimplicialObject C ⥤ ChainComplex C ℕ := …                   -- ✅ bi-normalized total
abbrev N₂ : BisimplicialObject C ⥤ ChainComplex C ℕ := diag ⋙ normalizedMooreComplex C  -- ✅

-- Dold–Kan inclusion/retraction chain maps (the chain-map halves of bridge₁/bridge₂):
def mooreInclusion : normalizedMooreComplex C ⟶ alternatingFaceMapComplex C := …  -- ✅ (nat trans)
def mooreRetraction : alternatingFaceMapComplex C ⟶ normalizedMooreComplex C := … -- ✅ (PInfty nat trans)
def inclusionN₁ (X) : N₁.obj X ⟶ F₁.obj X := totalFunctor.map (incl⊗incl)   -- ✅ (both directions)
def retractionN₁ (X) : F₁.obj X ⟶ N₁.obj X := totalFunctor.map (PInfty⊗PInfty) -- ✅
def inclusionN₂ (X) : N₂.obj X ⟶ F₂.obj X := inclusionOfMooreComplexMap (diag X)  -- ✅
def retractionN₂ (X) : F₂.obj X ⟶ N₂.obj X := PInftyToNormalizedMooreComplex (diag X) -- ✅

-- option 3: conjugate the unnormalized maps (no longer `sorry`):
def normalizedShuffleMap (X) := inclusionN₁ X ≫ shuffleMap X ≫ retractionN₂ X       -- ✅ ∇
def normalizedAlexanderWhitney (X) := inclusionN₂ X ≫ alexanderWhitney X ≫ retractionN₁ X -- ✅ AW
```

`BisimplicialNormalized.lean` (proofs layer; imports `…Defs`):
```lean
lemma normalizedShuffle_alexanderWhitney (X) : ∇ ≫ AW = 𝟙 (N₁.obj X) := sorry  -- ❌ EM 2.1a (strict)
def homotopyNormalizedAlexanderWhitneyShuffle (X) :                          -- ❌ EM 2.1a (homotopy Φ)
    Homotopy (AW ≫ ∇) (𝟙 (N₂.obj X)) := sorry
def eilenbergZilberNormalized (X) : HomotopyEquiv (N₁.obj X) (N₂.obj X) where -- ✅ assembled
  hom := normalizedShuffleMap X; inv := normalizedAlexanderWhitney X
  homotopyHomInvId := Homotopy.ofEq (normalizedShuffle_alexanderWhitney X)
  homotopyInvHomId := homotopyNormalizedAlexanderWhitneyShuffle X
-- TODO: bridge₁, bridge₂, and the transport assembly into the unnormalized `eilenbergZilber`.
```

### Milestones (current approach)

1. ✅ Split into three files: `BisimplicialNormalizedDefs.lean` (`[Abelian C]` defs — instances,
   `N₁`/`N₂`, normalized maps) and `BisimplicialNormalized.lean` (proofs — contraction lemmas +
   `eilenbergZilberNormalized`, imports `…Defs`); both import-chain from `Bisimplicial`
   (DONE — all three files compile; `Bisimplicial.lean` stays general
   `[Preadditive C] [HasFiniteCoproducts C]`).
2. ✅ Define the normalized maps (option 3): `mooreInclusion`/`mooreRetraction` nat-transs, the
   four inclusion/retraction chain maps `inclusionN₁`/`retractionN₁` (via `totalFunctor.map`) and
   `inclusionN₂`/`retractionN₂` (diagonal), then `normalizedShuffleMap`/`normalizedAlexanderWhitney`
   by conjugation (DONE — sorry-free; only the additivity instance + the two contraction proofs
   remain `sorry`).
3. ✅ Discharge `normalizedMooreComplex` additivity `sorry` (DONE — pipeline is additivity-clean).
4. ✅ `bridge₂` (one-liner via Mathlib). Built **inline** inside `eilenbergZilber` as
   `homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (A := C) (Y := diag.obj X)`, whose
   endpoints are *definitionally* `N₂.obj X`/`F₂.obj X`. (DONE — axiom-clean.)
5. ⚠️ `eilenbergZilberNormalized`: assembled. `homotopyHomInvId` = `normalizedShuffle_alexanderWhitney`
   (the strict `∇ ≫ AW = 𝟙 N₁`) is **DONE, sorry-free**. `homotopyInvHomId` =
   `homotopyNormalizedAlexanderWhitneyShuffle` (`AW ≫ ∇ ≃ 𝟙 N₂`, the explicit EM `Φ` homotopy —
   the hard, sourced part) is the **only remaining `sorry`** in the whole pipeline
   (`BisimplicialNormalized.lean:746`).
6. ✅ `bridge₁` (DONE — **axiom-clean**, in its own file `BisimplicialBridge1.lean`). Defined `M₁`,
   built `bridge₁Outer : N₁ ≃ M₁` and `bridge₁Inner : M₁ ≃ F₁`, composed to
   `bridge₁ : N₁ ≃ F₁`. The inner lift required a generalized outer-lift `totalMapHomotopy`
   (abstract `TotalComplexShape c₁ c₂ c`), a `totalFlipIso`-conjugation `totalMapHomotopy₂`, a global
   `TotalComplexShapeSymmetry (down ℕ)³` instance, a reusable flip-lift
   `flipMapHomologicalComplexHomotopy`, and naturality of the Dold–Kan contraction operator
   (`homotopyInvHomId_hom_naturality`). All `sorry`-free.
7. ⚠️ `eilenbergZilber` **assembled** (`BisimplicialNormalized.lean:757`):
   `(bridge₁ X).symm.trans <| (eilenbergZilberNormalized X).trans <| bridge₂`. Compiles and gives
   `HomotopyEquiv (F₁.obj X) (F₂.obj X)`. Depends on exactly one `sorryAx`, tracing to milestone 5's
   `homotopyNormalizedAlexanderWhitneyShuffle`. **Naturality in `X` still TODO.**

### ⟹ Current status (2026-06): the *transport scaffolding is complete and axiom-clean*; the sole
remaining mathematical gap is the EM homotopy `AW ≫ ∇ ≃ 𝟙` on the normalized diagonal
(`homotopyNormalizedAlexanderWhitneyShuffle`). `bridge₁`, `bridge₂`, the strict identity, additivity,
and the final `eilenbergZilber` composite are all done.

### Proof skeleton: `normalizedShuffle_alexanderWhitney` (`∇ ≫ AW = 𝟙 N₁`, EM `f∇ = i`)

The **strict, cheap** half of EM Thm 2.1a (eq. (2.3) `f∇ = i`). Unfold the conjugated maps and
reduce via the Dold–Kan round-trip identities (all `≫` right-associated):

```
∇_N ≫ AW_N
 = inclN₁ ≫ shuffle ≫ (retN₂ ≫ inclN₂) ≫ AW ≫ retN₁     -- unfold defs + assoc
 = inclN₁ ≫ shuffle ≫ AW ≫ retN₁     -- (B): retN₂≫inclN₂ = PInfty (Mathlib), dropped — ∇ preserves norms
 = inclN₁ ≫ retN₁                     -- (A): shuffle ≫ AW ≫ retN₁ = retN₁   (EM f∇=i mod norms)
 = 𝟙 N₁                               -- (glue): split-mono id, lifted through totalFunctor
```

**Content lemmas (the only real work):**
- **(A)** `shuffleMap X ≫ alexanderWhitney X ≫ retractionN₁ X = retractionN₁ X`. EM `f∇ = i` mod
  norms (`mcl2_sections_1_2.md:128–133`): unnormalized `shuffle ≫ AW = 𝟙 + D` with `D` landing in
  the degenerate subcomplex, and `retractionN₁` (Moore retraction in both directions) kills `D`.
  Combinatorial core = the shuffle-pairing `ezComponent p q ≫ awComponent r s` (diagonal `(r,s)=(p,q)`
  → id; off-diagonal → factors through a degeneracy `σ`). This is the **reverted**
  `ezComponent_comp_awComponent_ne` lemma, now **correct** because off-diagonal terms only need to
  vanish *after* `≫ retractionN₁`, not on the nose (where they are nonzero — see the counterexample).
- **(B)** `inclusionN₁ X ≫ shuffleMap X ≫ retractionN₂ X ≫ inclusionN₂ X = inclusionN₁ X ≫ shuffleMap X`.
  Folds (G1) `retN₂ ≫ inclN₂ = PInfty` (Mathlib `PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap`)
  and ∇-preserves-normalization (EM Lemma I.5.3, `mcl2_sections_1_2.md:91`): once on the normalized
  total, `∇` lands in the normalized diagonal, so the diagonal `PInfty` round-trip is a no-op.
  Tagged `@[reassoc]` so it rewrites under the trailing `AW ≫ retN₁`.
  **Full proof approach in "Proof of (B)" below** (reduction done; combinatorial core = the same
  diagonal/non-diagonal split + `swapDiagonalSteps` involution as `ezComponent_boundary`).

**Cheap glue:** `inclusionN₁ X ≫ retractionN₁ X = 𝟙 (N₁.obj X)` — total-complex lift of the Mathlib
split-mono identity `(splitMonoInclusionOfMooreComplexMap _).id` (`Normalized.lean:102`) via
functoriality of `totalFunctor` + `NatTrans.mapHomologicalComplex`. Reused by `bridge₁`.

Build order: sorry (A)/(B)/glue, confirm the top-level rewrite chain closes, then fill (B) (PInfty
algebra), the glue (total-complex functoriality), and finally (A)'s shuffle-pairing (the real grind).

### Proof of (B): `inclusionN₁ ≫ shuffleMap ≫ PInfty = inclusionN₁ ≫ shuffleMap`

`(B)` is **∇ preserves normalization** (EM Lemma I.5.3). After (G1) folds `retN₂ ≫ inclN₂ = PInfty`
(Mathlib `PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap`), the remaining goal is
`inclusionN₁ X ≫ shuffleMap X ≫ PInfty = inclusionN₁ X ≫ shuffleMap X`. The split-mono structure of
`inclusionOfMooreComplexMap (diag X)` makes "factors through the Moore complex" *equivalent* to this
goal (circular), so the real content is a degreewise **`HigherFacesVanish`** statement.

**Reduction (mechanical, done — `BisimplicialNormalized.lean`):**
1. `ext (_|n)` + `comp_P_eq_self` (mirrors Mathlib `inclusionOfMooreComplexMap_comp_PInfty`,
   `Normalized.lean:86`) ⇒ reduce to a private lemma
   `HigherFacesVanish (X := diag.obj X) (n+1) ((inclusionN₁ X ≫ shuffleMap X).f (n+1))`.
2. `intro j hj`; `HomologicalComplex.comp_f`; `HomologicalComplex₂.total.hom_ext` ⇒ per-summand
   `(p,q)`, `p+q=n+1`. The plumbing collapses (`totalFunctor_map`, `ιTotal_map_assoc`,
   `ι_totalDesc_assoc`) to a single `ezComponent` term.
3. `simp only [SimplicialObject.δ, diag_obj_map]` (the `Bisimplicial.lean:773` pattern) splits the
   diagonal face `(diag X).δ_{j+1}` into vertical (`(X.map δᵒᵖ).app`, p-dir) and horizontal
   (`X⟦n+1⟧.map δᵒᵖ`, q-dir) pieces.
4. Expand `ezComponent` (`∑_μ sign • (sndHom ≫ fstHom)`), then **mirror `ezComponent_boundary`'s
   eqToHom dance** (`Bisimplicial.lean:774–811`): one naturality commute
   (`← (X.map δᵒᵖ).naturality`), `generalize_proofs` the index-transport `eqToHom`, split it into
   `eqToHom_vert ≫ eqToHom_horiz`, fold each half into the adjacent `X.map`/`X⟦_⟧.map` via
   `eqToHom_map`/`eqToHom_app`/`Functor.map_comp`, a second naturality commute, and fuse adjacent
   same-direction maps. **Result (current `sorry`):**
   ```
   incl ≫ ∑ μ, μ.sign •
       X⟦p⟧.map ((shuffleSndHom μ)ᵒᵖ ≫ (δ_{j+1})ᵒᵖ)              -- q-direction
         ≫ (X.map ((shuffleFstHom μ)ᵒᵖ ≫ (δ_{j+1})ᵒᵖ)).app⟦n⟧    -- p-direction   = 0
   ```
   (index-transport `eqToHom`s absorbed into the homs).

**Combinatorial core (the real work, NOT termwise zero).** Per shuffle `μ`, vertex `j+1`
(`∈ {1,…,p+q}`, never 0) is classified by `Shuffle.isDiagonalVertex μ (j+1)` (is it a *corner* —
one p-step, one q-step?):

- **Non-diagonal** (both adjacent steps the same type): the matching projection misses value
  `≥ 1`, so `shuffleFstHom μ ∘ δ_{j+1}` (both p-steps) resp. `shuffleSndHom μ ∘ δ_{j+1}` (both
  q-steps) factors through a **higher coface `δ_v`, `v ≥ 1`**. Contravariantly the corresponding
  directional `X.map` then *begins* (right after the inclusion) with a higher face `d_v`; the
  matching leg of the bi-Moore inclusion — outer `inclusionOfMooreComplexMap X` (p-dir) / inner
  `mooreInclusion` (q-dir), both landing in `⋂_{k≥1} ker d_k` — annihilates it. The factorization
  is exactly the existing `Shuffle.insertLeftStep_face` / `insertRightStep_face`
  (`Bisimplicial.lean:586–669`). The top vertex `j+1 = p+q` always lands here.
- **Diagonal / corner** (one p-step, one q-step): both `fstHom∘δ` and `sndHom∘δ` stay surjective,
  so normalization gives nothing — instead these terms **cancel in sign-reversing pairs**. The
  partner `Shuffle.swapDiagonalSteps μ (j+1)` agrees with `μ` at every vertex except `j+1`; since
  `δ_{j+1}` deletes exactly that vertex, `fstHom`/`sndHom` agree after `∘ δ_{j+1}`, but the swap
  flips the sign (`Shuffle.swapDiagonalSteps_neg_sign`), so the pair cancels.

**This is the same diagonal/non-diagonal split + involution as `ezComponent_boundary`'s Steps 6–8
(`Bisimplicial.lean:812–871`).** Reusable `Shuffle` API: `isDiagonalVertex`(`_decidable`),
`swapDiagonalSteps`(`_neg_sign`/`_vertex`/`_involutive`/`_ne`), `insertLeftStep_face`,
`insertRightStep_face`. Plan to finish:
1. Bring `incl` into the sum (`Preadditive.comp_sum`), split `∑_μ` on `isDiagonalVertex μ (j+1)`.
2. Diagonal part → cancel via the `swapDiagonalSteps` involution (mirror `Bisimplicial.lean:829–871`).
3. Non-diagonal part → factor through `δ_v` (`v ≥ 1`) via `insert…Step_face`, kill with the
   `inclusionOfMooreComplexMap`/`mooreInclusion` kernel property.

**STATUS (B): assembled, sorry-free internally.** `higherFacesVanish_inclusionN₁_shuffleMap`
compiles; it now rests on two drafted helpers — `nondiag_sndHom_or_fstHom_comp_δ_not_surjective`
(combinatorial disjunction, `:86`) and `biInclusion_comp_outer_map_op_eq_zero` (outer glue, `:132`).
The diagonal case (swap involution) and both non-diagonal sub-cases (RR inner-glue, LL outer-glue via
naturality swap + `convert … using 2`) are done.

### Proof of (A): `shuffleMap ≫ alexanderWhitney ≫ retractionN₁ = retractionN₁`

`(A)` is **EM `f∇ = i` modulo norms** — the strict half of EM Thm 2.1a, but conjugated so the
unnormalized cross-terms die under `≫ retractionN₁` rather than on the nose (the counterexample
below shows they are nonzero unnormalized). Directions: `shuffleMap : F₁ → F₂`,
`alexanderWhitney : F₂ → F₁`, `retractionN₁ : F₁ → N₁`; the goal is an equality of maps `F₁ → N₁`.

**Reduction (mechanical, mirrors `inclusionN₁_shuffleMap_diag_normalize` + `alexanderWhitney.comm'`):**
1. `ext n`; both sides are maps `(F₁.obj X).X n → (N₁.obj X).X n`. Apply
   `HomologicalComplex₂.total.hom_ext` on the **source** total complex ⇒ precompose with each
   coproduct inclusion `ιTotal_{r,s}` (`r + s = n`).
2. `ιTotal_{r,s} ≫ shuffleMap.f n = ezComponent X r s ≫ eqToHom _` (def via `totalDesc`,
   `HomologicalComplex₂.ι_totalDesc`).
3. `≫ alexanderWhitney.f n = ∑_{p : Fin (n+1)} eqToHom _ ≫ awComponent X p (n-p) ≫ ιTotal_{p,n-p}`
   (def of `alexanderWhitney`). Absorbing the index-transport `eqToHom`s gives
   `∑_p (ezComponent X r s ≫ awComponent X p (n-p)) ≫ ιTotal_{p,n-p}`.
4. `≫ retractionN₁.f n`. Since `retractionN₁ = totalFunctor.map (bi-PInfty)`, we have
   `ιTotal_{p,q} ≫ retractionN₁.f n = r_{p,q} ≫ ιTotal^{N₁}_{p,q}`, where the **bidegree-`(p,q)`
   retraction component** `r_{p,q}` is the inner Moore retraction on `X⟦p⟧` at degree `q` composed
   with the outer `PInftyToNormalizedMooreComplex X` component (extract via `totalFunctor_map` /
   `ιTotal_map`, `NatTrans.mapHomologicalComplex_app_f`, `Functor.mapHomologicalComplex` field
   accessors — the dual of the `Aₚq`/`Bₚq` unfolding used in (B)).
   The RHS `retractionN₁.f n` precomposed with `ιTotal_{r,s}` is just `r_{r,s} ≫ ιTotal^{N₁}_{r,s}`.
5. Coproduct inclusions `ιTotal^{N₁}_{p,q}` are jointly mono-independent ⇒ match summand-by-summand
   in `p`. The goal splits into:
   - **diagonal** `p = r`: `ezComponent X r s ≫ awComponent X r s ≫ r_{r,s} = r_{r,s}`;
   - **off-diagonal** `p ≠ r`: `ezComponent X r s ≫ awComponent X p (n-p) ≫ r_{p,n-p} = 0`.

**Combinatorial core (the real grind — two lemmas, DUAL to (B)).** Where (B) killed *cofaces* `δ_v`
(`v ≥ 1`) with the Moore *inclusion* (kernel-of-faces), (A) kills *degeneracies* `σ_i` with the
Moore *retraction* `PInfty` (which annihilates the degenerate/image-of-`σ` subobject):

- **(A-offdiag)** `p ≠ r`: the pairing `awComponent X p (n-p) ∘ ezComponent X r s` factors through a
  **degeneracy** in one of the two directions. Geometrically: AW takes the front-`p`-face
  (`ι_front`) ⊗ back-`(n-p)`-face (`ι_back`); for every `(r,s)`-shuffle `μ`, when the split point
  `p ≠ r` the chosen front/back faces of `μ` repeat a vertex, so `ι_front/ι_back ∘ shuffleFst/SndHom μ`
  is **non-injective** ⇒ factors as `σ_i ∘ (…)` (`SimplexCategory.eq_σ_comp_of_not_injective`, dual
  of the `eq_comp_δ_of_not_surjective` used in (B)). Contravariantly the directional `X.map`/
  `X⟦p⟧.map` then *ends* (just before `r_{p,q}`) with a degeneracy `s_i`; the matching leg of the
  bi-PInfty retraction kills it (`PInfty`/`PInftyToNormalizedMooreComplex` annihilates degeneracies).
  ⇒ extract a **dual glue lemma**: `Y.map g.op ≫ (PInftyToNormalizedMooreComplex Y).f q = 0` for `g`
  non-injective (image-repeats) — and its outer/bi-graded analogue — mirroring
  `inclusionOfMooreComplexMap_comp_map_op_eq_zero` / `biInclusion_comp_outer_map_op_eq_zero` but on
  the **retraction** side. (Matches the counterexample: the `(r,s)=(0,1)≠(1,0)` term `d₁x ⊗ s₀y` is
  degenerate via `s₀`.)
- **(A-diag)** `p = r`: `ezComponent X r s ≫ awComponent X r s = 𝟙_{X⟦r⟧⟦s⟧} + D_deg`, with `D_deg`
  a sum of degenerate terms. The `𝟙` comes from the **trivial shuffle** (its front-`r`/back-`s` faces
  recover the identity); every other shuffle contributes a degenerate cross-term. Then
  `(𝟙 + D_deg) ≫ r_{r,s} = r_{r,s} + (D_deg ≫ r_{r,s}) = r_{r,s} + 0 = r_{r,s}` by the same
  degeneracy-kill. So (A-diag) reduces to (i) isolating the trivial-shuffle identity summand and
  (ii) showing every non-trivial shuffle term is degenerate (same `σ_i`-factorization as A-offdiag).

**Reusable API.** `ι_front`/`ι_back` (`Bisimplicial.lean`), `shuffleFstHom`/`shuffleSndHom`,
`Shuffle` structure + `coordSum_eq`; `SimplexCategory.eq_σ_comp_of_not_injective` (dual to
`eq_comp_δ_of_not_surjective`); Mathlib DoldKan degeneracy-kill lemmas for `PInfty`
(`SimplicialObject.σ`-comp-`PInfty` / `HigherFacesVanish` dual — **TODO: locate exact name**, likely
`DoldKan`'s `PInfty_comp_map_σ`-style or via `Decomposition`/`Degeneracies.lean`). The bidegree
unfolding of `retractionN₁` reuses the (B) plumbing (`totalFunctor_map`, `ιTotal_map`,
`mapHomologicalComplex_app_f`) verbatim, dualized to the retraction natural transformations
(`mooreRetraction`, `PInftyToNormalizedMooreComplex`).

**Plan to finish (A):**
1. Mechanical reduction (Steps 1–5) — pure plumbing, mirrors (B)'s reduction + `alexanderWhitney.comm'`.
2. Prove the **dual glue lemma(s)**: degeneracy-factoring map `≫ PInfty/Moore-retraction = 0`
   (inner + bi-graded), dual to the two (B) glue lemmas already proven.
3. **(A-offdiag)**: show `ι_front/ι_back ∘ shuffleFst/SndHom μ` is non-injective when `p ≠ r`
   (combinatorial, `coordSum_eq` + Fin reasoning), feed the dual glue.
4. **(A-diag)**: isolate the trivial-shuffle `𝟙` summand (`Finset` single-out), show the rest are
   degenerate (reuse Step 3's non-injectivity), kill with the dual glue.

**Difficulty: HIGH** (the "real grind", per the original build order). Heaviest sub-piece is the
non-injectivity combinatorics (Step 3) + the trivial-shuffle isolation (Step 4i). The dual glue
lemmas (Step 2) should be near-mechanical duals of the (B) glue lemmas. Recommend doing Step 2 (dual
glue) first as standalone `sorry`'d lemmas, then the mechanical reduction (Step 1), leaving the two
combinatorial cores (Steps 3–4) — exactly the build order that worked for (B).

---

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

## ~~Route B (build the Eilenberg–Mac Lane homotopy directly on unnormalized)~~ — SUPERSEDED

> **SUPERSEDED by the CURRENT APPROACH above.** Kept for history and because some pieces
> (`emHomotopy`/`emFstHom`/`emSndHom`, the `awShuffle_f_*` plumbing) may still be reusable for the
> *normalized* `Φ`. Route B attempts the **exact** identity `∇AW = 1 + dH` on the **unnormalized**
> `F₂` — which the literature never does (see survey below), and which EM's Thm 2.1 framing
> suggests holds only modulo norms. Do **not** invest further here without first exhausting the
> normalized+transport route.

### (historical) Route B detail

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

1. **✅ DONE — Base case `n = 0`.** The proof splits `awShuffle_eq_id_add_dH` on `rcases n`.
   For `n = 0`: `prevD 0 = 0` (`prevD_emHomotopyHom_zero`, via `emHomotopy_zero`) and
   `dNext 0 = 0` (`dNext_emHomotopyHom_zero`, `dNext_eq_zero` — no differential out of degree
   0), so the goal collapses to `(∇AW).f 0 = 𝟙` (`awShuffle_f_zero`). The base case proof:
   ```lean
   rw [HomologicalComplex.comp_f]
   simp [alexanderWhitney, shuffleMap]               -- ↝ awComponent 0 0 ≫ ezComponent 0 0 = 𝟙
   simp only [awComponent, ezComponent, ι_front, ι_back, shuffleFstHom, shuffleSndHom]
   have hid : ∀ (f : (⦋0⦌ : SimplexCategory) ⟶ ⦋0⦌), f = 𝟙 _ := fun f => Subsingleton.elim _ _
   simp [hid, Shuffle.sign, Shuffle.invCount]
   ```
   Key tricks: `⦋0⦌` is terminal so `Subsingleton (⦋0⦌ ⟶ ⦋0⦌)` collapses every face/degeneracy
   to `𝟙`; the unique `Shuffle 0 0` has `sign = 1` computed directly from the empty `invCount`
   sum (dodging a `default`-instance mismatch with `sign_default_zero_right`).

### The `n + 1` case (remaining `sorry`)

**Goal, made concrete.**  `(AW ≫ ∇).f (n+1) = dNext (n+1) + prevD (n+1) + 𝟙_{n+1}` where:
- `dNext (n+1)` (`dNext_nat`): `d_{n+1,n} ≫ emHomotopyHom X n (n+1)` = `d ≫ H_n`  (`Hd` term).
- `prevD (n+1)` (`prevD_eq` at `Rel (n+2) (n+1)`): `emHomotopy X (n+1) ≫ d_{n+2,n+1}` =
  `H_{n+1} ≫ d`  (`dH` term).
- LHS (`comp_f` + `total.hom_ext`/`ι_totalDesc`, like `awShuffle_f_zero` at general degree):
  `∑_{p+q=n+1} awComponent(p,q) ≫ ezComponent(p,q)` = EM's `F = ∇AW` at degree `n+1`.

**Key structural reduction.** Every term on both sides is a `ℤ`-linear combination of
*operator words* `(X.map a.op).app _ ≫ (X.obj _).map b.op` — a pair `(a, b)` of `SimplexCategory`
maps (horizontal, vertical). Since `X` is arbitrary/abstract, the identity holds iff the two
formal `ℤ`-combinations of **pairs of monotone maps** coincide coefficient-by-coefficient (over
`Hom(⦋n+1⦌,⦋p⦌) × Hom(⦋n+1⦌,⦋q⦌)`). So `n+1` reduces to a finite combinatorial identity in the
two-variable simplicial-operator algebra — exactly EM's computation, where the `(-1)^{m+1}` sign
(Franz footnote 2) makes it balance.

2. **Concretize both sides.** ✅ **partially done.**
   - LHS done: `awShuffle_f_eq_sum` proves
     `(AW ≫ ∇).f m = ∑ p:Fin(m+1), eqToHom ≫ awComponent p (m-p) ≫ ezComponent p (m-p) ≫ eqToHom`.
     Proof is short: `rw [HomologicalComplex.comp_f]; simp only [alexanderWhitney, shuffleMap,
     id_eq, Preadditive.sum_comp, Category.assoc, HomologicalComplex₂.ι_totalDesc]` (the `id_eq`
     strips the structure-projection wrapper so the sum distributes and `ι_totalDesc` collapses
     each `ιTotal ≫ totalDesc` to its component).
   - `n+1` goal now reads (after `rw [awShuffle_f_eq_sum, dNext_nat, prevD_eq …]`):
     `∑ p, … awComponent p (n+1-p) ≫ ezComponent p (n+1-p) … = d_{n+1,n} ≫ H_n + H_{n+1} ≫ d_{n+2,n+1} + 𝟙`.
   - Still TODO: expand the two differentials `d` on `F₂ = alternatingFaceMapComplex(diag X)` into
     alternating sums of diagonal faces `(diag X).δ k = (X.map δₖ.op).app ≫ (X.obj _).map δₖ.op`,
     and expand `emHomotopy` in components, so the RHS operator words become explicit.

3. **Operator-composition sub-lemmas (the reusable combinatorial core).** How `emFstHom` /
   `emSndHom` compose with a **boundary face `δ_k`** (and with `SimplexCategory.σ`), i.e. how
   `H`'s operator word recombines when the differential's faces are appended. Mirror the
   `*_comp_δ` lemmas already proven for `shuffleFstHom` / `ι_front`, in the
   `ext ⟨i,hi⟩; dsimp; split_ifs; omega` style. Also `awComponent ≫ ezComponent` rewritten in
   the same shuffle-indexed normal form. Outcome: `F_{n+1}`, `H_n d`, `d H_{n+1}` all land in a
   common normal form. **Self-contained and reusable — do these first as `sorry`'d statements.**

4. **Combinatorial cancellation.** Reindex the sums (over shuffles × face index), pair terms, and
   cancel everything except the identity term (à la `universalSimplexCrossProduct_boundary`).
   This is the EM/Rubio argument and the bulk of the work; the `m+1` sign exponent is essential.

**Honest assessment / fallback.** Step 4 is the crux of the whole theorem, and Franz/EM only
obtain it via the recursion (3.4), not the explicit formula. Treat Milestone 3 as a *probe*: it
is needed regardless and reveals how bad the bookkeeping is. If step 4 balloons, switch to
Route A or AMT (see literature survey below).

### Literature survey: is Route B (direct, unnormalized) sourced anywhere?

**Finding: no.** A direct combinatorial verification of `∇AW = 1 + dH` from the closed-form (3.3)
on *unnormalized* chains does not appear in the literature. Every treatment routes around that
cancellation in one of four ways:

1. **Acyclic models** (existence only, no explicit `H`): May *Simplicial Objects* Cor. 29.10;
   Dold VI.12; JHU note `math.jhu.edu/~jmb/note/eilzil.pdf`; nLab *EZAW deformation retraction*.
2. **Recursive `H` + induction with derived operators** (the EM original): Eilenberg–Mac Lane
   1954, Thm 2.1a — what Franz cites. = our Route A.
3. **Explicit formula reduced to the recursion:** Sergeraert, *EZ via discrete vector fields*
   (`www-fourier.univ-grenoble-alpes.fr/~sergerar/Papers/EZ-submitted.pdf`) writes the
   Rubio–Morace closed form and *proves it satisfies EM's recursion* (its point 5), i.e.
   explicit ⇒ recursive ⇒ EM. Even the explicit-formula authors bounce back to (2).
4. **Algebraic Morse theory / discrete vector fields:** builds the whole contraction `(f,g,h)`
   from a matching; the identities `fg=1`, `1−gf=dh+hd`, `hh=0` follow from general AMT lemmas,
   *not* from manipulating the shuffle sum (Sergeraert; Sköldberg; Kozlov).

### Literature survey: what is actually sourced for `homotopyInvHomId` on normalized chains?

**Finding: the sourced proof is recursive.** For the normalized identity
`AW ≫ ∇ ≃ 𝟙` / `∂Φ + Φ∂ = ∇f - i`, the literature we checked supports:

1. **Eilenberg–Mac Lane** (`pdfs/mcl2_sections_1_2.md:163`–`194`): define `Φ` recursively by
   `(2.13)`, prove it preserves norms, and prove the homotopy identity by induction using derived
   operators. This is the primary source.
2. **Franz** (`pdfs/Franz_EilenbergZilberMap.pdf`): gives the explicit Rubio–Morace formula and
   restates the contraction identities, but explicitly cites EM for those identities rather than
   reproving them.
3. **Sergeraert** (`EZ-submitted.pdf`, §12, especially the roadmap point 5): proves the
   Rubio–Morace closed formula satisfies the recursive Eilenberg–Mac Lane definition. This gives
   a sourced bridge `explicit formula ⇒ recursion ⇒ EM identity`, but still routes through the
   recursive argument.

**Practical consequence for Lean.** If we want `homotopyInvHomId` to follow a literature proof,
the safe route is to set up enough recursive/derived-operator machinery to run EM (or enough to
show the explicit formula satisfies EM recursion, which in practice still requires the recursive
layer). A direct closed-form verification appears to be unsourced.

The explicit-`H` shuffle-form sources all work **normalized** and drop degenerate summands, citing
EM for the contraction identities rather than reproving `dH+Hd`:
- González-Díaz & Real, `arXiv:math/0110308` (also `maths.ed.ac.uk/~v1ranick/papers/real1.pdf`):
  notable reusable idea — put every face/degeneracy composite in the **canonical form**
  `s_{jₜ}…s_{j₁} ∂_{i₁}…∂_{iₛ}`, then kill leading-degeneracy summands. That canonical-form
  normalization is exactly the bookkeeping Route B needs.
- James-map paper (Hess–Parent–Scott–Tonks, HHA 9(2)): reproduces EM's *recursive* `ϕ`.
- MathOverflow #323966 → Muro points to GD–Real p. 7 (normalized).

**Why nobody does it directly:** on unnormalized chains the cancellation does *not* fully
collapse — the surviving degenerate terms are precisely what `dH+Hd` accounts for, which is why
the `(-1)^{m+1}` sign is delicate (Franz fn. 2). So Route B is genuinely un-precedented; we would
be doing a computation the literature deliberately avoids.

**Revised recommendation.** Prefer a *precedented* route:
- **Route A (recursion ⇒ induction, à la Sergeraert pt. 5).** Formalize a derived operator
  `f ↦ f'` + its laws (Franz (2.4), Lemma 2.1), prove our explicit (3.3) satisfies (3.4), then
  the short induction `dH + Hd = F − 1` using `dF = Fd` (free). Sergeraert gives the explicit ⇒
  recursive argument to follow.
- **AMT reconstruction.** Replace `emHomotopy` by the homotopy coming from an Eilenberg–Zilber
  discrete vector field; get all of (3.6) from general algebraic-Morse-theory lemmas. Cleanest in
  principle but means abandoning the current explicit `emHomotopy` and building an AMT layer.

Route B remains viable as a *probe* (Milestone 3 lemmas are reusable regardless), but if it
stalls, Route A is the documented fallback.

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

## (historical) Route B scaffold state — unnormalized, SUPERSEDED

> For the live scaffold see **"Current drafted scaffold"** under the CURRENT APPROACH section
> above. The block below is the unnormalized Route B attempt, retained for reuse of the explicit
> `emHomotopy` pieces in the normalized `Φ`.

```lean
-- Phase 1 — operators DONE, identity is the remaining sorry
def emFstHom (n p q) (μ : Shuffle (p+1) q) : ⦋n+1⦌ ⟶ ⦋n⦌ := …    -- ✅ s_{β+m} s_{m-1} ∂ⁿ_{n-q+1}
def emSndHom (n p q) (μ : Shuffle (p+1) q) : ⦋n+1⦌ ⟶ ⦋n⦌ := …    -- ✅ s_{α+m} ∂^{n-q-1}_m
def emHomotopy (X) (n) : (F₂.obj X).X n ⟶ (F₂.obj X).X (n+1) := … -- ✅ formula (3.3)
lemma emHomotopy_zero (X) : emHomotopy X 0 = 0 := …               -- ✅ H₀ = 0
def emHomotopyHom (X) (i j) : (F₂.obj X).X i ⟶ (F₂.obj X).X j := … -- ✅ Homotopy.hom family
lemma emHomotopyHom_zero (X) … : emHomotopyHom X i j = 0 := …     -- ✅ Homotopy.zero

-- base-case + LHS-concretization plumbing
lemma awShuffle_f_zero (X) : (AW ≫ ∇).f 0 = (𝟙 …).f 0 := …       -- ✅ n=0 base case
lemma dNext_emHomotopyHom_zero (X) : dNext 0 (emHomotopyHom X) = 0 := …  -- ✅
lemma prevD_emHomotopyHom_zero (X) : prevD 0 (emHomotopyHom X) = 0 := …  -- ✅
lemma awShuffle_f_eq_sum (X) (m) :                               -- ✅ LHS = ∑ awComp ≫ ezComp
    (AW ≫ ∇).f m = ∑ p:Fin(m+1), eqToHom ≫ awComponent p (m-p) ≫ ezComponent p (m-p) ≫ eqToHom := …

lemma awShuffle_eq_id_add_dH (X) (n) :                            -- ⚠️ n=0 ✅, n+1 ❌ sorry (main work)
    (alexanderWhitney X ≫ shuffleMap X).f n
      = dNext n (emHomotopyHom X) + prevD n (emHomotopyHom X) + (𝟙 (F₂.obj X)).f n :=
  -- rcases n: base case closed via awShuffle_f_zero; n+1 reduced via awShuffle_f_eq_sum/dNext_nat/prevD_eq then sorry

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

## Difficulty estimate (CURRENT APPROACH)

| Item | Difficulty | Notes |
|------|-----------|-------|
| Switch to `[Abelian C]` + `Abelian (SimplicialObject C)` + `N₁`/`N₂` skeleton | Easy | ✅ done — compiles |
| `normalizedMooreComplex` additivity instance | Easy–Medium | `sorry` now; subobject-factorization `map_add` |
| `bridge₂` (normalized ≃ unnormalized diagonal) | Easy | one-liner via Mathlib |
| `eilenbergZilberNormalized`: `∇ ≫ AW = 𝟙` strict | Medium | shuffle-pairing, valid on normalized |
| `eilenbergZilberNormalized`: `AW ≫ ∇ ≃ 𝟙` via `Φ` | **Hard** | EM 2.1a; explicit homotopy on general bisimplicial obj |
| `bridge₁` (total-complex Dold–Kan) | **Hard** | new plumbing; `mapBifunctorMapHomotopy₁/₂` is the tool |
| Transport assembly `eilenbergZilber` | Easy | `bridge₁.symm.trans (… .trans bridge₂)` |
| Naturality of the equivalence | Medium | layer on after pieces exist |

## Supporting lemmas / API (CURRENT APPROACH)

- `AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex`
  (`.lake/.../DoldKan/HomotopyEquivalence.lean:78`) — gives `bridge₂` directly.
- `HomologicalComplex.mapBifunctorMapHomotopy₁` / `…₂`
  (`.lake/.../Algebra/Homology/BifunctorHomotopy.lean:175,185`) — lift a homotopy in one
  direction of a double complex to the total complex; the core of `bridge₁`.
- `HomotopyEquiv.trans` / `.symm` (`.lake/.../Algebra/Homology/Homotopy.lean:702,710`) — compose.
- `Homotopy.ofEq` — wrap the strict `∇ ≫ AW = 𝟙` direction.
- `CategoryTheory.Abelian.functorCategoryAbelian` — `Abelian (SimplicialObject C)`.

## Files involved

- `HomologyLean/SingularHomology/Bisimplicial.lean` — **unnormalized only**, general
  `[Preadditive C] [HasFiniteCoproducts C]`: `F₁`/`F₂`, `shuffleMap`/`alexanderWhitney`, the
  target `eilenbergZilber`, and the (historical) `emHomotopy` apparatus.
- `HomologyLean/SingularHomology/BisimplicialNormalized.lean` — **normalized**, `[Abelian C]`:
  `N₁`/`N₂`, normalized maps + homotopies, `eilenbergZilberNormalized`, and (to add) `bridge₁`,
  `bridge₂`, the transport assembly. Imports `Bisimplicial` + `CategoryTheory.Abelian.FunctorCategory`
  + `AlgebraicTopology.MooreComplex` (and later the DoldKan/Bifunctor homotopy files).
- `HomologyLean/SingularHomology/Shuffle.lean` — shuffle/sign lemmas (reused for the normalized `Φ`).
- Mathlib `AlgebraicTopology.DoldKan.*`, `Algebra.Homology.BifunctorHomotopy`,
  `CategoryTheory.Abelian.FunctorCategory`.
- `pdfs/mcl2_sections_1_2.md` — EM Ch. 1–2 transcription (**use this, not `mcl2.pdf`**).
