# Plan: Cubical Sites as Generalized Reedy / Eilenberg–Zilber Categories

## Goal

Formalize the cubical sites of Grandis–Mauri, *Cubical sets and their site* (TAC 11, 2003):
the restricted site `I` (faces + degeneracies), the intermediate site `J` (+ connections),
and the extended site `K` (+ interchange). Following Campion (*Cubical sites as EZ
categories*, arXiv:2303.06206, Thm 7.9) and Doherty (AGT 26:2, Prop 2.6), these cube
categories without diagonals are **generalized Reedy categories with degree = dimension**;
the restricted site `I` (no sym/reversals) is in fact a *strict* Eilenberg–Zilber category.

Concretely: the site has objects = dimensions `ℕ`, morphisms = monotone (order-preserving)
maps between elementary cubes `2ⁿ = Fin 2 → Fin n`. We instantiate our
`GeneralizedReedyCategory` (and, for `I`, optionally `EilenbergZilberCategory`) on the
object set `ℕ`, so that cubical presheaves `(site)ᵒᵖ ⥤ Type` inherit the decomposition
machinery already in `EilenbergZilbergCategory.lean` (skeleta, unique decomposition).

## Why GR, not EZ, by default

The elementary cube `2ⁿ` = product of `n` copies of `{0 < 1}` has the coordinate
permutations `Sₙ` as **nontrivial order-automorphisms**. The interchange map `σ : 2² → 2²`
(swap `(x,y) ↦ (y,x)`) generates these. Hence:

- For sites **with** connections/interchange (`J`, `K`), `isIso_eqToHom` (our EZ axiom: every
  iso is `eqToHom`, no nontrivial autos) **fails**. These are **generalized Reedy** (BM,
  autos allowed) — this is exactly the resolution the user flagged.
- For the **restricted site** `I` (faces+degs only), the only auto is the identity, so
  `isIso_eqToHom` **holds** and `I` is a strict EZ category.

So the plan: default to `GeneralizedReedyCategory` for all three sites (uniform), with the
`I`-only EZ instance as a follow-up corollary that recovers the strong decomposition theorems.

## Key Design Decision: objects = dimensions, not the function types

Mathlib's natural "2ⁿ" object type is `Fin 2 → Fin n` (the actual cube as the poset `{0<1}ⁿ`).
But the category we want has:

- **objects** = the dimensions `n : ℕ` (a discrete set of sizes),
- **morphisms** `n ⟶ m` = monotone maps `(Fin 2 → Fin n) →o (Fin 2 → Fin m)`,

rather than a `Preord`-full subcategory on the actual `2ⁿ` types. Reasons (from our earlier
discussion):

1. **`isIso_eqToHom` (EZ) needs objects whose isos force equality.** In the function-type
   model, an iso `X ⟶ Y` is an order-bijection of *types* — isomorphic types need not be equal
   (e.g. `Fin 2 → Fin 3` vs `Fin 8`), so EZ fails. With objects = `ℕ`, an iso `m ≅ n` is an
   order-iso `Cube m ≃o Cube n`, forcing `m = n` by cardinality; then the iso is `eqToHom`.
2. **`degree` becomes `id : ℕ → ℕ`**, so all degree inequalities reduce to `n < m` — trivial.
3. **No dimension-indexed transport** (`eqToHom`) anywhere, since objects are plain `ℕ`.

We define a custom category on `ℕ` with `Hom n m := Cube m →o Cube n` (note the contravariance:
`Hom n m` is maps `m → n` if we orient faces `m -> n` correctly; we fix orientation during
draft — see Open Questions).

## Architecture Overview

```
                                      category on ℕ
objects : ℕ   (dimension n ↦ cube 2ⁿ)
homs    : n ⟶ m  =  monotone maps  Cube n →o Cube m    (2ⁿ →o 2ᵐ)
  faces      F : n → n+1   (coord-inserting order-embeddings, mono)   ── R⁺
  degeneracy D : n+1 → n   (coord-dropping projections,  split-epi)   ── R⁻
  (J) connections Γ : n+1 → n   (coordinate-wise max/min merges)
  (K) interchange  σ : n → n    (coordinate permutation / transpose)

instance : GeneralizedReedyCategory CubeSite ℕ        (all three sites)
instance : EilenbergZilberCategory CubeSite           (restricted site I only, follow-up)
```

## Abbreviations and Notation

- `Dim := ℕ` (already in `CubicalSite.lean`)
- `Cube n := Fin 2 → Fin n` with pointwise `≤` (product of `{0<1}`)
- `δᵢᵉ : Cube n →i Cube (n+1)` — insert coordinate `i` with value `ε` (the two `Fin 2` endpoints),
  via `Fin.insertNth`/`succAbove`-style *incremented embedding*
- `εᵢ : Cube (n+1) →i Cube n` — drop coordinate `i` (the `Fin.succAbove`/projection `erase`),
  a surjective order-hom / split-epi
- (J) `γᵢᵉ : Cube (n+1) →o Cube n` — coordinate-wise `max` (ε=1) or `min` (ε=0)
- (K) `σ : Cube 2 →≃o Cube 2` — swap `(x,y) ↦ (y,x)`; there is one per pair of coordinates

## What Already Exists (ours)

- `WideSubcategory A` (wide subcat via `MorphismProperty`)
- `GeneralizedReedyCategory R ι` with `ι : outParam` — **class we will instantiate**
- `EilenbergZilberCategory A extends GeneralizedReedyCategory A ℕ` — `isIso_eqToHom` + sections
- `EilenbergZilberCategory.Presheaf.*`: `Decomposition`, `IsDegenerate`, `IsNondegenerate`,
  `MinusDecomposition`, `existsUnique_minusDecomposition`, `IsInSkeleton`, `skeleton`,
  `skeletonι`, `skeletonFunctor` — all parametric over `[EilenbergZilberCategory A]`, ready to
  use on cubical presheaves once `I` is an EZ instance.

## Detailed Steps

### Phase 0: The cube comparsset and maps (restricted site content)
File: `CubicalSite.lean` (scaffold already there)

1. `Cube (n : Dim) := Fin 2 → Fin n`; `Preorder` (pointwise). Instance `LinearOrder (Cube n)` exists
   (finite product of `Fin`); provide if needed.
2. **Faces** `δ (i : Fin (n+1)) (ε : Fin 2) : Cube n ↪o Cube (n+1)`:
   insert at position `i` a constant `ε` coordinate; on output coordinate `j`,
   `j = i ↦ ε`, else offset by `i`'s predecessor. (These are the two `2ⁿ →i 2^(n+1)` one-face maps.)
3. **Degeneracies** `ε₀ (i : Fin (n+1)) : Cube (n+1) →o Cube n`:
   drop coordinate `i` (`Fin.succAbove`-inverse / `Fin.erase`). Surjective. Split-epi with section =
   the corresponding face.
4. `simp` lemmas: `δ` is monotone; `ε` is surjective; `ε ∘ δ`-type identities (face after
   degeneracy).

### Phase 1: The `CubeSite` category and subcategories
File: `CubicalSite.lean`

1. `structure CubeSite where dim : ℕ` — *or* just use `ℕ` directly with a bundled `Category`.
   Decide: `abbrev CubeObj := ℕ` with `instance : Category CubeObj := {..custom}` where
   `Hom m n := Cube n →o Cube m`. (Orientation: see Open Questions.) Provide `id_comp/comp_id/assoc`
   via `OrderHom` composition.
   - Note: we may instead define a bespoke `Category` on `ℕ` whose `Hom` is `Cube n →o Cube m`.
2. `plus` : the wide subcategory whose maps are **order-embeddings** (= `Cube n ↪o Cube m`,
   monos). `minus` : maps that are **surjective** (= split-epis on finite sets).
3. Verify these are `WideSubcategory`s (`id_mem`, `comp_mem`).
4. Provisional `instance : GeneralizedReedyCategory CubeSite ℕ` (sorry'd) — see Phase 2 for the
   difficult axioms.

### Phase 1b. The cocubical relations (the deferred index work) — RESOLVED from literature

The **full generator relation table** (1-based indices), matching Krishnan–Rudman [13, Lemma 4.1]
via Kapulkin–Mavinkurve (arXiv:2408.05289, §1) and Grandis–Mauri eq. (5)/(16)/(28)–(30):

**Faces & degeneracies** (restricted site `I`):
- `∂ⱼ,ε' ∂ᵢ,ε = ∂ᵢ₊₁,ε ∂ⱼ,ε'` for `j ≤ i`   — face/face commutation (the one I errored on)
- `σⱼ ∂ᵢ,ε = { ∂ᵢ₋₁,ε σⱼ (j<i) ; id (j=i) ; ∂ᵢ,ε σⱼ₋₁ (j>i) }`   — face/degeneracy interchange
- `σᵢ σⱼ = σⱼ σᵢ₊₁` for `j ≤ i`   — degeneracy/degeneracy commutation

**Connections** (site `J`, `γᵢ,ε` = coord-wise max/min):
- `γⱼ,ε' γᵢ,ε = { γᵢ,ε γⱼ₊₁,ε' (j>i) ; γᵢ,ε γᵢ₊₁,ε (j=i, ε'=ε) }`
- `γⱼ,ε' ∂ᵢ,ε = { ∂ᵢ₋₁,ε γⱼ,ε' (j<i−1) ; id (j=i−1,i, ε=ε') ; ∂ᵢ,ε σᵢ (j=i−1,i, ε=1−ε') ; ∂ᵢ,ε γⱼ₋₁,ε' (j>i) }`
- `σⱼ γᵢ,ε = { γᵢ₋₁,ε σⱼ (j<i) ; σᵢ σᵢ (j=i) ; γᵢ,ε σⱼ₊₁ (j>i) }`

**Interchanges** (site `K`, `σᵢ` = transpose of coords `i,i+1`): Moore relations (28) +
mixed (29),(30): `σᵢσᵢ=1`, `σᵢσⱼσᵢ=σⱼσᵢσⱼ` (adjacent, Yang–Baxter), `σᵢσⱼ=σⱼσᵢ` (|i−j|>1),
`εⱼσᵢ`, `σᵢ∂...`, `σᵢγ...`.

**Canonical factorization** (Doherty Lemma 2.12, Grandis–Mauri eq. (6)): every map `φ = ∂·γ`
with `γ` "active" and `∂` a face-composite, uniquely — this is our GR `factorization`.

These 1-based identities are the ground truth to transcribe into `CubicalSite.lean` (converting to
0-based `Fin` / `succAbove` conventions), superseding the guessed `Fin` formulas that failed.

## Root-cause diagnosis: why the `Fin` transcriptions kept failing

The cube maps here are the **same combinatorial gadget as `SimplexCategory`** in Mathlib:

- `Cube n = Fin n → Fin 2`
- `face n i ε = Fin.insertNth i ε` (fill coordinate `i` with `ε`)
- `degeneracy n i = precomposition with Fin.succAbove i` (delete coordinate `i`)

Mathlib's `SimplexCategory` (`AlgebraicTopology/SimplexCategory/Basic.lean`) defines
`δ i = Fin.succAboveOrderEmb i`, `σ i = i.predAboveOrderHom` and **already proves** the full
simplicial identity family with correct `Fin` index arithmetic:

| `SimplexCategory` (to mirror) | our cubical analogue |
|---|---|
| `δ_comp_δ {i j : Fin (n+2)} (H : i ≤ j) : δ i ≫ δ j.succ = δ j ≫ δ i.castSucc` | face/face |
| `δ_comp_σ_of_le`, `δ_comp_σ_self`, `δ_comp_σ_succ`, `δ_comp_σ_of_gt` | face/degen interchange |
| `σ_comp_σ {i j : Fin (n+1)} (H : i ≤ j)` | degen/degen |

Their proofs are uniformly `ext k; rcases i/j/k; split_ifs <;> simp <;> lia` — mechanical, not
clever. The cubical relations are the **same statements ε-decorated** (faces carry an extra
`ε : Fin 2` label; `J` adds `γ`, `K` adds `σ`).

**What went wrong in previous attempts (and the fix):**
1. I transcribed subscript-soup **1-based identities with a right-action convention** from papers,
   and hand-converted to 0-based `Fin` with `succAbove`/`predAbove`/`castSucc` by eye. Each
   conversion had an off-by-one that `native_decide` then exposed.
2. The actual ground truth was obtained by **asking the user to read the PDF's eq. (5)** and
   confirm the sub/superscripts directly (the superscript layer garbled the PDF extractor).
   Confirmed (1-based, `α,β ∈ {0,1}`, composition right-to-left = `ε_i` applied first):
   - (5a) `δⱼ^β δᵢ^α = δᵢ₊₁^α δⱼ^β` for `j ≤ i`
   - (5b) `εᵢ εⱼ = εⱼ εᵢ₊₁` for `j ≤ i`
   - (5c) `εⱼ δᵢ^α = { δᵢ₋₁^α εⱼ (j<i) ; 1 (j=i) ; δᵢ^α εⱼ₋₁ (j>i) }`
3. Each was then **`native_decide`-verified on concrete small `n`** before being written to the
   file. **Lesson: don't guess `Fin` bookkeeping; verify each concrete instance by `native_decide`
   (scratch `lean_run_code`) before committing the general statement.**

### Status of the cocubical relations (RESOLVED — Phase 1b DONE, proofs DONE)

In `CubicalSite.lean`, all five restricted-site (`I`) relations are **stated and proved**
(statements were verified by `native_decide`; proofs are the ε-decorated analogues of
`SimplexCategory.δ_comp_δ`/`σ_comp_σ`):

- `face_degeneracy` (proved): `(degeneracy n i) ∘ (face n i ε) = id`  — eq. (3).
- `face_face` (proved): `face (n+1) (j.castSucc) β (face n i α x) = face (n+1) (i.succ) α (face n j β x)`, `j ≤ i`.
- `degeneracy_degeneracy` (proved): `degeneracy n a (degeneracy (n+1) b.castSucc x) = degeneracy n b (degeneracy (n+1) a.succ x)`, `b ≤ a`.
- `face_degeneracy_of_lt` (proved): `degeneracy (n+1) j (face (n+1) i α x) = face n (i.pred _) α (degeneracy n (j.castLT _) x)`, `j < i`.
- `face_degeneracy_of_gt` (proved): `degeneracy (n+1) j (face (n+1) i α x) = face n (i.castLT _) α (degeneracy n (j.pred _) x)`, `j > i`.

All four commutations reduce to one master lemma `succAbove_succAbove_comm`
(`i.succ.succAbove (j.succAbove k) = j.castSucc.succAbove (i.succAbove k)` for `j ≤ i`),
proved by mathlib's `δ_comp_δ` recipe (`Fin.ext; dsimp only [Fin.succAbove]; rcases;
split_ifs <;> simp at * <;> omega`). The `castPred`-vs-`castLT` and proof-term-`change`
gotchas are recorded in `.claude/memory/api/fin-succabove.md`. `lake build` green,
sorry-free.

### Phase 2: The Generalized-Reedy axioms (the main work)
File: `CubicalSite.lean` (or `GeneralizedReedyCube.lean`)

Per Doherty/Campion, raise = order-embeds, lower = surjectives, `degree = ∥·∥ = n` via cardinality.

- `degree_lt_of_plus`: an order-embedding `Cube m ↪o Cube n`, non-iso ⇒ `m < n` (strictly more
  coordinates). Proof: an order-embedding between the two finite products has `n > m` unless it
  hits everything; `Injectivity` + `card Cube n > card Cube m`.
  - Equivalent, cleaner: any *order-elementary* map of cubes that is injective but not a bijection
    has `m < n` (injectivity of the coordinate count). Use `card_le_card` / `Fin` cardinalities:
    `card (Fin 2 → Fin m) = 2ᵐ ≤ 2ⁿ`, so `m ≤ n`, strict when non-surjective.
- `degree_lt_of_minus`: a surjective `Cube n →o Cube m`, non-iso ⇒ `m < n`.
- `degree_eq_of_isIso`: an order-iso `Cube m ≃o Cube n` ⇒ `m = n` (cardinality `2ᵐ=2ⁿ`, or the
  iso is fundamentally a permutation of coordinates, so equal size).
- `isomorphisms_le_plus/minus`: order-iso is both an order-embedding and surjective.
- `factorization`: every monotone `f : Cube m →o Cube n` factors as surjective `Cube m ↠
  image-set` then a mono — or (cleaner) use the order-*epi/mono* factorization `f.mono` from
  `OrderHom` (`f.mono : m →o Set.range f`, `f.epi`), which *is* the canonical factorization
  (`f = f.epi ≫ f.mono`).
  - The `image` object must be a **cube of dimension `k`** for the *site* `I` (not Set.range of
    an arbitrary intermediate set). For the site `I` (and precategory), the "image" of an inj+surj
    decomposition lands in `Cube k` where `k = # of distinct surviving coordinates` — matches
    `I`'s degenerate/face decomposition. This is the subtle part for **restricted `I`**
    (surjectives can be non-projection? No — for `I`, `f = ε·δ` form: the factorization is
    `ε : m → k`, `δ : k → n`).
- `factorization_unique`: uniqueness of the `(k, ε, δ)` triangle up to unique iso, for site `I`.
  This is the hard combinatorial lemma (the paper's "unique up to iso" factorization) — sorry it
  and fill later.
- `iso_eq_id_of_comp_minus` (BM): an iso `θ : Cube n →o Cube n` with `f ≫ θ = f` for a
  surjective `f` forces `θ = 𝟙`. For `I`, an iso is a coordinate perm; `f` surjective + fixing all
  points in image forces perman sorted... Prove: `θ` fixes every element of the image of `f`;
  by surjectivity of `f`, `θ` is identity.

- **Restricted `I` / EZ instance** (follow-up): `I` has no autos ⇒ add `isIso_eqToHom`,
  `section_of_minus` (surjective ↦ split-epi on finite cubes: any surjective set-map has a
  section via `Classical.choice`), `eq_of_sections_eq`. Then cubical presheaves get the full EZ
  decomposition.

### Phase 3: Connections `J` (intermediate site)
- Add `γᵢ : Cube (n+1) →o Cube n`, coordinate-wise max (or min). Surjective, in `minus`.
- Adjoining `γ` keeps it a generalized Reedy category (Doherty Prop 2.6 lower = projections+
  connections+).
- No new basic axioms — reuses Phase 2 machinery with `minus` extended.

### Phase 4: Interchange `K` (extended site)
- Add `σ : Cube n →o Cube n`, the coordinate permutation (interchange `2²→2²`, generalized to any
  pair of coordinates).
- `K` has autos (the permutations), so stays **GR only**. `isIso_eqToHom` fails — that's expected
  and fine.

### Phase 5: Cubical EZ decomposition (payoff)
- Once `I` is an `EilenbergZilberCategory`, re-export `Presheaf.existsUnique_minusDecomposition`,
  `skeleton`, etc. for cubical presheaves. This gives the cubical Eilenberg–Zilber lemma.
- For `J`/`K` (GR), develop a GR-level "decomposition up to iso" analogue if/when needed.

## File Organization

- `HomologyLean/InfinityCategories/CubicalSite.lean` — the cube, faces/degs/conns/interchange,
  the `CubeSite` category, `plus`/`minus` subcats, and the GR (then EZ) instance.
- Possibly split when it grows: `CubicalSite.lean` (site + maps) then
  `CubicalEZ.lean` (the GR/EZ instance + decomposition).
- Keep the two-class hierarchy in `WideSubcategory.lean`/`GeneralizedReedyCategory.lean`/
  `EilenbergZilbergCategory.lean` untouched.

## Difficulty Estimate

| Phase | Difficulty | Est. lines | Notes |
|---|---|---|---|
| 0 (cube + faces/degs) | Easy | ~100 | `Fin`/`OrderHom` combinatorics; face = insert, deg = erase |
| 1 (CubeSite category + subcats) | Easy–Med | ~80 | custom `Category` on ℕ; wide-subcat closure |
| 2 (GR axioms) | Hard | ~200 | factorization + unique-up-to-iso on the restricted site is the crux |
| 3 (connections J) | Med | ~80 | reuses lower machinery |
| 4 (interchange K) | Med | ~60 | permutations; GR-only |
| 5 (cubical EZ decomposition) | Med | ~100 | re-export existing presheaf theorems on `I` |

**Total**: ~550–700 lines.

## Dependencies, Resolved and Open Questions

**Resolved**
1. Objects = dimensions (`ℕ`), not the function types — EZ `isIso_eqToHom` needs it; avoids
   transport.
2. Default class = `GeneralizedReedyCategory` (all three sites), because `J`/`K` have autos;
   `I` gets an EZ instance only as a strict corollary.
3. Follow the paper faithfully: the morphisms are the **restricted/gnerated famil**es
   (`I` = generated by faces+degs, `J` = + connections, `K` = + interchange),
   *not* all monotone maps on `2ⁿ`. So the category is built from the generators, together
   with the cocubical relations, as in the paper. The all-monotone model is a non-goal
   (its `f : Cube m →o Cube n` images neednot be cubes, and it would not satisfy the
   strict-site EZ structure).

**Open**
1. **Orientation of homs.** We want `Hom n m := Cube n →o Cube m` (maps `2ⁿ → 2ᵐ`), but with `ℕ`
   as the object set that's `Hom n m = Cube n →o Cube m` — no contravariance issue if we say
   `Hom n m` literally. Must fix signs of faces/degs w.r.t. `+1`/`-1`. Use `Hom n m := Cube n →o
   Cube m` where `n = source dim`, `m = target dim`.
2. **The restricted hom sets vs all-monotone.** Resolved for faithfulness: the sites are the
   restricted generated families. But *within* that, the concrete construction is still open:
   (a) model the site as a category whose morphisms are a `subtype` of "coordinate-wise maps"
   generated by faces/degs (closed under composition), or (b) build it as a Quotient of the free
   category on the generators subject to the cocubical relations (paper's characterization (c/e)).
   (a) is lighter and gives the EZ structure; (b) is most faithful to the paper's presentation and
   gives the "classifying category" characterization. Draft will explore (a) first since it's
   direct and compiles; keep (b) as the faithful-complete description later.
3. **The factorization's middle object.** For the *site* `I` (`Hom` = generated maps), the middle
   cube `k` = number of distinct output coordinates. For the *all-monotone* category, `f : Cube m
   →o Cube n`'s canonical factorization lands in `Set.range f ≅ Cube k` only for `I`-maps; for a
   general monotone map the image need not be a cube. So the GR instance should be on the
   **restricted hom set** for correctness (the `I`-site), not on all monotone maps. Re-examine in
   Phase 2.
4. **Which cube site exactly** do we instantiate first — `I` (fewest maps, the EZ case) or start
   with `K` for the main theorem 8.2? Recommend `I` first (practices the machinery; EZ payoff),
   but with the restricted families built faithfully so `J`/`K` extend cleanly.

## Immediate next actions (updated after eq. (5) locked in and proved)

1. **~~Fill the 4 `sorry`'d relations~~** — DONE. All restricted-site relations are proved
   via the master lemma `succAbove_succAbove_comm` (see
   `.claude/memory/api/fin-succabove.md`).
2. **Phase 1: `CubeSite` category + subcategories.** Decide the object model (Open Q1: `ℕ` with
   `Hom n m := Cube m →o Cube n` orientation) and define `plus` (order-embeds) / `minus`
   (surjective) as `WideSubcategory`s.
3. **Phase 2: the GR instance.** The heavy axiom is `factorization` (Grandis–Mauri eq. (6)) — the
   canonical `f = ε·δ` form for the site `I`. Draft sorry'd, then `/fill-sorry`.
4. Then `J` (connections γ) and `K` (interchange σ) as `minus`/`plus` extensions, and finally the
   cubical EZ decomposition (re-export `Presheaf.existsUnique_minusDecomposition` etc.).

The restricted-site cocubical relations are **fully done** (statements and proofs); commits
`c44c94e` (stale `ℕ`-indexed `face_face`) is superseded by the current `Fin`-indexed forms in
`CubicalSite.lean`.