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

## The Reedy category hierarchy

The literature has several related notions of "Reedy category". The hierarchy is:

```
Bergner–Rezk EZ ⊂ Elegant Reedy ⊂ Ordinary Reedy
                      ∪                ∪
Berger–Moerdijk EZ ⊂ Campion EZ ⊂ Generalized Reedy
```

**Key distinction**: the **left column** (Bergner–Rezk) is *strict* Reedy (no nontrivial
isomorphisms); the **right column** (Berger–Moerdijk) is *generalized* (isomorphisms
allowed). The intersection is the strict EZ case.

| Notion | Definition | Key property | Examples |
|--------|-----------|--------------|----------|
| **Ordinary Reedy** | Two wide subcats `R⁺`/`R⁻`, degree `d : Ob → α` (ordinal), non-iso `R⁺` raises degree, non-iso `R⁻` lowers, iso preserves, factorization `R⁻ ∘ R⁺` unique up to iso, `R⁺ ∩ R⁻` = isos | No nontrivial isomorphisms | `Δ`, `Θ`; our `OrdinaryReedyCategory` |
| **Generalized Reedy** (Campion) | Same as ordinary but isomorphisms allowed; drops the BM `iso_eq_id_of_comp_minus` condition | `R⁺ ∩ R⁻` = core (isos); factorization unique up to iso | Base for Campion EZ; our `GeneralizedReedyCategory` |
| **Generalized Reedy** (BM) | Campion GR + `iso_eq_id_of_comp_minus`: iso `θ` with `f ≫ θ = f` for `f ∈ R⁻` forces `θ = 𝟙` | BM condition ensures `R⁻` maps are "epi enough" | `Γ`, `Λ`, trees `Ω`, cubes with symmetries; our `BMGeneralizedReedyCategory` |
| **Elegant Reedy** | Ordinary Reedy + Reedy model structure = injective model structure | Every presheaf element is a degeneracy of a nondegenerate element uniquely | `Δ`, `Θ` |
| **Bergner–Rezk EZ** | Elegant Reedy + (EZ1) every map has a section + (EZ2) maps with same sections are equal | Strict Reedy with split epis determined by sections | `Θ` |
| **Berger–Moerdijk EZ** | BM Generalized Reedy + `A⁻` = split epis + `A⁺` = monos + absolute pushouts of `A⁻` | EZ lemma holds for presheaves | Cubes with symmetries, `Γ` |
| **Campion EZ** | Campion Generalized Reedy + absolute pushouts of `A⁻` (drops `A⁺` = monos) | Mild generalization of BM EZ; characterized by EZ lemma | Cubical sites without diagonals; our `CampionEZCategory` |

**Where the cube sites sit**:
- `I` (faces + degeneracies only): **strict EZ** (no nontrivial autos) — intersection of left and right columns
- `J` (+ connections): **Campion EZ** (generalized, has autos)
- `K` (+ interchange): **Campion EZ** (generalized, has autos)

Our `GeneralizedReedyCategory.lean` is **Campion's Generalized Reedy** (the base,
without `iso_eq_id_of_comp_minus`). Our `BMGeneralizedReedyCategory` adds the BM
condition. Our `CampionEZCategory` is **Campion's** EZ notion (extends
`GeneralizedReedyCategory` with absolute pushouts of `A⁻`). Our `EilenbergZilbergCategory.lean`
is the older Cisinski variant (extends `GeneralizedReedyCategory` with split epis determined
by sections).

**Note on terminology**: Campion's "generalized Reedy category" (Def 1.1 in arXiv:2303.06206)
omits the `iso_eq_id_of_comp_minus` condition; he reserves "Berger–Moerdijk generalized Reedy"
for the version with that condition. Our formalization has both, with Campion's as the base.

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
- The restricted site `I`, implemented concretely on `Dim := ℕ` with generated morphisms
  `CubeHom n m`, where `Cube n := Fin n → Fin 2`.
- The face/degeneracy cocubical relations and a syntactic canonical-factorization layer:
  `IsFaceComposite`, `IsDegeneracyComposite`,
  `faceComposite_degeneracyComposite_factor`, and `isGen_factorization`.
- A sorry-free `BMGeneralizedReedyCategory Dim ℕ` instance for `I`, including factorization,
  unique comparison isomorphisms, and the BM cancellation axiom.
- `EilenbergZilberCategory A extends GeneralizedReedyCategory A ℕ` — `isIso_eqToHom` + sections
- `EilenbergZilberCategory.Presheaf.*`: `Decomposition`, `IsDegenerate`, `IsNondegenerate`,
  `MinusDecomposition`, `existsUnique_minusDecomposition`, `IsInSkeleton`, `skeleton`,
  `skeletonι`, `skeletonFunctor` — all parametric over `[EilenbergZilberCategory A]`, ready to
  use on cubical presheaves once `I` is an EZ instance.

## Detailed Steps

### Phase 0: The cube poset and maps (restricted site content) — DONE
File: `CubicalSite.lean`

1. `Cube (n : Dim) := Fin n → Fin 2`, with the pointwise order.
2. **Faces** `δ (i : Fin (n+1)) (ε : Fin 2) : Cube n ↪o Cube (n+1)`:
   insert at position `i` a constant `ε` coordinate; on output coordinate `j`,
   `j = i ↦ ε`, else offset by `i`'s predecessor. (These are the two `2ⁿ →i 2^(n+1)` one-face maps.)
3. **Degeneracies** `ε₀ (i : Fin (n+1)) : Cube (n+1) →o Cube n`:
   drop coordinate `i` (`Fin.succAbove`-inverse / `Fin.erase`). Surjective. Split-epi with section =
   the corresponding face.
4. `simp` lemmas: `δ` is monotone; `ε` is surjective; `ε ∘ δ`-type identities (face after
   degeneracy).

### Phase 1: The `CubeSite` category and subcategories — DONE
File: `CubicalSite.lean`

1. Objects are dimensions `Dim := ℕ`.
2. `Hom n m := CubeHom n m`, bundling an order hom `Cube n →o Cube m` with an `IsGen`
   derivation from faces, degeneracies, identities, and composition.
3. `plus` consists of injective generated maps; `minus` consists of surjective generated maps.
4. The category laws and wide-subcategory closure properties are proved extensionally.

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

### Phase 2: The Generalized-Reedy axioms — DONE
File: `CubicalSite.lean`

The restricted site now has a sorry-free `BMGeneralizedReedyCategory Dim ℕ` instance:

- Degree inequalities and invariance under isomorphism follow from
  `Fintype.card (Cube n) = 2 ^ n`.
- Canonical factorization is proved by retaining syntactic certificates for face-only and
  degeneracy-only composites. A face composite is commuted past a degeneracy composite using
  the three cases of the face/degeneracy relation.
- Degeneracy composites have face-composite sections; face composites have
  degeneracy-composite retractions.
- A bijective generated endomorphism is an isomorphism by factoring it as `ε ≫ δ` and upgrading
  the one-sided inverses of `ε` and `δ` using injectivity/surjectivity.
- Two semantic surjective/injective factorizations are uniquely isomorphic: sections construct
  the comparison map, while surjective/injective cancellation proves its equations and uniqueness.
- The BM axiom follows directly from surjectivity of the lowering map.

- **Restricted `I` / EZ instance** (follow-up): `I` has no autos ⇒ add `isIso_eqToHom`,
  `section_of_minus` (the generated section is already available as
  `hasSection_of_surjective`), and `eq_of_sections_eq`. Then cubical presheaves get the full EZ
  decomposition.

### Deferred: Grandis–Mauri Theorem 4.2 and the tensor product

The equivalent presentations of `I` in Theorem 4.2 are not prerequisites for constructing `J`,
`K`, or their generalized Reedy structures. In particular, the current concrete `IsGen` model
does **not yet** have a formal tensor product or a `MonoidalCategory` instance.

Defer these until they are needed for the geometric product or the universal/classifying-category
results:

- define the block-sum tensor on maps over `Fin (m + n)`;
- prove that generated maps are closed under this tensor;
- construct the strict monoidal structure on `I`;
- prove Theorem 4.2(b–e), including the free strict monoidal/category-of-models descriptions.

### Phase 3: Connections `J` (intermediate site)
- **NEXT.** Define positive and negative connections
  `γᵢ : Cube (n+1) →o Cube n` by coordinate-wise min/max.
- Define the generated morphism family for `J` by adjoining connections to the generators of `I`.
- Prove the connection relations (Grandis–Mauri (16)).
- Formalize the `δ · γ · ε` canonical form of Theorem 5.1, retaining syntactic certificates as
  in Phase 2.
- Instantiate the generalized Reedy structure with raising maps generated by faces and lowering
  maps generated by degeneracies and connections.

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
4. Orientation is covariant: `Hom n m` bundles generated order homs `Cube n →o Cube m`.
5. The concrete restricted family is implemented by an inductive `IsGen` predicate, rather
   than as a quotient of a free category.
6. The restricted site `I` and its BM generalized Reedy structure are complete and sorry-free.
7. Grandis–Mauri Theorem 4.2 and monoidal closure are deferred; they are not dependencies for
   the concrete construction of `J` and `K`.

**Open**
1. Whether `J` and `K` should use separate generated-morphism structures or a common generator
   parameterization that makes the inclusions `I ⟶ J ⟶ K` explicit.
2. Whether to prove the strict `EilenbergZilberCategory` instance for `I` before starting `J`, or
   return to it after the three concrete sites exist.
3. When the geometric product becomes necessary, choose the concrete block-sum representation
   for the tensor on `Fin (m + n)` and prove closure of each generated family.

## Immediate next actions

1. Define the positive and negative connection maps and prove monotonicity and surjectivity.
2. Transcribe and prove the connection relations (16), validating the `Fin` index conventions on
   small concrete dimensions before proving the general statements.
3. Introduce the generated category `J` and its face/connection/degeneracy composite certificates.
4. Prove Grandis–Mauri Theorem 5.1's canonical form and derive the generalized Reedy instance.
5. Then add interchanges for `K`; defer tensor closure and Theorem 4.2 until required by geometric
   products or universal properties.