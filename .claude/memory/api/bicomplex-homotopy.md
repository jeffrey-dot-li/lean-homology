# Bicomplex (`HomologicalComplex₂`) flip + homotopy patterns

Patterns for `HomologicalComplex₂ C c₁ c₂ = HomologicalComplex (HomologicalComplex C c₂) c₁`,
its `flip`, and lifting homotopies through `flip`/`mapHomologicalComplex`.

## Key `@[simps]` component lemmas for `flip` / `flipFunctor`

From `Mathlib/Algebra/Homology/HomologicalBicomplex.lean` (both `flip` and `flipFunctor` are
`@[simps]`):

- `HomologicalComplex₂.flip_X_d : (K.flip.X i).d j j' = (K.d j j').f i` — differential of a *column*.
- `HomologicalComplex₂.flip_d_f : (K.flip.d i i').f j = (K.X j).d i i'` — component of a *flip
  differential* (this is the m-direction differential, evaluated in the r-direction).
- `HomologicalComplex₂.flip_X_X : (K.flip.X i).X j = (K.X j).X i`.
- `HomologicalComplex₂.flipFunctor_obj : (flipFunctor C c₁ c₂).obj K = K.flip` (rewrite to use the
  bare `flip` lemmas above).
- `HomologicalComplex₂.flipFunctor_map_f_f : ((flipFunctor C c₁ c₂).map φ).f i).f j = (φ.f j).f i`.

Plus the `mapHomologicalComplex` component lemmas:
- `Functor.mapHomologicalComplex_obj_X : (F.mapHomologicalComplex c).obj W).X i = F.obj (W.X i)`.
- `Functor.mapHomologicalComplex_obj_d : (F.mapHomologicalComplex c).obj W).d i i' = F.map (W.d i i')`.
- `NatTrans.mapHomologicalComplex_app_f : ((NatTrans.mapHomologicalComplex α c).app W).f i = α.app (W.X i)`.

## Pattern: lift a natural family of homotopies through `flip ∘ mapHomologicalComplex`

Goal shape (the reusable `flipMapHomologicalComplexHomotopy`): given additive functors
`F G : 𝒜 ⥤ ChainComplex C ℕ`, natTrans `α β : F ⟶ G`, a family `h : ∀ Y, Homotopy (α.app Y) (β.app Y)`,
and naturality
`hnat : (F.map f).f i ≫ (h Z).hom i j = (h Y).hom i j ≫ (G.map f).f j`,
build `Homotopy (flipFunctor.map ((mapHomologicalComplex α).app W)) (flipFunctor.map ((…β…).app W))`.

Build the `Homotopy` **structure directly** — each field reduces componentwise (`ext r`):

```lean
where
  hom m m' :=
    { f := fun r => (h (W.X r)).hom m m'
      comm' := fun r r' _ => by
        simp only [HomologicalComplex₂.flipFunctor_obj, HomologicalComplex₂.flip_X_d,
          Functor.mapHomologicalComplex_obj_d]
        exact (hnat (W.d r r') m m').symm }     -- chain-map-in-r condition IS hnat
  zero m m' hmm' := by ext r; exact (h (W.X r)).zero m m' hmm'
  comm m := by
    ext r
    have key := (h (W.X r)).comm m
    simp only [dNext, prevD, AddMonoidHom.mk'_apply] at key
    simp only [HomologicalComplex.add_f_apply, HomologicalComplex₂.flipFunctor_map_f_f,
      NatTrans.mapHomologicalComplex_app_f, dNext, prevD, AddMonoidHom.mk'_apply,
      HomologicalComplex.comp_f, HomologicalComplex₂.flipFunctor_obj,
      HomologicalComplex₂.flip_d_f, Functor.mapHomologicalComplex_obj_X]
    exact key
```

### Why each field works
- **`comm'`** (the operator is a chain map in the `𝒜`/`r`-direction): after rewriting the column
  differentials with `flip_X_d` + `mapHomologicalComplex_obj_d`, the goal is *literally*
  `(hnat (W.d r r') m m').symm`. So the `hnat` hypothesis is exactly the operator's chain-map condition.
- **`comm`** (the key trick): expand `dNext`/`prevD` on **both** the goal and `(h (W.X r)).comm m`
  with `[dNext, prevD, AddMonoidHom.mk'_apply]`, then push `.f r` through with `HomologicalComplex.comp_f`
  and reduce the flip differential with `flip_d_f`. **Keep `ComplexShape.next/prev` symbolic** — do NOT
  case on `m = 0`. Because both sides carry the same `next m`/`prev m`, they align and `exact key` closes
  it. (Trying `dNext_eq`/`prevD_eq`, which need a `c.Rel` witness, forces a needless `m = 0` split.)

### Defeq bonus when instantiating
`(NatTrans.mapHomologicalComplex (α ≫ β)).app W` is **definitionally** `(…α….app W) ≫ (…β….app W)`
(both are `α.app (W.X r) ≫ …` levelwise), and `(mapHomologicalComplex (𝟙 _)).app W = 𝟙`. So a stated
goal phrased with the *composite* `R ≫ I` and `𝟙` is closed by `exact` of the helper instantiated at
`α := …≫…`, `β := 𝟙` — no `Homotopy.ofEq`/transport plumbing.

## Gotcha: bare `comp_add`/`add_comp`/`assoc` not in scope
In this repo use the namespaced forms: `Preadditive.comp_add`, `Preadditive.add_comp`,
`Category.assoc` (the unqualified `comp_add`/`add_comp`/`assoc` are "unknown identifier").
