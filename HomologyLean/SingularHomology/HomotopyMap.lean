/-
  The homotopy map `X ⨯ Δ[1] ⟶ Y` and its endpoint evaluation lemmas.

  Given a topological homotopy `H : f ∼ g`, we construct a `TopCat` morphism
  `homotopyMap H : X ⨯ Δ[1] ⟶ Y` and show that composing with the two face
  inclusions `δ₀, δ₁ : Δ[0] → Δ[1]` recovers `f` and `g` respectively.
-/
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

noncomputable section

open CategoryTheory CategoryTheory.Limits unitInterval

universe u

namespace HomologyLean.SingularHomology

local notation "Δ[" p "]" => SimplexCategory.toTop.obj (SimplexCategory.mk p)

/-- The standard 1-simplex `Δ[1]` is isomorphic to the unit interval `I`. -/
noncomputable def stdSimplex1_iso_I : (Δ[1] : TopCat.{u}) ≅ TopCat.of (ULift.{u} I) := by
  refine TopCat.isoOfHomeo
    (Homeomorph.ulift.trans
      (stdSimplexHomeomorphUnitInterval.trans Homeomorph.ulift.symm))

/-- The homotopy map `Hmap : X ⨯ Δ[1] ⟶ Y` built from a topological homotopy
`H : f ∼ g` via braiding, the standard simplex–interval iso, and `H` itself. -/
noncomputable def homotopyMap {X Y : TopCat.{u}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom' g.hom') : X ⨯ Δ[1] ⟶ Y :=
  (prod.braiding X Δ[1]).hom ≫
    prod.map stdSimplex1_iso_I.hom (𝟙 X) ≫
    (TopCat.prodIsoProd _ X).hom ≫
    (show TopCat.of (ULift.{u} I × X) ⟶ Y from
      ⟨⟨fun ⟨t, x⟩ => H.toContinuousMap ⟨t.down, x⟩, by fun_prop⟩⟩)

/-- Pointwise evaluation of `prod.lift s c ≫ homotopyMap H` at `x`:
the categorical product chain (braiding, prod.map, prodIsoProd) reduces to
`H.toContinuousMap` applied to `(iso(c(x)).down, s(x))`.

This is the key computational lemma that normalizes away the `TopCat` limit
machinery so that downstream rewrites (e.g., `rw [h_t]`) have clean motives.

**Proof technique**: `TopCat` limit operations (`prod.lift`, `prod.fst`, `prod.map`, etc.)
are not definitionally transparent — `rfl` cannot see through them.  The proof alternates
between `← ConcreteCategory.comp_apply` (recombining `g(f(x))` back into `(f ≫ g)(x)`)
and categorical lemmas (`prod.lift_fst`, `prod.map_fst`, etc.) that simplify the `≫` form.
`simp` cannot drive this automatically because `← ConcreteCategory.comp_apply` is ambiguous
about which pair of applications to recombine; explicit `rw` with named arguments is needed. -/
lemma homotopyMap_eval {X Y : TopCat.{u}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom' g.hom')
    {Z : TopCat.{u}} (s : Z ⟶ X) (c : Z ⟶ Δ[1]) (x : Z) :
    (ConcreteCategory.hom (prod.lift s c ≫ homotopyMap H)) x =
    H.toContinuousMap
      (((TopCat.Hom.hom stdSimplex1_iso_I.hom) ((TopCat.Hom.hom c) x)).down,
       (TopCat.Hom.hom s) x) := by
  unfold homotopyMap
  simp only [ConcreteCategory.comp_apply]
  erw [TopCat.prodIsoProd_hom_apply]
  simp only [prod.braiding_hom]
  simp only [← ConcreteCategory.comp_apply, prod.map_fst, prod.map_snd, Category.assoc]
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply]
  rw [← ConcreteCategory.comp_apply (prod.lift prod.snd prod.fst) prod.fst]
  rw [prod.lift_fst]
  rw [← ConcreteCategory.comp_apply (prod.lift s c) prod.snd]
  rw [prod.lift_snd]
  rw [← ConcreteCategory.comp_apply (prod.lift prod.snd prod.fst) prod.snd]
  rw [prod.lift_snd]
  rw [← ConcreteCategory.comp_apply (prod.lift s c) prod.fst]
  rw [prod.lift_fst]
  rfl

/-- Composing a product simplex `(s, const ≫ δ₀)` with the homotopy map gives `s ≫ g`.

Geometrically: `δ₀` includes `Δ[0]` as vertex 1 of `Δ[1]`, which under the
standard simplex–interval homeomorphism corresponds to `t = 1` in `I`,
so the homotopy evaluates to `g`. -/
lemma homotopyMap_comp_delta0 {X Y : TopCat.{u}} {n : ℕ} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom' g.hom') (s : Δ[n] ⟶ X) :
    prod.lift s (SimplexCategory.toTop.map default ≫
      SimplexCategory.toTop.map (SimplexCategory.δ 0)) ≫
    homotopyMap H = s ≫ g := by
  ext x
  have h_t : ((TopCat.Hom.hom stdSimplex1_iso_I.hom) ((TopCat.Hom.hom (SimplexCategory.toTop.map default ≫ SimplexCategory.toTop.map (SimplexCategory.δ 0))) x)).down = 1 := by
    change (stdSimplexHomeomorphUnitInterval _ : I) = 1
    ext
    change ((stdSimplexHomeomorphUnitInterval _ : I) : ℝ) = 1
    change ((stdSimplex.map _ _) 1 : ℝ) = 1
    erw [stdSimplex.map_coe]
    rw [FunOnFinite.linearMap_apply_apply]
    change Finset.sum (Finset.filter (fun x_1 => (ConcreteCategory.hom (SimplexCategory.δ 0)) x_1 = (1 : Fin 2)) Finset.univ) _ = 1
    have h0 : Finset.filter (fun x_1 => (ConcreteCategory.hom (SimplexCategory.δ 0)) x_1 = (1 : Fin 2)) Finset.univ = {(0 : Fin 1)} := rfl
    rw [h0, Finset.sum_singleton]
    change ((stdSimplex.map _ x.down) 0 : ℝ) = 1
    erw [stdSimplex.map_coe]
    rw [FunOnFinite.linearMap_apply_apply]
    change Finset.sum (Finset.filter (fun x_1 => (ConcreteCategory.hom (default : SimplexCategory.mk n ⟶ SimplexCategory.mk 0)) x_1 = (0 : Fin 1)) Finset.univ) _ = 1
    have hs : Finset.filter (fun x_1 => (ConcreteCategory.hom (default : SimplexCategory.mk n ⟶ SimplexCategory.mk 0)) x_1 = (0 : Fin 1)) Finset.univ = Finset.univ := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      rfl
    rw [hs]
    exact x.down.property.2
  rw [homotopyMap_eval]
  rw [h_t]
  exact H.apply_one _

/-- Composing a product simplex `(s, const ≫ δ₁)` with the homotopy map gives `s ≫ f`.

Geometrically: `δ₁` includes `Δ[0]` as vertex 0 of `Δ[1]`, which under the
standard simplex–interval homeomorphism corresponds to `t = 0` in `I`,
so the homotopy evaluates to `f`. -/
lemma homotopyMap_comp_delta1 {X Y : TopCat.{u}} {n : ℕ} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom' g.hom') (s : Δ[n] ⟶ X) :
    prod.lift s (SimplexCategory.toTop.map default ≫
      SimplexCategory.toTop.map (SimplexCategory.δ 1)) ≫
    homotopyMap H = s ≫ f := by
  ext x
  have h_t : ((TopCat.Hom.hom stdSimplex1_iso_I.hom) ((TopCat.Hom.hom (SimplexCategory.toTop.map default ≫ SimplexCategory.toTop.map (SimplexCategory.δ 1))) x)).down = 0 := by
    change (stdSimplexHomeomorphUnitInterval _ : I) = 0
    ext
    change ((stdSimplexHomeomorphUnitInterval _ : I) : ℝ) = 0
    change ((stdSimplex.map _ _) 1 : ℝ) = 0
    erw [stdSimplex.map_coe]
    rw [FunOnFinite.linearMap_apply_apply]
    change Finset.sum (Finset.filter (fun x_1 => (ConcreteCategory.hom (SimplexCategory.δ 1)) x_1 = (1 : Fin 2)) Finset.univ) _ = 0
    have h0 : Finset.filter (fun x_1 => (ConcreteCategory.hom (SimplexCategory.δ 1)) x_1 = (1 : Fin 2)) Finset.univ = ∅ := rfl
    rw [h0, Finset.sum_empty]
  rw [homotopyMap_eval]
  rw [h_t]
  exact H.apply_zero _

end HomologyLean.SingularHomology
