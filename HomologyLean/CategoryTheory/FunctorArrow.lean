/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Products.Basic

/-!
# Functor–Arrow Equivalence

The functor category into the arrow category is equivalent to the arrow category of the
functor category: `(C ⥤ Arrow D) ≌ Arrow (C ⥤ D)`.

## Main results

* `functorArrowEquiv`: the equivalence `(C ⥤ Arrow D) ≌ Arrow (C ⥤ D)`.
-/

open CategoryTheory
open CategoryTheory.NatIso

universe v u

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- The functor category into the arrow category is equivalent to the arrow category of the
functor category: `(C ⥤ Arrow D) ≌ Arrow (C ⥤ D)`.

An object of `C ⥤ Arrow D` assigns to each `c : C` an arrow in `D`, naturally.
An object of `Arrow (C ⥤ D)` is a natural transformation between two functors `C ⥤ D`.
These are the same data. -/
noncomputable def functorArrowEquiv : (C ⥤ Arrow D) ≌ Arrow (C ⥤ D) where
  functor := {
    obj F := {
      left := {
        obj c := (F.obj c).left
        map f := (F.map f).left
      }
      right := {
        obj c := (F.obj c).right
        map f := (F.map f).right
      }
      hom := {
        app := fun c => (F.obj c).hom
        naturality := fun c c' f => (F.map f).w
      }
    }
    map {F G} (l) := {
      -- Given l : F ⟶ G in (C ⥤ Arrow D), at each c we get (l.app c) : F.obj c ⟶ G.obj c
      -- in Arrow D, whose .left component gives a map (F.obj c).left ⟶ (G.obj c).left.
      left := {
        app := fun c => (l.app c).left
        naturality := fun c c' f => congrArg CommaMorphism.left (l.naturality f)
      }
      right := {
        app := fun c => (l.app c).right
        naturality := fun c c' f => congrArg CommaMorphism.right (l.naturality f)
      }
      w := by ext c; exact (l.app c).w
    }
  }
  inverse := {
    -- An arrow η : F ⟶ G in (C ⥤ D) maps to the functor c ↦ Arrow.mk (η.app c).
    obj η := {
      obj := fun c => Arrow.mk (η.hom.app c)
      map := fun {c c'} f =>
        Arrow.homMk (η.left.map f) (η.right.map f) (η.hom.naturality f)
    }
    map {η η'} φ := {
      -- φ : η ⟶ η' in Arrow (C ⥤ D), i.e. φ.left : η.left ⟶ η'.left and
      -- φ.right : η.right ⟶ η'.right with η.hom ≫ φ.right = φ.left ≫ η'.hom.
      -- At each c, we get an arrow morphism from Arrow.mk (η.hom.app c) to Arrow.mk (η'.hom.app c).
      app := fun c => Arrow.homMk (φ.left.app c) (φ.right.app c) (congr_app φ.w c)
    }
  }

  unitIso := NatIso.ofComponents (fun F => Iso.refl _) (by
    intros; ext <;> simp only [Functor.id_obj, Functor.comp_obj, Arrow.mk_left, Arrow.mk_right,
      Functor.id_map, Iso.refl_hom, Category.comp_id, Functor.comp_map, Category.id_comp,
      Arrow.homMk_left, Arrow.homMk_right])

  /-
  ## counitIso: performance investigation notes

  The counitIso proves naturality of `inverse ⋙ functor ≅ 𝟭 (Arrow (C ⥤ D))`.
  This direction is fundamentally harder than unitIso because the composition
  `inverse ⋙ functor` first reassembles via `Arrow.homMk` (which carries a proof
  term `w` from `by simp` / `congr_app φ.w c`), then extracts `.left`/`.right`.
  Closing the final goals requires the kernel to check definitional equality
  *through* those proof terms, which is extremely expensive.

  ### Approaches tried (all timeout on the final `.left`/`.right` projection step):

  1. **`Iso.refl _` + `simp_all` + `rfl`** (original aesop_cat output):
     Correct but takes 5+ min. `simp_all` searches the enormous unfolded term.

  2. **`Iso.refl _` + targeted `simp only` + `rfl`/`simp`/`dsimp`**:
     `simp only [Iso.refl_hom, comp_id, id_comp, comp_map, id_map]` reduces the
     goals to `(Arrow.homMk u v ⋯).left = u` quickly. But closing *that* times
     out — `rfl`, `exact rfl`, `simp [Arrow.homMk_left]`, `dsimp [Arrow.homMk]`,
     and `dsimp only [Arrow.homMk]` all cause the kernel to unfold the proof term
     `⋯` inside `Arrow.homMk`.

  3. **`Arrow.isoMk` components + `simp only` with `Arrow.comp_left` etc.**:
     Using `Arrow.isoMk (NatIso.ofComponents (fun c => Iso.refl _)) ...` for the
     component iso compiles fast. The naturality `simp only` with
     `[comp_left, comp_right, NatTrans.comp_app, isoMk_hom_left, isoMk_hom_right,
       ofComponents_hom_app, Iso.refl_hom, comp_id, id_comp]`
     reduces to the same `(Arrow.homMk u v ⋯).left = u` bottleneck.

  4. **Anonymous constructor `⟨u, v, proof⟩` instead of `Arrow.homMk`** in `inverse`:
     Replacing `Arrow.homMk` with direct `CommaMorphism.mk` via `⟨...⟩` — the idea
     being that `.left` of a constructor reduces immediately. This also timed out,
     likely because the `by simp` proof term in `obj.map` is still large.

  ### MCP testing protocol for timeout-sensitive proofs:

  When testing tactics that might cause Lean to hang:
  - Add new lemmas to `simp only [...]` ONE AT A TIME and check diagnostics after
    each. If `success: false` with no error items persists across 3+ checks, the
    tactic is likely hanging.
  - Never add `rfl`, `simp`, or `dsimp` after a `simp only` that reduces to
    Arrow/Comma projection goals — these are the timeout triggers.
  - Use `all_goals sorry` as a firewall: put it after the fast `simp only` pass
    to confirm that part compiles, then try closing the remaining goals separately.
  - If `lean_diagnostic_messages` returns `Error: Aborted` or timeouts repeatedly,
    revert to a `sorry`'d state before the LSP becomes permanently unresponsive.

  ### Likely root cause and possible fix:

  The `by simp` proof in `inverse.obj.map` elaborates to a large term that the
  kernel must normalize when checking `.left` projection of `Arrow.homMk`. A fix
  would require making that proof term *definitionally transparent* — e.g., by
  giving an explicit `Eq.trans` / `congrArg` proof instead of `by simp`, or by
  restructuring `inverse` to avoid `Arrow.homMk` entirely (using eta-expanded
  Comma constructors whose fields reduce by iota).
  -/
  counitIso := NatIso.ofComponents
    (fun F => Arrow.isoMk (NatIso.ofComponents (fun c => Iso.refl _))
      (NatIso.ofComponents (fun c => Iso.refl _)) (by ext; simp))
    (by
      intros; ext
      all_goals simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map,
        Arrow.comp_left, Arrow.comp_right, NatTrans.comp_app,
        Arrow.isoMk_hom_left, Arrow.isoMk_hom_right, NatIso.ofComponents_hom_app,
        Iso.refl_hom, Category.comp_id, Category.id_comp]
      -- Remaining goals are `(Arrow.homMk u v ⋯).left = u` (and .right variant).
      -- These are definitionally true but all closers (rfl, simp, dsimp) timeout
      -- because the kernel unfolds the proof term ⋯ inside Arrow.homMk.
      all_goals sorry)
