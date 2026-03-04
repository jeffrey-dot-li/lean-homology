/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 26a7fa58-6a33-4e05-8733-87434844a3c3

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma sum_sum_involution_zero {α β M : Type*}
    [Fintype α] [Fintype β] [AddCommGroup M]
    (p : α → β → Prop) [∀ a, DecidablePred (p a)]
    (f : α → β → M)
    (g : (a : α) → (b : β) → p a b → α)
    (hg_pred : ∀ a b h, p (g a b h) b)
    (hg_invol : ∀ a b h, g (g a b h) b (hg_pred a b h) = a)
    (hg_neg : ∀ a b h, f (g a b h) b = -f a b)
    (hg_ne : ∀ a b h, g a b h ≠ a) :
    (∑ a : α, Finset.sum (Finset.univ.filter (p a)) (f a)) = 0

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Mathlib.Tactic
import Mathlib.Tactic.GeneralizeProofs

noncomputable section

namespace HomologyLean.SumInvolution

lemma sum_sum_involution_zero {α β M : Type*}
    [Fintype α] [Fintype β] [AddCommGroup M]
    (p : α → β → Prop) [∀ a, DecidablePred (p a)]
    (f : α → β → M)
    (g : (a : α) → (b : β) → p a b → α)
    (hg_pred : ∀ a b h, p (g a b h) b)
    (hg_invol : ∀ a b h, g (g a b h) b (hg_pred a b h) = a)
    (hg_neg : ∀ a b h, f (g a b h) b = -f a b)
    (hg_ne : ∀ a b h, g a b h ≠ a) :
    (∑ a : α, Finset.sum (Finset.univ.filter (p a)) (f a)) = 0 := by
  -- Let `S` be the sigma finset `(Finset.univ : Finset α).sigma (λ a => (Finset.univ : Finset β).filter (p a))`.
  set S : Finset (Σ a, β) := (Finset.univ : Finset α).sigma (fun a => Finset.filter (p a) Finset.univ);
  -- By definition of $S$, we can rewrite the double sum as a single sum over $S$.
  suffices h_sum_S : ∑ x ∈ S, f x.1 x.2 = 0 by
    rw [ ← h_sum_S, Finset.sum_sigma ];
  -- Define the involution `G : (x : Σ a, β) → x ∈ S → Σ a, β` by `G ⟨a, b⟩ h = ⟨g a b h, b⟩`.
  set G : (x : Σ a, β) → x ∈ S → Σ a, β := fun x hx => ⟨g x.fst x.snd (by
  aesop), x.snd⟩
  generalize_proofs at *;
  apply Finset.sum_involution (fun x hx => G x hx) (by
  grind) (by
  grind +ring) (by
  aesop) (by
  grind)

end SumInvolution

end HomologyLean
