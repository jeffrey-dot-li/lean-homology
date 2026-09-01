# `Fin.succAbove` / cubical face–degeneracy index algebra

Patterns from proving the cocubical relations in `CubicalSite.lean`
(`face_face`, `degeneracy_degeneracy`, `face_degeneracy_of_lt/_gt`).

## The master helper: `succAbove_succAbove_comm`

Every cocubical commutation reduces to one double-`succAbove` identity
(proved in `CubicalSite.succAbove_succAbove_comm`):

```lean
lemma succAbove_succAbove_comm {n : ℕ} (i j : Fin (n + 1)) (hij : j ≤ i) (k : Fin n) :
    i.succ.succAbove (j.succAbove k) = j.castSucc.succAbove (i.succAbove k)
```

Proof is mathlib's `SimplexCategory.δ_comp_δ` recipe verbatim:

```lean
apply Fin.ext
dsimp only [Fin.succAbove]   -- unfolds to `if castSucc _ < _ then ...` — NOT simp (loops)
rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩; rcases k with ⟨k, hk⟩
split_ifs <;> simp at * <;> omega
```

The `simp at *` between `split_ifs` and `omega` is **essential**: contradictory branches
(e.g. `j ≤ i ∧ k < j ∧ i + 1 < k`) are discharged by `simp at *` deriving `False`;
bare `omega` chokes on atoms like `↑⟨k, hk⟩.castSucc.castSucc` that it can't reduce.

## Peeling faces/degeneracies off a pointwise goal

For a goal about `face`/`degeneracy` applied at a point `k`, case-split on whether `k`
is the hole, using `Fin.exists_succAbove_eq` (`∃ z, p.succAbove z = k ↔ k ≠ p`):

```lean
by_cases hjk : k = j.castSucc
· subst k; rw [..., face_apply_self]        -- hole: face returns the inserted value
rcases Fin.exists_succAbove_eq hjk with ⟨a, rfl⟩
rw [face_apply_succAbove]                    -- off-hole: face peels to the inner tuple
```

Hole-closing API (both directions needed for `of_lt` vs `of_gt`):
- `Fin.succAbove_pred_of_lt (p i) (h : p < i) : p.succAbove (i.pred _) = i`
- `Fin.succAbove_castPred_of_lt (p i) (h : i < p) : p.succAbove (i.castPred _) = i`
- `Fin.succAbove_succ_of_le (p i) (h : i ≤ p) : p.succ.succAbove i = i.castSucc`
- `Fin.succAbove_castSucc_of_le (p i) (h : p ≤ i) : p.castSucc.succAbove i = i.succ`

## Pitfall: prefer `castPred` over `castLT` in `change`/`show` canonicalizations

To make API lemmas match a goal full of proof-term-carrying `Fin`s, first `change` the
goal to use *canonical* proof terms (defeq by proof irrelevance, since
`Fin.pred h = ⟨i-1, _⟩` regardless of `h`). But **`castLT` is reducible while `castPred`
is semireducible**: a `change` mentioning `castLT` leaves downstream terms whose types
mention `Fin ↑(Fin.last (n+1))` instead of `Fin (n+1)` — well-typed, but *not* type-correct
under `instances` transparency, which makes later `rw` fail with
"Did not find an occurrence ... not type-correct under the instances transparency level".
Use `i.castPred (Fin.ne_of_lt (Nat.lt_of_lt_of_le h (Fin.le_last j)))` instead.

Related: the val lemma is **`Fin.coe_castPred`** (`(castPred i h : ℕ) = i`), *not*
`Fin.val_castPred` (doesn't exist).

## Pitfall: `rw` chain leaves a visually-closed goal → trailing `rfl`

After a long `rw` chain through `face_apply_succAbove`/`degeneracy_apply`, the goal can
print as `x ((j.castLT ⋯).succAbove b) = x ((j.castLT ⋯).succAbove b)` yet stay open —
the two `⋯` are *different proof terms*. `rw`'s implicit closing `rfl` doesn't fire.
Diagnose by appending an explicit `rfl`: if it closes the goal, keep it (proof-irrelevance
defeq); if the goal was already closed, remove it ("No goals to be solved").
