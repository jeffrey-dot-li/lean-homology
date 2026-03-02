# Memory Index

Cross-session knowledge for the homology-lean project.

## Always read before proof work

- [`proof-strategies.md`](proof-strategies.md) — General tactic patterns, goal state discipline, and Lean gotchas

## API-specific files — load when relevant

| File | Load when working on... |
|------|------------------------|
| [`api/coproducts-sigma.md`](api/coproducts-sigma.md) | Sigma types, coproduct isos, `PreservesCoproduct`, `DirectSum`/`Finsupp` bridges |
| [`api/topcat-limits.md`](api/topcat-limits.md) | `TopCat` products, `prodIsoProd`, pointwise evaluation of limit maps |
| [`api/monoidal-tensor.md`](api/monoidal-tensor.md) | Monoidal categories, tensor products, `ModuleCat.free`, `NatIso.ofComponents` |
| [`api/homology-shortcomplex.md`](api/homology-shortcomplex.md) | `ShortComplex`, homology functor, AB4, connecting homomorphism δ, chain map mono |

## When to update memory

After completing a tricky `/fill-sorry` proof, check if the strategy generalizes:
- New general tactic pattern or Lean gotcha? → `proof-strategies.md`
- API-specific proof pattern, pitfall, or useful lemma? → appropriate `api/` file (create a new one if no file fits)
