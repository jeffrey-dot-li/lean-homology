# Memory Index

Cross-session knowledge for the homology-lean project.

## Always read before proof work

- [`proof-strategies.md`](proof-strategies.md) — General tactic patterns, goal state discipline, and Lean gotchas

## API-specific files — search with rg

To find relevant entries, search the `api/` folder rather than reading files whole:
```bash
rg -i "keyword" .claude/memory/api/
```
Then read the full section from the matching file if needed.

| File | Topics |
|------|--------|
| [`api/coproducts-sigma.md`](api/coproducts-sigma.md) | Sigma types, coproduct isos, `PreservesCoproduct`, `DirectSum`/`Finsupp` bridges |
| [`api/topcat-limits.md`](api/topcat-limits.md) | `TopCat` products, `prodIsoProd`, pointwise evaluation of limit maps |
| [`api/monoidal-tensor.md`](api/monoidal-tensor.md) | Monoidal categories, tensor products, `ModuleCat.free`, `NatIso.ofComponents` |
| [`api/homology-shortcomplex.md`](api/homology-shortcomplex.md) | `ShortComplex`, homology functor, AB4, connecting homomorphism δ, chain map mono |
| [`api/homotopy-paths.md`](api/homotopy-paths.md) | `Path.Homotopic`, `HomotopyRel`, quotients, covering maps |
| [`api/chain-complex.md`](api/chain-complex.md) | `HomologicalComplex.d`, `Nat.add` index shifting, `eqToHom_comp_d`, face map expansion |
| [`api/transport-cast.md`](api/transport-cast.md) | `h ▸` transport elimination, `generalize`+`rcases` trick, successor-index blockers, `cast`↔`eqToHom` |
| [`api/eqToHom-casting.md`](api/eqToHom-casting.md) | `eqToHom` through functors (TopCat/SimplexCategory), `eqToHom_map`, `Functor.map_comp` folding, `slice_lhs`/`slice_rhs`, Fin.succAbove simp recipe |
| [`api/sset-yoneda-ulift.md`](api/sset-yoneda-ulift.md) | `SSet.yonedaEquiv`, `stdSimplex.objEquiv`, `ULift` bridge lemmas, namespace collision with `SSet.stdSimplex`, `uliftYonedaEquiv` |
| [`api/dold-kan-moore-retraction.md`](api/dold-kan-moore-retraction.md) | `degeneracy_comp_PInfty`, `PInftyToNormalizedMooreComplex` glue (kill degenerate ops), generalizing inner glue to fire at outer/bisimplicial level, decomposing bi-graded retraction `R'`, EZ∘AW summand merge |

## When to update memory

After completing a tricky `/fill-sorry` proof, check if the strategy generalizes:
- New general tactic pattern or Lean gotcha? → `proof-strategies.md`
- API-specific proof pattern, pitfall, or useful lemma? → appropriate `api/` file (create a new one if no file fits)
