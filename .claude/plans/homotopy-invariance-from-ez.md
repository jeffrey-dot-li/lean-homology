# Deriving homotopy invariance from `EilenbergZilber.lean`

This note records the current conclusion about the relationship between
`HomotopyInvariance.lean` and `EilenbergZilber.lean`.

## Main conclusion

`singularHomology_iso_of_homotopyEquiv` should be derivable from what is already proved in
`HomologyLean/SingularHomology/EilenbergZilber.lean`, without introducing any new deep
shuffle/combinatorial arguments.

In particular, the old homotopy-invariance proof does **not** appear to require a second
independent cross-product development. The cross-product combinatorics should remain centralized
in `EilenbergZilber.lean`.

What is still needed is mainly:

- interval-specific specialization;
- categorical / chain-level plumbing;
- exposing the right consequences of the existing EZ theory as downstream-facing API.

## What already exists in `EilenbergZilber.lean`

At the chain-map / natural-transformation level, the main ingredients are already present:

- the simplicial-set Eilenberg-Zilber chain map;
- its naturality theorem;
- the simplicial-set natural transformation;
- the topological natural transformation
  `TopCat.eilenbergZilberNatTrans`;
- the general Leibniz rule for the cross product;
- the zero-left / zero-right specializations of the cross product.

So the main categorical object one wants for downstream use already exists:

```lean
TopCat.eilenbergZilberNatTrans :
  Functor.prod ((singularChainComplexFunctor C).obj (𝟙_ C))
      ((singularChainComplexFunctor C).obj (𝟙_ C)) ⋙
    MonoidalCategory.tensor (C := ChainComplex C ℕ) ⟶
  MonoidalCategory.tensor (C := TopCat) ⋙
    (singularChainComplexFunctor C).obj (𝟙_ C)
```

## What the homotopy-invariance proof should still need

To recover `singularChain_chainHomotopy_of_homotopy`, and hence
`singularHomology_map_eq_of_homotopy` / `singularHomology_iso_of_homotopyEquiv`, the remaining
work should be:

1. specialize the existing EZ Leibniz rule to the interval case;
2. specialize zero-right cross-product evaluation to the two endpoints of `Δ[1]`;
3. combine those with `homotopyMap_comp_delta0` and `homotopyMap_comp_delta1` from
   `HomotopyMap.lean`;
4. package the resulting prism operator as a chain homotopy;
5. deduce the homology-level corollaries.

This is a derivation / packaging task, not a new combinatorial proof.

## Small new facts that may still be needed

The main thing that may still need to be stated and proved directly is the boundary of the
fundamental `1`-simplex of `Δ[1]`, i.e. the old lemma

- `boundary_identity_1simplex_generic`

This should not be thought of as a new shuffle/combinatorial argument. It is just the basic
degree-`1` singular boundary computation on the interval simplex.

So the likely split is:

- no new shuffle insertion / involution / sign-cancellation lemmas;
- yes, a few interval-specific boundary and endpoint lemmas.

## API guidance

The right public API should be built around the already existing topological EZ map, plus a small
set of interval-specialized consequences.

Good candidates for public API:

- `TopCat.eilenbergZilberNatTrans`
- the boundary lemma for the interval fundamental simplex
- `singularChain_chainHomotopy_of_homotopy`
- `singularHomology_map_eq_of_homotopy`
- `singularHomology_iso_of_homotopyEquiv`

Likely private / proof-local:

- degree-specific `(0,1)` special-case Leibniz lemmas, unless they emerge as very clean
  corollaries;
- endpoint-evaluation lemmas phrased in the most proof-local style;
- any remaining tensor / coprojection plumbing used only inside the prism argument.

## Practical goal

The practical target is:

1. keep all genuine cross-product combinatorics in `EilenbergZilber.lean`;
2. rebuild homotopy invariance from EZ and `HomotopyMap.lean`;
3. shrink `HomotopyInvariance.lean` to thin corollaries, or replace it by the new derivation.

## Current judgment

The existing EZ development is already strong enough. What remains is mostly choosing and exposing
the right interval-specialized consequences, not proving new hard mathematics.
