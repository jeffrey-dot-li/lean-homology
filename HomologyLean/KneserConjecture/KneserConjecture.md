# Kneser's Conjecture: Proof Structure

This document outlines the proof of Kneser's Conjecture following Lovász's 1978 paper "Kneser's Conjecture, Chromatic Number, and Homotopy."

## Main Theorem

**Theorem 1 (Kneser's Conjecture):** If we split the n-subsets of a (2n + k)-element set into k + 1 classes, one of the classes will contain two disjoint n-subsets.

### Equivalent Formulation via Kneser Graphs

**Definition (Kneser Graph):** The Kneser graph KG(n,k) has:
- **Vertices:** All n-subsets of {1, 2, ..., 2n + k}
- **Edges:** Two n-subsets are joined by an edge iff they are disjoint

**Theorem 1' (Equivalent):** The chromatic number of KG(n,k) is k + 2.

*Note:* KG(2,1) is the well-known Petersen graph.

---

## Key Definitions

### Neighborhood Complex

**Definition:** Let G be a graph. The *neighborhood complex* N(G) is the simplicial complex whose:
- **Vertices:** The vertices of G
- **Simplices:** Subsets of V(G) which have a common neighbor

**Notation:** For any simplicial complex K, we denote by K̃ the geometric realization (polyhedron) determined by K.

### n-Connectedness

**Definition:** A topological space T is *n-connected* if every continuous mapping of S^r (the r-dimensional sphere) into T extends continuously to the whole (r+1)-dimensional ball, for r = 0, 1, ..., n.

*Intuition:* n-connected means there are no "holes" in dimensions 0 through n.

### Common Neighbor Function

**Definition:** For X ⊆ V(G), let ν(X) denote the set of common neighbors of X.

---

## Proof Structure

The proof proceeds via two key theorems:

### Theorem 2 (Topological Obstruction to Coloring)

**Statement:** If Ñ(G) is (k + 2)-connected, then G is not k-colorable.

**Corollary:** Ñ(G) is never homotopically trivial (for non-bipartite G).

### Theorem 3 (Connectivity of Kneser Neighborhood Complex)

**Statement:** Let S be a finite set and n, k natural numbers. Consider the simplicial complex K whose:
- **Vertices:** The n-subsets of S
- **Simplices:** Sets {A₀, ..., Aₘ} of n-subsets for which |⋃ᵢ₌₀ᵐ Aᵢ| ≤ n + k

Then K is (k − 1)-connected.

### How They Combine

**Key observation:** For |S| = 2n + k, the complex K in Theorem 3 is exactly the neighborhood complex N(KG(n,k)).

*Why?* In KG(n,k), vertices are n-subsets of S. A collection {A₀, ..., Aₘ} has a common neighbor iff there exists an n-subset B disjoint from each Aᵢ. This requires B ⊆ S \ ⋃Aᵢ with |B| = n, so |S \ ⋃Aᵢ| ≥ n, i.e., |⋃Aᵢ| ≤ |S| − n = (2n + k) − n = n + k.

**Applying the theorems:**

Theorem 2 restated: If Ñ(G) is m-connected, then G is not (m + 2)-colorable.

- By Theorem 3: N(KG(n,k)) is (k − 1)-connected
- By Theorem 2 with m = k − 1: KG(n,k) is not (k − 1 + 2) = (k + 1)-colorable
- Therefore: χ(KG(n,k)) ≥ k + 2

The upper bound χ(KG(n,k)) ≤ k + 2 is easy (partition n-subsets by their smallest element into k + 2 classes), so χ(KG(n,k)) = k + 2.

---

## Proof of Theorem 2

### Setup: Barycentric Subdivision

Let N₁(G) denote the barycentric subdivision of N(G).

**Vertices of N₁(G):** Sets X ⊂ V(G) whose elements have a common neighbor (i.e., X is contained in the neighborhood of some vertex).

**Simplices of N₁(G):** Collections {X₁, ..., Xₘ} that form a chain with respect to inclusion.

*Fact:* Ñ(G) and Ñ₁(G) are homeomorphic.

### The ν Map

For X ⊂ V(G), let ν(X) be the set of common neighbors of X.

**Key properties:**
1. ν maps vertices of N₁(G) to vertices of N₁(G)
2. X ⊆ Y implies ν(X) ⊇ ν(Y), so ν is simplicial
3. Extend ν simplicially to a continuous map ν̃: Ñ₁(G) → Ñ₁(G)

**Crucial identity:**
```
ν³ = ν    and    ν̃³ = ν̃                    (1)
```

*Proof of (1):* If X has common neighbors ν(X), then the common neighbors of ν(X) include all vertices adjacent to all of ν(X). Any vertex in X is adjacent to all of ν(X), so X ⊆ ν(ν(X)) = ν²(X). Thus ν³(X) ⊆ ν(X). But also clearly ν(X) ⊆ ν³(X) by applying ν² to both sides of X ⊆ ν²(X).

### Constructing Antipodal Maps φᵣ: Sʳ → Ñ₁(G)

We construct maps φᵣ: Sʳ → Ñ₁(G) for r = 0, 1, ..., k − 1 by induction such that:

```
φᵣ(−x) = ν̃(φᵣ(x))                          (2)
```

for all x ∈ Sʳ (where −x is the antipodal point of x).

#### Base Case: r = 0

S⁰ = {+1, −1} consists of two points.

- Let v be an arbitrary point of Ñ₁(G)
- Set φ₀(+1) = ν̃(v)
- Set φ₀(−1) = ν̃²(v)

**Verification:** φ₀(−1) = ν̃²(v) = ν̃(ν̃(v)) = ν̃(φ₀(+1)) ✓

#### Inductive Step: r ≥ 1

Assume φᵣ₋₁: Sʳ⁻¹ → Ñ₁(G) is defined satisfying (2).

**Notation:**
- S⁺ = upper hemisphere of Sʳ
- S⁻ = lower hemisphere of Sʳ
- S⁺ ∩ S⁻ = Sʳ⁻¹ (the equator)

**Construction:**

Since Ñ₁(G) is k-connected (by hypothesis), we can extend φᵣ₋₁ to a continuous map ψ: S⁺ → Ñ₁(G).

Define:
```
         ⎧ ν̃²(ψ(x))    if x ∈ S⁺
φᵣ(x) = ⎨                              (3)
         ⎩ ν̃(ψ(−x))    if x ∈ S⁻
```

**Verification that this is well-defined on Sʳ⁻¹ = S⁺ ∩ S⁻:**

For x ∈ Sʳ⁻¹:
- From S⁺ definition: ν̃²(ψ(x)) = ν̃²(φᵣ₋₁(x))
- From S⁻ definition: ν̃(ψ(−x)) = ν̃(φᵣ₋₁(−x)) = ν̃(ν̃(φᵣ₋₁(x))) = ν̃²(φᵣ₋₁(x))

These agree! ✓

**Verification of antipodal property (2):**

*Case x ∈ S⁺:* Then −x ∈ S⁻, so:
- φᵣ(−x) = ν̃(ψ(−(−x))) = ν̃(ψ(x))
- ν̃(φᵣ(x)) = ν̃(ν̃²(ψ(x))) = ν̃³(ψ(x)) = ν̃(ψ(x)) by (1)

Thus φᵣ(−x) = ν̃(φᵣ(x)) ✓

*Case x ∈ S⁻:* Then −x ∈ S⁺, so:
- φᵣ(−x) = ν̃²(ψ(−x))
- ν̃(φᵣ(x)) = ν̃(ν̃(ψ(−x))) = ν̃²(ψ(−x))

Thus φᵣ(−x) = ν̃(φᵣ(x)) ✓

### Deriving Contradiction from k-Coloring

Suppose G admits a k-coloring.

**Define:** Let Nᵢ (for i = 1, ..., k) be the subcomplex of N(G) formed by simplices whose vertices have a common neighbor of color i.

**Observation 1:**
```
Ñ(G) = Ñ₁ ∪ ··· ∪ Ñₖ
```

**Observation 2:**
```
Ñᵢ ∩ ν̃(Ñᵢ) = ∅
```

*Proof of Observation 2:* Suppose x ∈ Ñᵢ and ν̃(x) ∈ Ñᵢ. Then:
- x belongs to a simplex of N(G) spanned by the neighborhood of some vertex v of color i
- In the barycentric subdivision, x is in the interior of a unique simplex spanned by vertices X₁, ..., Xₘ ⊆ ν(v) of N₁(G)
- Then Yⱼ = ν(Xⱼ) ∋ v for each j, and ν̃(x) is in the interior of the simplex spanned by some of Y₁, ..., Yₘ
- Since ν̃(x) ∈ Ñᵢ, there exists a vertex u of color i such that some Yⱼ ⊆ ν(u)
- But then u, v are adjacent vertices of G (since v ∈ Yⱼ ⊆ ν(u) means u ~ v), both of color i

This contradicts proper k-coloring. □

### Applying Borsuk's Theorem

**Define:** Fᵢ = φₖ₋₁⁻¹(Ñᵢ) (preimage of Ñᵢ under φₖ₋₁)

**Properties:**
1. Each Fᵢ is a closed subset of Sᵏ⁻¹
2. F₁ ∪ ··· ∪ Fₖ = Sᵏ⁻¹
3. **No Fᵢ contains antipodal points:**

*Proof of (3):* If x ∈ Fᵢ and −x ∈ Fᵢ, then:
- φₖ₋₁(x) ∈ Ñᵢ
- φₖ₋₁(−x) = ν̃(φₖ₋₁(x)) ∈ Ñᵢ

This contradicts Ñᵢ ∩ ν̃(Ñᵢ) = ∅. □

**Borsuk's Theorem:** If Sᵏ = F₁ ∪ ··· ∪ Fₖ₊₁ where F₁, ..., Fₖ₊₁ are closed, then one of the Fᵢ contains two antipodal points.

But we have covered Sᵏ⁻¹ with k closed sets, none containing antipodal points. This contradicts Borsuk's Theorem!

Therefore G is not k-colorable. □

---

## Proof of Theorem 3

**Goal:** Show that the simplicial complex K (whose vertices are n-subsets of S and whose simplices are collections with |union| ≤ n + k) is (k − 1)-connected.

### Definitions for the Proof

For a simplex A = {A₀, ..., Aₘ} in K:
- **U(A)** = ⋃ᵢ₌₀ᵐ Aᵢ (the union of all sets in A)
- **M(A)** = the simplex spanned by all n-subsets of U(A)
- A is **crowded** if |U(A)| < n + k

### Proof by Induction on |S|

**Base case:** If |S| ≤ n + k, then K is a single simplex (all n-subsets have union ⊆ S with |S| ≤ n + k), hence contractible.

**Inductive step:** Assume |S| > n + k.

**Define:**
- K' = closed subcomplex of K whose simplices are the crowded simplices
- K₀ = (k − 1)-skeleton of K (simplices of dimension ≤ k − 1)

### Step 1: Deform K̃₀ into K̃'

We construct a continuous map ψ: K̃₀ → K̃' such that:

```
(*) For each simplex A of K₀, ψ(Ã) lies in M̃(A)
```

This implies ψ is homotopic to the inclusion K̃₀ ↪ K̃.

**Construction by induction on dim(A):**

*If dim(A) = 0:* A single vertex (n-subset) A is automatically crowded since |U(A)| = |A| = n < n + k. Set ψ(A) = A.

*If dim(A) > 0:* Assume ψ is defined on ∂Ã (boundary of Ã) satisfying (*).

Consider K'_A = subcomplex of K' induced by vertices of M(A), i.e., the crowded simplices contained in M(A).

By induction hypothesis on |S|: Since |U(A)| ≤ n + k < |S|, the complex K'_A is (r − 1)-connected where r = dim(A).

By (*), ψ(∂Ã) ⊆ K̃'_A. Since K̃'_A is (r − 1)-connected and ∂A ≅ Sʳ⁻¹, we can extend ψ over the interior of Ã.

### Step 2: Contract K̃' to a Point

For u, v ∈ S, define φᵤᵥ: K' → K' on vertices (n-subsets X ⊆ S) by:

```
         ⎧ X − {u} ∪ {v}   if u ∈ X but v ∉ X
φᵤᵥ(X) = ⎨
         ⎩ X               otherwise
```

**Claim:** φᵤᵥ is simplicial (maps simplices to simplices).

*Proof:* If A = {A₀, ..., Aₘ} is a crowded simplex:
- If u ∉ U(A): then φᵤᵥ(A) = A, still crowded
- If u ∈ U(A) and v ∉ U(A): then U(φᵤᵥ(A)) = U(A) − {u} ∪ {v}, so |U(φᵤᵥ(A))| = |U(A)| < n + k
- If both u, v ∈ U(A): then U(φᵤᵥ(A)) ⊆ U(A), so |U(φᵤᵥ(A))| ≤ |U(A)| < n + k

In all cases, φᵤᵥ(A) is crowded. □

**Key observation:**
```
(**) φᵤᵥ(Ã) ∪ Ã is contained in the simplex of K̃ spanned by n-subsets of U(A) ∪ {v}
```

This implies φᵤᵥ is homotopic to the identity in K̃.

### Contracting to a Single Point

Fix elements u₁, u₂, ..., uₙ ∈ S. Consider the composition:

```
φᵤₙuₙ₋₁ ∘ φᵤₙuₙ₋₂ ∘ ··· ∘ φᵤₙu₁ ∘ φᵤₙ₋₁uₙ₋₂ ∘ ··· ∘ φᵤ₂u₁
```

This composition maps every n-subset of S to {u₁, ..., uₙ}.

Since each φᵤᵥ is homotopic to the identity in K̃, this composition is homotopic to the identity. But the image is a single point {u₁, ..., uₙ}.

Therefore K̃' is contractible.

### Conclusion

- K̃₀ can be deformed into K̃' within K̃ (Step 1)
- K̃' is contractible in K̃ (Step 2)
- Therefore K̃₀ is contractible in K̃
- Therefore K is (k − 1)-connected □

---

## Summary of Logical Dependencies

```
Theorem 3                    Borsuk's Theorem
    |                              |
    v                              v
N(KG(n,k)) is              Sᵏ⁻¹ covered by k closed
(k-1)-connected            sets ⟹ one has antipodal pair
    |                              |
    +------------+   +-------------+
                 |   |
                 v   v
              Theorem 2
                 |
                 v
         KG(n,k) is not
         (k+1)-colorable
                 |
                 v
         χ(KG(n,k)) ≥ k + 2
                 |
                 v
           Theorem 1
       (Kneser's Conjecture)
```

---

## Definitions to Formalize

### Required Mathematical Objects

1. **Kneser Graph** `KG(n, k)` - the graph structure
2. **Simplicial Complex** - abstract simplicial complex
3. **Geometric Realization** - topological space from simplicial complex
4. **Neighborhood Complex** `N(G)` - simplicial complex from graph
5. **Barycentric Subdivision** - refinement of simplicial complex
6. **n-Connectedness** - topological property
7. **Chromatic Number** - graph coloring invariant

### Required Theorems from Library

1. **Borsuk-Ulam Theorem** (or Borsuk's covering theorem)
2. **Simplicial maps are continuous** on geometric realizations
3. **Barycentric subdivision is homeomorphic** to original
4. **Extension of maps from spheres** (characterization of n-connectedness)

---

## Formalization Strategy

### Phase 1: Graph Theory Foundations
- Define Kneser graph
- Define graph coloring and chromatic number
- Prove basic properties

### Phase 2: Simplicial Complex Theory
- Abstract simplicial complexes
- Geometric realization (might use existing Mathlib)
- Barycentric subdivision
- Simplicial maps

### Phase 3: Neighborhood Complex
- Define N(G) for a graph G
- Define the ν function and prove ν³ = ν
- Prove simplicial extension ν̃

### Phase 4: Connectivity
- Define n-connectedness
- Prove Theorem 3 (connectivity of Kneser neighborhood complex)

### Phase 5: Main Proof
- Construct the antipodal maps φᵣ
- Apply Borsuk's theorem
- Conclude Theorem 2
- Derive Kneser's conjecture

---

## Open Questions / Points to Clarify

1. **Borsuk's Theorem version:** The paper uses "covering by k+1 closed sets implies one contains antipodal pair." Is this equivalent to Borsuk-Ulam? (Answer: Yes, it's a consequence.)

2. **Connectivity indexing:** Need to verify exact indices. Paper says "if Ñ(G) is (k+2)-connected then G is not k-colorable" and "K is (k-1)-connected" for the Kneser complex. Need to trace through carefully.

3. **Does Mathlib have geometric realization?** May need to construct or use a simpler model.
