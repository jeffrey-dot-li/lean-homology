# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Terminal Settings:
All commands executed with the bash tool are run in the user's fish shell, so ensure compatibility.

## Project Overview

This is a Lean 4 formalization project for basic homology computations in algebraic topology. The project follows proofs from Hatcher's *Algebraic Topology* textbook and builds upon Mathlib's algebraic topology foundations.

**Main theorem**: The n-dimensional sphere is simply connected for n ≥ 2 (`EuclideanSphere.simplyConnectedSpace`).

## Build System: Lake

Lake is Lean's build system and package manager. Common commands:

```bash
# Build the entire project
lake build

# Build and update dependencies
lake update

# Build a specific target (the library)
lake build HomologyLean

# Execute Lake commands in the project environment
lake env <command>

# Clean build artifacts
lake clean
```

## Development Commands

```bash
# Check a single Lean file for errors
lake env lean HomologyLean/Basic.lean

# Build the project (builds all .lean files)
lake build

# Update Mathlib and other dependencies to versions specified in lakefile.toml
lake update
```

## Project Structure

- **HomologyLean.lean**: Root file that imports all modules in the project
- **HomologyLean/Basic.lean**: Currently contains minimal placeholder code
- **HomologyLean/SimplyConnectedSphere/**: Main proof that n-spheres are simply connected
  - `SimplyConnectedSphere.lean`: Proves `EuclideanSphere.simplyConnectedSpace` following Hatcher's proof strategy
- **HomologyLean/Topology/**: Supporting topology definitions
  - `Subpath.lean`: Defines `Path.subpath` for restricting paths to subintervals
  - `FoldTrans.lean`: Implements `foldTrans` for concatenating sequences of paths with compatible endpoints

## Architecture

### Key Proof Strategy

The simply connected sphere proof uses an **open cover approach** (Lemma 1.15 from Hatcher):

1. Cover the n-sphere with open sets whose pairwise intersections are path-connected
2. Decompose any loop into a concatenation of loops, each contained in one element of the cover
3. Show each loop is homotopically trivial using contractibility of the sphere minus a point
4. Conclude the entire loop is homotopically trivial

### Important Definitions

- **`foldTrans`** (FoldTrans.lean): Concatenates a sequence of paths with compatible endpoints using `Fin.dfoldl`
- **`Path.subpath`** (Subpath.lean): Restricts a path to a subinterval [t₀, t₁], reparameterized to [0, 1]
- **`exists_loops_homotopic_foldTrans_of_open_cover`** (SimplyConnectedSphere.lean): Core lemma showing any loop can be decomposed into a sequence of loops in an open cover

### Dependencies

The project depends on:
- **mathlib** (v4.28.0-rc1): Lean's mathematics library providing fundamental definitions and theorems
- Standard dependencies: plausible, LeanSearchClient, importGraph, proofwidgets, aesop, Qq, batteries, Cli

### Lean Options (lakefile.toml)

- `pp.unicode.fun = true`: Pretty-prints `fun a ↦ b` with Unicode
- `relaxedAutoImplicit = false`: Disables automatic insertion of implicit arguments
- `weak.linter.mathlibStandardSet = true`: Enables Mathlib linting standards
- `maxSynthPendingDepth = 3`: Controls type class synthesis depth

## File Organization

Lean files follow standard Mathlib conventions:
- Copyright headers with Apache 2.0 license
- Module docstrings (`/-! ... -/`) explaining purpose and main results
- Imports at the top
- `noncomputable section` when definitions require classical reasoning
- `open` declarations for commonly used namespaces

## Notation Conventions

- `S n` denotes the n-sphere in `EuclideanSpace ℝ (Fin (n + 1))`
- `I` denotes the unit interval `[0, 1]`
- Homotopy and path operations use Mathlib's `FundamentalGroupoid` framework