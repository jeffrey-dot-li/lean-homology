import HomologyLean.Basic
import HomologyLean.Tactic.NamePartsTest

-- Cellular Homology
import HomologyLean.CellularHomology.CellularChainComplex
import HomologyLean.CellularHomology.Basic
import HomologyLean.CellularHomology.Degree
import HomologyLean.CellularHomology.Agreement
import HomologyLean.CellularHomology.Computations

-- Category Theory
-- TEMP: commented out during mathlib 4.28 → 4.31 migration. The counitIso naturality
-- proof hits the kernel-timeout issue documented in the file, and `Arrow.ext` now needs
-- a third `hom`-compatibility argument. Re-enable after reworking those proofs.
-- import HomologyLean.CategoryTheory.FunctorArrow
import HomologyLean.CategoryTheory.Working
