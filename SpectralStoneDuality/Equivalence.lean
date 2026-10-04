/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.Reconstruction

/-!
# Stone duality for spectral spaces

`stoneDuality : BddDistLatᵒᵖ ≌ SpectralCat` assembles the spectrum and
compact-open functors with their natural reconstruction isomorphisms.
The opposite category records the contravariance; no choice of Boolean
structure or Hausdorff topology is imposed.

## References

- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, §2.2(b), Theorem 2.2.8(2).
- Mathlib, `Order.Category.BddDistLat` and `Topology.Spectral.Basic`, for
  the bounded lattice and spectral-space interfaces.
-/

public section

set_option warningAsError true

open CategoryTheory

namespace SpectralStoneDuality

/-- Stone duality for bounded distributive lattices and spectral spaces;
Fujiwara--Kato, *Foundations of Rigid Geometry I*, Theorem 2.2.8(2). -/
noncomputable def stoneDuality : BddDistLatᵒᵖ ≌ SpectralCat :=
  CategoryTheory.Equivalence.mk spectrumFunctor compactOpenFunctor
    latticeUnitIso spaceUnitIso.symm

end SpectralStoneDuality
