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
-/

public section

set_option warningAsError true

open CategoryTheory

namespace SpectralStoneDuality

/-- Stone duality for bounded distributive lattices and spectral spaces. -/
noncomputable def stoneDuality : BddDistLatᵒᵖ ≌ SpectralCat :=
  CategoryTheory.Equivalence.mk spectrumFunctor compactOpenFunctor
    latticeUnitIso spaceUnitIso.symm

end SpectralStoneDuality
