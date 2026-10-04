/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.PrimeSpectrum
public import SpectralStoneDuality.Functoriality
public import SpectralStoneDuality.Category
public import SpectralStoneDuality.Reconstruction
public import SpectralStoneDuality.Equivalence
public import SpectralStoneDuality.Limits
public import SpectralStoneDuality.CompactOpenBasis
public import SpectralStoneDuality.Subspace
public import SpectralStoneDuality.Topology.LocallyClosed
public import SpectralStoneDuality.LimitCylinderDescent
public import SpectralStoneDuality.FiniteCylinderDescent
public import SpectralStoneDuality.Topology.Soberification
public import SpectralStoneDuality.Topology.Category.Soberification
public import SpectralStoneDuality.Topology.Cofinite
public import SpectralStoneDuality.Topology.Finite
public import SpectralStoneDuality.FiniteCoordinates
public import SpectralStoneDuality.FiniteCoordinates.Limits
public import SpectralStoneDuality.Topology.NhdsKer
public import SpectralStoneDuality.CategoryTheory.Lattice.Extensive
public import SpectralStoneDuality.CategoryTheory.Lattice.Preserves

/-!
# Spectral Stone duality

Public entry point for prime-ideal spectra, their contravariant functoriality,
reconstruction from compact opens, and `SpectralStoneDuality.stoneDuality`.
It also exports cofiltered spectral-limit and arbitrary-subspace compact-open APIs.
Compact-open cylinders of specified or chosen limits have an `Opens.IsBasis` API.
Their compact-open/open containments descend to a stage over the same index.
Finite labelled compact-open covers descend coherently to a cover of an entire stage.
The lattice chapter describes universal finite coproducts in thin distributive-lattice
categories and a related extensive-topology covering family. It also identifies
bounded lattice homomorphisms with functors of the underlying order categories
preserving finite limits and finite colimits, without distributivity.
The `Topology.Soberification` and `Topology.Category.Soberification` leaves give
the soberification of any topological space and its adjunction with the inclusion
of `T₀` quasi-sober spaces; these are independent of spectrality. The separately
built `Examples.SpectralStoneDuality` and `SpectralStoneDualityExamples.Soberification`
modules demonstrate these imports.
The `Topology.Cofinite` leaf characterizes quasi-sobriety of a cofinite space by
finiteness of its underlying type, including the empty case.
The `Topology.Finite` leaf proves that every finite irreducible set contains a generic
point of its closure; every finite topological space is therefore quasi-sober, without
a separation assumption.
The `FiniteCoordinates` leaf reconstructs a spectral space from compatible realized
Sierpiński membership patterns at its finite families of compact opens.
The `Topology.NhdsKer` leaf identifies the unique closed point in the subspace
of generizations of a point in any `T₀` space.
The `Topology.LocallyClosed` leaf gives retrocompactness and prespectral,
compact, quasi-separated subspaces for compact locally closed subsets of
prespectral quasi-separated spaces, without ambient compactness.
-/
