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

/-!
# Spectral Stone duality

Public entry point for prime-ideal spectra, their contravariant functoriality,
reconstruction from compact opens, and `SpectralStoneDuality.stoneDuality`.
It also exports cofiltered spectral-limit and arbitrary-subspace compact-open APIs.
Compact-open cylinders of specified or chosen limits have an `Opens.IsBasis` API.
The separately built `Examples.SpectralStoneDuality` module demonstrates this import.
-/
