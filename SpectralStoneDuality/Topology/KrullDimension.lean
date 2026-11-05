/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.Topology.Soberification
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Specialization

/-!
# Krull dimension and the specialization order

For a quasi-sober space `X`, its topological Krull dimension agrees with the
order-theoretic Krull dimension of its points in `Specialization X`. This type
synonym retains the original points, with `Specialization.toEquiv a ≤
Specialization.toEquiv b` exactly when `b` specializes to `a` in the given topology.
No topology on the type synonym is needed.

The soberification unit `TopologicalSpace.IrreducibleCloseds.unit X` sends `x` to
`closure {x}` in the original space. Its codomain carries the inclusion order on
irreducible closed subsets, in the same direction as the specialization order.
No separation axiom or finiteness assumption is imposed on `X`.

Both dimensions take values in `WithBot ℕ∞`: the empty space has dimension `⊥`,
and unbounded finite chain lengths give dimension `⊤`, without requiring a chain
attaining the supremum.

## References

- Mathlib contributors, `Topology.KrullDimension` and `Order.KrullDimension`, for
  the dimensions and their strict-monotone and strictly reflecting surjective transports;
  `Topology.Specialization`, for the original-point specialization preorder;
  `Topology.Sober`, for generic points of irreducible closed sets in quasi-sober spaces.
- Formal Frontier Agents, `SpectralStoneDuality.Topology.Soberification`, for the
  soberification unit and its singleton-closure formula.
-/

@[expose] public section

universe u

/-- The topological Krull dimension of a quasi-sober space is the Krull dimension
of its original points with the specialization preorder. -/
theorem topologicalKrullDim_eq_krullDim_specialization (X : Type u)
    [TopologicalSpace X] [QuasiSober X] :
    topologicalKrullDim X = Order.krullDim (Specialization X) := by
  let f : Specialization X → TopologicalSpace.IrreducibleCloseds X :=
    TopologicalSpace.IrreducibleCloseds.unit X ∘ Specialization.ofEquiv
  have hle (a b : Specialization X) : f a ≤ f b ↔ a ≤ b :=
    (TopologicalSpace.IrreducibleCloseds.unit_le_unit_iff
      (Specialization.ofEquiv a) (Specialization.ofEquiv b)).trans
        Specialization.ofEquiv_specializes_ofEquiv
  have hlt (a b : Specialization X) : f a < f b ↔ a < b :=
    lt_iff_lt_of_le_iff_le' (hle b a) (hle a b)
  have hsurj : Function.Surjective f :=
    (TopologicalSpace.IrreducibleCloseds.unit_surjective X).comp
      Specialization.ofEquiv.surjective
  exact le_antisymm
    (Order.krullDim_le_of_strictComono_and_surj f (fun {a b} h => (hlt a b).mp h) hsurj)
    (Order.krullDim_le_of_strictMono f (fun {a b} h => (hlt a b).mpr h))
