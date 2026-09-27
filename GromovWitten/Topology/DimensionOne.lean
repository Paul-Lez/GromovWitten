/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Topology.KrullDimension
import Mathlib.Topology.NoetherianSpace
/-!
# Closed subsets in dimension at most one

Nongeneric points of a T₀ space of Krull dimension at most one are closed.
In a Noetherian sober space, a closed subset consisting of closed points is
finite. In particular, a closed subset of a Noetherian sober curve that avoids
its generic points is finite.
-/

open TopologicalSpace Set Order
namespace GromovWitten.Topology
universe u
variable {X : Type u} [TopologicalSpace X] [T0Space X]
/-- A nongeneric point in dimension at most one is closed. -/
lemma isClosed_singleton_of_not_genericPoints (hd : topologicalKrullDim X ≤ 1)
    (x : X) (hx : x ∉ genericPoints X) : IsClosed ({x} : Set X) := by
  let C : IrreducibleCloseds X := ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hC := (Order.krullDim_le_one_iff.mp hd) C
  have hmin : IsMin C := by
    rcases hC with hmin | hmax
    · exact hmin
    · exfalso
      apply hx
      refine ⟨isIrreducible_singleton.closure, ?_⟩
      intro s hs hCs
      let D : IrreducibleCloseds X := ⟨closure s, hs.closure, isClosed_closure⟩
      have hCD : C ≤ D := hCs.trans subset_closure
      exact subset_closure.trans (hmax hCD)
  apply isClosed_of_closure_subset
  intro y hy
  have hyx : x ⤳ y := specializes_iff_mem_closure.mpr hy
  let D : IrreducibleCloseds X := ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hDC : D ≤ C := hyx.closure_subset
  have hxy : y ⤳ x := specializes_iff_closure_subset.mpr (hmin hDC)
  exact (hxy.antisymm hyx).eq

omit [T0Space X] in
/-- A closed subset consisting of closed points in a Noetherian quasi-sober space is finite. -/
lemma finite_of_isClosed_of_closed_points [NoetherianSpace X] [QuasiSober X]
    (s : Set X) (hs : IsClosed s) (hpts : ∀ x ∈ s, IsClosed ({x} : Set X)) : s.Finite := by
  obtain ⟨S, hS, hclosed, hirred, rfl⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hs
  apply hS.sUnion
  intro t ht
  let x := (hirred t ht).genericPoint
  have hx : IsGenericPoint x t := (hirred t ht).isGenericPoint_genericPoint (hclosed t ht)
  have hxclosed := hpts x (Set.mem_sUnion_of_mem hx.mem ht)
  rw [← hx.def, hxclosed.closure_eq]
  exact Set.finite_singleton x

/-- A closed subset avoiding the generic points of a Noetherian sober curve is finite. -/
lemma finite_of_isClosed_disjoint_genericPoints [NoetherianSpace X] [QuasiSober X]
    (hd : topologicalKrullDim X ≤ 1) (s : Set X) (hs : IsClosed s)
    (hgen : Disjoint s (genericPoints X)) : s.Finite := by
  apply finite_of_isClosed_of_closed_points s hs
  intro x hx
  exact isClosed_singleton_of_not_genericPoints hd x
    (fun h => Set.disjoint_left.mp hgen hx h)
end GromovWitten.Topology
