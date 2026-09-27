/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.TotalComponentNormalization
import GromovWitten.AlgebraicGeometry.Curves.TotalNodeBranches
import GromovWitten.AlgebraicGeometry.Curves.SmoothComponents

/-!
# The two normalized branches of a geometric node

Every node of a prestable curve over an algebraically closed field has exactly two
points on the disjoint union of the actual component normalizations. This constructs
the branch data used to identify the unordered endpoints of the geometric dual graph.
-/

open CategoryTheory Limits AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves
universe u
noncomputable section
variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of K)) [PrestableFamily f]

/-- The full normalized-component fibre over a geometric node has two points. -/
def normalizedComponentNodeFibreEquiv {x : X} (hx : x ∈ nodeSet f) :
    {p : NormalizedComponents.Point (f := f) //
      NormalizedComponents.pointToCurve (f := f) p = x} ≃ Fin 2 := by
  let _ : IsNoetherian X := isNoetherian_of_quasiCompact f
  let e := componentToTotalNormalization (f := f)
  let e' : {p : NormalizedComponents.Point (f := f) //
      NormalizedComponents.pointToCurve (f := f) p = x} ≃
      {q : totalNormalization X // totalNormalizationToScheme X q = x} :=
    e.subtypeEquiv fun p => by
      rw [componentToTotalNormalization_toScheme]
  exact e'.trans (totalNormalization_node_fibre_equiv f hx)

/-- The actual normalized fibre above an edge, with its two branches enumerated. -/
def normalizedEdgeFibreEquiv (e : Edge f) :
    NormalizedBranchData.nodeFibre (f := f) e ≃ Fin 2 :=
  normalizedComponentNodeFibreEquiv f (edgePoint_mem_nodeSet f e)

/-- Canonical branch data constructed from the full normalized fibre over each node. -/
def normalizedBranchData : NormalizedBranchData f where
  point e j := ((normalizedEdgeFibreEquiv f e).symm j).1
  point_to_node e j := ((normalizedEdgeFibreEquiv f e).symm j).2
  point_injective e := by
    intro i j h
    apply (normalizedEdgeFibreEquiv f e).symm.injective
    exact Subtype.ext h
  point_fibre_surjective e p hp := by
    obtain ⟨j, hj⟩ := (normalizedEdgeFibreEquiv f e).symm.surjective ⟨p, hp⟩
    fin_cases j
    · exact Or.inl (congrArg Subtype.val hj).symm
    · exact Or.inr (congrArg Subtype.val hj).symm

/-- The graph endpoint pair is the unordered pair of its actual normalized branch images. -/
theorem endpoint_pair_eq_normalizedBranches (e : Edge f) :
    s(endpoint f e 0, endpoint f e 1) =
      s(((normalizedBranchData f).point e 0).1, ((normalizedBranchData f).point e 1).1) :=
  NormalizedBranchData.endpoint_pair_of_normalized_fibre f e
    (fun j => (normalizedBranchData f).point e j)
    (fun j => (normalizedBranchData f).point_to_node e j)
    (fun p hp => (normalizedBranchData f).point_fibre_surjective e p hp)

end
end GromovWitten.AlgebraicGeometry.Curves
