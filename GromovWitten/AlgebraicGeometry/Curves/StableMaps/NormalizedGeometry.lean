/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableMaps.Geometry
import GromovWitten.AlgebraicGeometry.Curves.NormalizedBranches

/-!
# Normalized geometry of stable-map fibre graphs

The canonical decorated graph reads genera from normalized components. Its edge
endpoints agree with the unordered pair of normalized branches over the node.
-/

open CategoryTheory Limits
open AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves

namespace GromovWitten.AlgebraicGeometry.Curves.StableMaps.MarkedMap
universe u v
noncomputable section
variable {V S : Scheme.{u}} {q : V ⟶ S} {I : Type v}
variable (F : MarkedMap q I) [Fintype I] [DecidableEq I]
  [PrestableFamily F.toBase] {H : LineBundle V} (D : PolarizedDegree F H)
  (K : Type u) [Field K] (y : Spec (.of K) ⟶ S)
  [PrestableFamily (pullback.snd F.toBase y)]

/-- The genus of a decorated-graph vertex is the arithmetic genus of its actual
normalized component. -/
@[simp] theorem normalizedDecoratedGraph_genus_eq (C : Component (F.sourceFiber y)) :
    (normalizedDecoratedGraph F D K y).toDualGraph.genus ((normalizedVertexLift F y) C) =
      arithmeticGenus K (normalizedComponentToBase (pullback.snd F.toBase y) C) := rfl

/-- A separating node has distinct endpoints in the decorated graph. -/
theorem normalizedDecoratedGraph_endpoint_ne_of_multi
    (e : multiEdges (X := F.sourceFiber y)) :
    (normalizedDecoratedGraph F D K y).toDualGraph.endpoint
        ((normalizedEdgeLift F y) (Sum.inr e)) 0 ≠
      (normalizedDecoratedGraph F D K y).toDualGraph.endpoint
        ((normalizedEdgeLift F y) (Sum.inr e)) 1 := by
  change (normalizedVertexLift F y) (endpoint (pullback.snd F.toBase y) (Sum.inr e) 0) ≠
    (normalizedVertexLift F y) (endpoint (pullback.snd F.toBase y) (Sum.inr e) 1)
  exact fun h => endpoint_ne_of_multi (pullback.snd F.toBase y) e
    ((normalizedVertexLift F y).injective h)

/-- The decorated graph endpoints are the images of the constructed normalized branches. -/
theorem normalizedDecoratedGraph_endpoint_pair_eq_normalizedBranches [IsAlgClosed K]
    (e : Edge (f := pullback.snd F.toBase y)) :
    s((normalizedDecoratedGraph F D K y).toDualGraph.endpoint
        ((normalizedEdgeLift F y) e) 0,
      (normalizedDecoratedGraph F D K y).toDualGraph.endpoint
        ((normalizedEdgeLift F y) e) 1) =
      s((normalizedVertexLift F y)
          (((normalizedBranchData (pullback.snd F.toBase y)).point e 0).1),
        (normalizedVertexLift F y)
          (((normalizedBranchData (pullback.snd F.toBase y)).point e 1).1)) :=
  normalizedDecoratedGraph_endpoint_pair_eq F D K y
    (normalizedBranchData (pullback.snd F.toBase y)) e

end
end GromovWitten.AlgebraicGeometry.Curves.StableMaps.MarkedMap
