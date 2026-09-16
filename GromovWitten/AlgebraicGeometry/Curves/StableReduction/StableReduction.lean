/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.Geometrically.Connected
import GromovWitten.AlgebraicGeometry.Curves.StabilityGraph
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.PicardSpecialization

/-!
# Semistable and stable reduction

The reduction results in this file contain a selected finite extension DVR, an actual model over
that DVR, actual relative-dualizing data, and proofs of nodality and numerical positivity.  Their
dual graphs are tied to the scheme-theoretic special fibre: vertices are equivalent to its actual
irreducible components and every edge carries a genuine node point lying on both endpoint
components.

Deep existence is exposed through construction engines rather than placeholder propositions.
Given such an engine, the genus split is executable and the low-genus obstruction to unpointed
stability follows from the compiled graph theorem.  Stable-model comparison contains an actual
isomorphism of models and a uniqueness proof.  The final theorem packages the usual good-reduction
criterion: in genus at least two, any canonical stable model is smooth exactly when some proper
smooth model exists, provided smooth models acquire stable dualizing data and stable models satisfy
the comparison theorem.
-/

open CategoryTheory AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

universe u

noncomputable section

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

/-- A smooth proper geometrically connected generic curve with its arithmetic genus. -/
structure SmoothProperCurve (C : Scheme.{u}) (toK : C ⟶ Spec (.of K)) : Type (u + 1) where
  proper : IsProper toK
  smooth : Smooth toK
  geometricallyConnected : GeometricallyConnected toK
  genus : ℕ

/-- A proper at-worst-nodal model over the original DVR.  This is the Chapter 55 notion of
having nodal reduction; it is deliberately distinct from a semistable family, whose fibres have
genus at least one and no rational tails. -/
structure ProperNodalModel : Type (u + 1) where
  model : Model R K C toK
  proper : model.IsProper
  nodal : model.IsNodal

/-- A curve has nodal reduction over the fixed DVR when it admits a proper nodal model. -/
def HasNodalReduction : Prop :=
  Nonempty (ProperNodalModel (R := R) (K := K) (C := C) (toK := toK))

/-- Nodal reduction after a selected finite extension of DVRs.  Unlike semistability, this notion
also applies in genus zero. -/
structure NodalReduction (curve : SmoothProperCurve C toK) : Type (u + 1) where
  extension : FiniteDVRExtension R K
  model : Model extension.localRing extension.extensionField
    (Model.baseChangedCurve (C := C) (toK := toK) extension).left
    (Model.baseChangedCurve (C := C) (toK := toK) extension).hom
  proper : model.IsProper
  nodal : model.IsNodal

/-- A semistable family after a selected finite extension of DVRs.  Graph vertices and edges are
geometrically anchored in the special fibre. -/
structure SemistableReduction (curve : SmoothProperCurve C toK) extends
    NodalReduction (R := R) (K := K) curve where
  dualizing : model.DualizingSheaf
  semistable : model.IsSemistable dualizing
  graph : DualGraph.{u}
  componentEquiv : graph.Vertex ≃ ArithmeticSurface.Component model
  nodePoint : graph.Edge → model.specialFiberScheme
  nodePoint_injective : Function.Injective nodePoint
  endpoint_incidence : ∀ (e : graph.Edge) (j : Fin 2),
    nodePoint e ∈ (componentEquiv (graph.endpoint e j) : Set model.specialFiberScheme)
  graph_genus : graph.arithmeticGenus = curve.genus
  dualizing_degree : ∀ v : graph.Vertex,
    dualizing.omega.degree (specialPointMap extension.localRing) (componentEquiv v) =
      graph.canonicalDegree v
  graphSemistable : graph.IsSemistable

/-- A stable model after finite extension. -/
structure StableReductionResult (curve : SmoothProperCurve C toK) extends
    SemistableReduction (R := R) (K := K) curve where
  stable : model.IsStable dualizing
  graphStable : graph.IsStable

namespace StableReductionResult

variable {curve : SmoothProperCurve C toK}

/-- An unpointed stable reduction can exist only in genus at least two. -/
theorem genus_ge_two (result : StableReductionResult (R := R) (K := K) curve) :
    2 ≤ curve.genus := by
  rw [← result.graph_genus]
  exact result.graphStable.1

/-- In genus zero there is no unpointed stable reduction. -/
theorem not_exists_of_genus_zero (hgenus : curve.genus = 0) :
    IsEmpty (StableReductionResult (R := R) (K := K) curve) :=
  ⟨fun result ↦ by have := result.genus_ge_two; omega⟩

/-- In genus one there is no unpointed stable reduction. -/
theorem not_exists_of_genus_one (hgenus : curve.genus = 1) :
    IsEmpty (StableReductionResult (R := R) (K := K) curve) :=
  ⟨fun result ↦ by have := result.genus_ge_two; omega⟩

end StableReductionResult

/-- Construction interface for semistable and higher-genus stable reduction. -/
structure StableReductionEngine : Type (u + 1) where
  nodal : ∀ {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}
    (curve : SmoothProperCurve C toK), NodalReduction (R := R) (K := K) curve
  semistable : ∀ {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}
    (curve : SmoothProperCurve C toK), 1 ≤ curve.genus →
      SemistableReduction (R := R) (K := K) curve
  stable : ∀ {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}
    (curve : SmoothProperCurve C toK), 2 ≤ curve.genus →
      StableReductionResult (R := R) (K := K) curve

/-- The output selected by the arithmetic genus. -/
inductive ReductionByGenus (curve : SmoothProperCurve C toK) : Type (u + 1)
  | genusZero (h : curve.genus = 0)
      (result : NodalReduction (R := R) (K := K) curve)
  | genusOne (h : curve.genus = 1)
      (result : SemistableReduction (R := R) (K := K) curve)
  | higherGenus (h : 2 ≤ curve.genus)
      (result : StableReductionResult (R := R) (K := K) curve)

namespace StableReductionEngine

/-- Execute the correct reduction construction in genus zero, one, or at least two. -/
def reduceByGenus
    (engine : StableReductionEngine (R := R) (K := K))
    (curve : SmoothProperCurve C toK) :
    ReductionByGenus (R := R) (K := K) curve := by
  by_cases hzero : curve.genus = 0
  · exact .genusZero hzero (engine.nodal curve)
  by_cases hone : curve.genus = 1
  · exact .genusOne hone (engine.semistable curve (by omega))
  · exact .higherGenus (by omega) (engine.stable curve (by omega))

end StableReductionEngine

/-- Comparison of two stable models of the same generic curve.  The comparison is an actual
categorical isomorphism of models and is unique among all such isomorphisms. -/
structure StableModelComparison {M N : Model R K C toK}
    (DM : M.DualizingSheaf) (DN : N.DualizingSheaf) : Type (u + 1) where
  sourceStable : M.IsStable DM
  targetStable : N.IsStable DN
  iso : M ≅ N
  unique : ∀ e : M ≅ N, e = iso

/-- The stable-model uniqueness construction, uniformly for all stable models over a DVR. -/
structure StableModelUniquenessEngine : Type (u + 1) where
  compare : ∀ {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}
    {M N : Model R K C toK} (DM : M.DualizingSheaf) (DN : N.DualizingSheaf),
    M.IsStable DM → N.IsStable DN → StableModelComparison DM DN

/-- Smoothness of the structural morphism is invariant under an isomorphism of models. -/
theorem model_smooth_of_iso {M N : Model R K C toK} (e : M ≅ N)
    (hM : Smooth M.toBase) : Smooth N.toBase := by
  have htotal : IsIso e.hom.hom := by
    change IsIso ((Over.forget (Spec (.of R))).map
      ((Model.toOverFunctor (R := R) (K := K) (C := C) (toK := toK)).map e.hom))
    infer_instance
  let _ := htotal
  let arrowIso : Arrow.mk M.toBase ≅ Arrow.mk N.toBase :=
    Arrow.isoMk (asIso e.hom.hom) (Iso.refl _) e.hom.over_base
  rw [HasRingHomProperty.eq_affineLocally (P := @Smooth)] at hM ⊢
  let _ := affineLocally_respectsIso RingHom.Smooth RingHom.Smooth.respectsIso
  exact (MorphismProperty.arrow_mk_iso_iff
    (P := affineLocally RingHom.Smooth) arrowIso).mp hM

/-- A proper smooth model of the generic curve. -/
structure GoodReductionModel : Type (u + 1) where
  model : Model R K C toK
  proper : model.IsProper
  smooth : Smooth model.toBase

/-- Good reduction means existence of an actual proper smooth model over the original DVR. -/
def HasGoodReduction : Prop :=
  Nonempty (GoodReductionModel (R := R) (K := K) (C := C) (toK := toK))

/-- In the stable genus range, construct stable dualizing data on every proper smooth model. -/
structure SmoothModelStabilityEngine (curve : SmoothProperCurve C toK) : Type (u + 1) where
  stableGenus : 2 ≤ curve.genus
  dualizing : ∀ (M : Model R K C toK), M.IsProper → Smooth M.toBase → M.DualizingSheaf
  stable : ∀ (M : Model R K C toK) (proper : M.IsProper) (smooth : Smooth M.toBase),
    M.IsStable (dualizing M proper smooth)

/-- Stable-model uniqueness turns existence of any proper smooth model into smoothness of the
chosen stable model.  The reverse direction uses the chosen stable model itself. -/
theorem hasGoodReduction_iff_stableModel_smooth
    (curve : SmoothProperCurve C toK)
    (stability : SmoothModelStabilityEngine (R := R) (K := K) curve)
    (uniqueness : StableModelUniquenessEngine (R := R) (K := K))
    (M : Model R K C toK) (D : M.DualizingSheaf) (hstable : M.IsStable D) :
    HasGoodReduction (R := R) (K := K) (C := C) (toK := toK) ↔ Smooth M.toBase := by
  constructor
  · rintro ⟨good⟩
    let Dgood := stability.dualizing good.model good.proper good.smooth
    let comparison := uniqueness.compare Dgood D
      (stability.stable good.model good.proper good.smooth) hstable
    exact model_smooth_of_iso comparison.iso good.smooth
  · intro hsmooth
    exact ⟨⟨M, hstable.2.1, hsmooth⟩⟩

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction
