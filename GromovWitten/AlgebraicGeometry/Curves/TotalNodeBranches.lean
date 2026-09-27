/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.NodeTotalNormalization

/-!
# Normalization fibres at nodes of a prestable curve

An affine étale node chart compares the global total-normalization fibre with the standard
node fibre. Closed points over an algebraically closed field have the same residue field,
so these comparisons identify the complete fibre with `Fin 2`.
-/

open CategoryTheory Limits AlgebraicGeometry Topology
namespace GromovWitten.AlgebraicGeometry.Curves

universe u
noncomputable section

variable {K : Type u} [Field K]

lemma closed_singleton_of_closed_discrete {T : Type u} [TopologicalSpace T]
    {s : Set T} (hs : IsClosed s) (hd : IsDiscrete s) {x : T} (hx : x ∈ s) :
    IsClosed ({x} : Set T) := by
  have : DiscreteTopology s := isDiscrete_iff_discreteTopology.mp hd
  simpa using hs.isClosedEmbedding_subtypeVal.isClosedMap
    ({⟨x, hx⟩} : Set s) (isClosed_discrete _)

lemma NodeChartAt.exists_affine {X : Scheme.{u}} {f : X ⟶ Spec (.of K)}
    {x : X} (c : NodeChartAt f x) :
    ∃ d : NodeChartAt f x, IsAffine d.source := by
  obtain ⟨i, q, hq⟩ := c.source.affineCover.exists_eq c.point
  let a := c.source.affineCover.f i
  let _ : Etale c.toCurve := c.etale_toCurve
  let _ : Etale c.toNode := c.etale_toNode
  refine ⟨{
    source := c.source.affineCover.X i
    point := q
    toCurve := a ≫ c.toCurve
    toNode := a ≫ c.toNode
    etale_toCurve := by dsimp [a]; infer_instance
    etale_toNode := by dsimp [a]; infer_instance
    mapsToPoint := by simp [a, hq, c.mapsToPoint]
    overBase := by simp only [Category.assoc, c.overBase]
    mapsToOrigin := by simpa [a, hq] using c.mapsToOrigin
  }, ?_⟩
  infer_instance

lemma NodeChartAt.isNoetherian_source {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {x : X} (c : NodeChartAt f x) [IsAffine c.source]
    [LocallyOfFiniteType f] : IsNoetherian c.source := by
  let _ : Etale c.toCurve := c.etale_toCurve
  let _ : LocallyOfFiniteType (c.toCurve ≫ f) := inferInstance
  let _ : IsLocallyNoetherian c.source :=
    LocallyOfFiniteType.isLocallyNoetherian (c.toCurve ≫ f)
  exact ⟨⟩

lemma standardNodeOrigin_point (r : Spec (.of K)) :
    StableReduction.LocalNode.nodeOriginSpec K 1 one_ne_zero r = standardNodeOrigin K := by
  let _ : r.asIdeal.IsPrime := r.isPrime
  apply PrimeSpectrum.ext
  change Ideal.comap (StableReduction.LocalNode.nodeOrigin K 1 one_ne_zero).toRingHom r.asIdeal =
    RingHom.ker (StableReduction.LocalNode.nodeOrigin K 1 one_ne_zero).toRingHom
  rw [show r.asIdeal = ⊥ by exact Ideal.eq_bot_of_prime _]
  rfl

lemma isClosed_standardNodeOrigin :
    IsClosed ({standardNodeOrigin K} : Set (StableReduction.branchNode K)) := by
  have hrange :=
    (StableReduction.LocalNode.nodeOriginSpec K 1 one_ne_zero).isClosedEmbedding.isClosed_range
  rw [show Set.range (StableReduction.LocalNode.nodeOriginSpec K 1 one_ne_zero) =
      ({standardNodeOrigin K} : Set (StableReduction.branchNode K)) by
    ext p
    constructor
    · rintro ⟨r, rfl⟩
      simpa only [standardNodeOrigin_point r] using
        (Set.mem_singleton (standardNodeOrigin K))
    · intro hp
      rw [Set.mem_singleton_iff.mp hp]
      exact ⟨(default : Spec (.of K)), standardNodeOrigin_point _⟩] at hrange
  exact hrange

/-- The total normalization has exactly the two standard branches over every geometric node. -/
noncomputable def totalNormalization_node_fibre_equiv
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [PrestableFamily f]
    [IsAlgClosed K] {x : X} (hx : x ∈ nodeSet f) :
    {p : @totalNormalization X (isNoetherian_of_quasiCompact f) //
      @totalNormalizationToScheme X (isNoetherian_of_quasiCompact f) p = x} ≃ Fin 2 := by
  letI : IsNoetherian X := isNoetherian_of_quasiCompact f
  let c₀ : NodeChartAt f x := Classical.choice (nodeChart_nonempty_of_mem_nodeSet f hx)
  let c : NodeChartAt f x := Classical.choose (c₀.exists_affine)
  have hcaff : IsAffine c.source := Classical.choose_spec (c₀.exists_affine)
  letI : IsAffine c.source := hcaff
  letI : IsNoetherian c.source := c.isNoetherian_source
  let hnod : IsNodalCurveOverField f := isNodalCurveOverField_of_atWorstNodal f
  have hxclosed : IsClosed ({x} : Set X) := by
    exact closed_singleton_of_closed_discrete (isClosed_nodeSet f)
      (nodeSet_isDiscrete f hnod) hx
  have hcclosed : IsClosed ({c.point} : Set c.source) := by
    let _ : Etale c.toCurve := c.etale_toCurve
    let _ := locallyQuasiFinite_of_etale c.toCurve
    apply closed_singleton_of_closed_discrete (hxclosed.preimage c.toCurve.continuous)
      (c.toCurve.isDiscrete_preimage_singleton x)
    exact c.mapsToPoint
  have hcurve : c.toCurve c.point = x := c.mapsToPoint
  have hnode : c.toNode c.point = standardNodeOrigin K :=
    nodeChart_toNode_point f hx c
  letI : Etale c.toCurve := c.etale_toCurve
  letI : Etale c.toNode := c.etale_toNode
  letI : LocallyOfFiniteType (c.toCurve ≫ f) := by infer_instance
  have hcurveclosed : IsClosed ({c.toCurve c.point} : Set X) := by
    simpa only [hcurve] using hxclosed
  have hnodeclosed : IsClosed ({c.toNode c.point} : Set (StableReduction.branchNode K)) := by
    simpa only [hnode] using (isClosed_standardNodeOrigin (K := K))
  letI : LocallyOfFiniteType (c.toNode ≫ standardNodeToSpec K) := by
    rw [← c.overBase]
    infer_instance
  letI : IsIso (c.toCurve.residueFieldMap c.point) :=
    Scheme.Hom.residueFieldMap_isIso_of_closed c.toCurve f c.point hcclosed hcurveclosed
  letI : IsIso (c.toNode.residueFieldMap c.point) :=
    Scheme.Hom.residueFieldMap_isIso_of_closed c.toNode (standardNodeToSpec K)
      c.point hcclosed hnodeclosed
  let r : Spec (.of K) := default
  let ecurve := totalNormalizationEtaleFibreEquiv c.toCurve c.point
  let enode := totalNormalizationEtaleFibreEquiv c.toNode c.point
  let hcurveSet :
      {q : totalNormalization X // totalNormalizationToScheme X q = c.toCurve c.point} =
        {q : totalNormalization X // totalNormalizationToScheme X q = x} := by
    rw [hcurve]
  let hnodePoint :
      StableReduction.LocalNode.nodeOriginSpec K 1 one_ne_zero r = c.toNode c.point := by
    rw [standardNodeOrigin_point, hnode]
  let hnodeSet :
      {q : totalNormalization (StableReduction.branchNode K) //
          totalNormalizationToScheme (StableReduction.branchNode K) q = c.toNode c.point} =
        {q : totalNormalization (StableReduction.branchNode K) //
          totalNormalizationToScheme (StableReduction.branchNode K) q =
            StableReduction.LocalNode.nodeOriginSpec K 1 one_ne_zero r} := by
    rw [hnodePoint]
  exact (Equiv.cast hcurveSet).symm.trans
    (ecurve.symm.trans (enode.trans
      ((Equiv.cast hnodeSet).trans
        (StableReduction.standardNodeTotalNormalizationFibreEquiv K r))))

end
end GromovWitten.AlgebraicGeometry.Curves
