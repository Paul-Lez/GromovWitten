/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.TotalNormalization
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.NodeNormalizationFibre
import GromovWitten.AlgebraicGeometry.Curves.ComponentGenericResidue
/-!
# The total normalization of a standard node

The two axis generic points exhaust the generic points of the node. Their residue fields
identify the explicit generic-branch coproduct with the canonical generic-point coproduct.
Consequently the explicit node normalization computes its total normalization.
-/

universe u
open CategoryTheory Limits AlgebraicGeometry Topology

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction
open LocalNode
noncomputable section
variable (K : Type u) [Field K]

lemma branch_generic_closure (b : branchAxis K ⟶ branchNode K) [IsClosedImmersion b] :
    closure {b (genericPoint (branchAxis K))} = Set.range b := by
  calc
    _ = closure (b '' (Set.univ : Set (branchAxis K))) :=
      ((genericPoint_spec (branchAxis K)).image b.continuous).def
    _ = closure (Set.range b) := by rw [Set.image_univ]
    _ = Set.range b := b.isClosedEmbedding.isClosed_range.closure_eq

def xBranchGenericPoint : GenericPointSet (branchNode K) :=
  ⟨xBranch K (genericPoint (branchAxis K)), by
    rw [branch_generic_closure]
    change Set.range (xBranchSpec K 1 one_ne_zero) ∈
      irreducibleComponents (PrimeSpectrum (LocalNode.Ring K 0 1))
    rw [irreducibleComponents_zero_parameter_eq K 1 one_ne_zero]
    exact Or.inl rfl⟩

def yBranchGenericPoint : GenericPointSet (branchNode K) :=
  ⟨yBranch K (genericPoint (branchAxis K)), by
    rw [branch_generic_closure]
    change Set.range (yBranchSpec K 1 one_ne_zero) ∈
      irreducibleComponents (PrimeSpectrum (LocalNode.Ring K 0 1))
    rw [irreducibleComponents_zero_parameter_eq K 1 one_ne_zero]
    exact Or.inr rfl⟩

lemma xBranchGenericPoint_ne_yBranchGenericPoint :
    xBranchGenericPoint K ≠ yBranchGenericPoint K := by
  intro h
  have he : Set.range (xBranch K) = Set.range (yBranch K) := by
    rw [← branch_generic_closure, ← branch_generic_closure]
    exact congrArg (fun x : GenericPointSet (branchNode K) => closure {x.val}) h
  rw [LocalNode.range_xBranchSpec, LocalNode.range_yBranchSpec] at he
  have hp : (Ideal.span {LocalNode.y K 0 1} : Ideal (LocalNode.Ring K 0 1)).IsPrime := by
    rw [← LocalNode.xBranch_ker K 1 one_ne_zero]
    exact RingHom.ker_isPrime _
  let p : PrimeSpectrum (LocalNode.Ring K 0 1) := ⟨_, hp⟩
  have hm : p ∈ PrimeSpectrum.zeroLocus
      (Ideal.span {LocalNode.y K 0 1} : Ideal (LocalNode.Ring K 0 1)) := by
    intro z hz
    exact hz
  rw [he] at hm
  exact LocalNode.x_not_mem_span_y K 1 one_ne_zero
    (hm (Ideal.subset_span (Set.mem_singleton _)))

lemma node_generic_eq_x_or_y (q : GenericPointSet (branchNode K)) :
    q = xBranchGenericPoint K ∨ q = yBranchGenericPoint K := by
  have hq := q.property
  change closure {q.val} ∈ irreducibleComponents
    (PrimeSpectrum (LocalNode.Ring K 0 1)) at hq
  rw [irreducibleComponents_zero_parameter_eq K 1 one_ne_zero] at hq
  rcases hq with hq | hq
  · left
    apply Subtype.ext
    apply eq_of_specializes_generic (xBranchGenericPoint K).property
    apply specializes_iff_mem_closure.mpr
    change xBranch K (genericPoint (branchAxis K)) ∈ closure {q.val}
    rw [hq]
    exact Set.mem_range_self _
  · right
    apply Subtype.ext
    apply eq_of_specializes_generic (yBranchGenericPoint K).property
    apply specializes_iff_mem_closure.mpr
    change yBranch K (genericPoint (branchAxis K)) ∈ closure {q.val}
    rw [hq]
    exact Set.mem_range_self _

end
end GromovWitten.AlgebraicGeometry.Curves.StableReduction

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction
open LocalNode
noncomputable section
variable (K : Type u) [Field K]

@[simp] lemma branch_genericPointMap_apply (p : branchGeneric K) :
    Normalization.genericPointMap (branchAxis K) p = genericPoint (branchAxis K) := by
  let _ : Subsingleton (branchGeneric K) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (branchAxis K).functionField))
  have hp : p = IsLocalRing.closedPoint (branchAxis K).functionField := Subsingleton.elim _ _
  rw [hp]
  exact Scheme.fromSpecStalk_closedPoint

def nodeGenericPairToTotal :
    (branchGeneric K ⨿ branchGeneric K) ⟶ genericPointCoproduct (branchNode K) :=
  coprod.desc
    ((genericFunctionFieldResidueSpecIso (xBranch K)).hom ≫
      Sigma.ι (genericPointSpectrum (branchNode K)) (xBranchGenericPoint K))
    ((genericFunctionFieldResidueSpecIso (yBranch K)).hom ≫
      Sigma.ι (genericPointSpectrum (branchNode K)) (yBranchGenericPoint K))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)] lemma nodeGenericPairToTotal_toScheme :
    nodeGenericPairToTotal K ≫ genericPointsToScheme (branchNode K) =
      standardNodeBranchPairMap K := by
  apply coprod.hom_ext <;>
    simp only [nodeGenericPairToTotal, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
      standardNodeBranchPairMap, coprod.inl_desc, coprod.inr_desc,
      genericPointsToScheme]
  all_goals rw [Category.assoc, Sigma.ι_desc]
  · exact genericFunctionFieldResidueSpecIso_commutes (xBranch K)
  · exact genericFunctionFieldResidueSpecIso_commutes (yBranch K)

lemma nodeGenericPairToTotal_bijective : Function.Bijective (nodeGenericPairToTotal K) := by
  let A := branchGeneric K
  let _ : Subsingleton A :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (branchAxis K).functionField))
  have hx (p : A) :
      genericPointCoproductEquiv (branchNode K)
          (nodeGenericPairToTotal K ((coprod.inl : A ⟶ A ⨿ A) p)) = xBranchGenericPoint K := by
    apply Subtype.ext
    rw [genericPointCoproductEquiv_val, ← Scheme.Hom.comp_apply,
      nodeGenericPairToTotal_toScheme]
    rw [← Scheme.Hom.comp_apply, standardNodeBranchPairMap_inl]
    change xBranch K (Normalization.genericPointMap (branchAxis K) p) =
      xBranch K (genericPoint (branchAxis K))
    rw [branch_genericPointMap_apply]
  have hy (p : A) :
      genericPointCoproductEquiv (branchNode K)
          (nodeGenericPairToTotal K ((coprod.inr : A ⟶ A ⨿ A) p)) = yBranchGenericPoint K := by
    apply Subtype.ext
    rw [genericPointCoproductEquiv_val, ← Scheme.Hom.comp_apply,
      nodeGenericPairToTotal_toScheme]
    rw [← Scheme.Hom.comp_apply, standardNodeBranchPairMap_inr]
    change yBranch K (Normalization.genericPointMap (branchAxis K) p) =
      yBranch K (genericPoint (branchAxis K))
    rw [branch_genericPointMap_apply]
  constructor
  · intro p q hpq
    obtain ⟨p, rfl⟩ := (coprodMk A A).surjective p
    obtain ⟨q, rfl⟩ := (coprodMk A A).surjective q
    cases p with
    | inl p =>
      cases q with
      | inl q => exact congrArg (fun p => coprodMk A A (Sum.inl p)) (Subsingleton.elim p q)
      | inr q =>
        have h := congrArg (genericPointCoproductEquiv (branchNode K)) hpq
        rw [coprodMk_inl, coprodMk_inr, hx, hy] at h
        exact (xBranchGenericPoint_ne_yBranchGenericPoint K h).elim
    | inr p =>
      cases q with
      | inl q =>
        have h := congrArg (genericPointCoproductEquiv (branchNode K)) hpq
        rw [coprodMk_inr, coprodMk_inl, hy, hx] at h
        exact (xBranchGenericPoint_ne_yBranchGenericPoint K h.symm).elim
      | inr q => exact congrArg (fun p => coprodMk A A (Sum.inr p)) (Subsingleton.elim p q)
  · intro q
    let p : A := IsLocalRing.closedPoint (branchAxis K).functionField
    rcases node_generic_eq_x_or_y K (genericPointCoproductEquiv (branchNode K) q) with h | h
    · refine ⟨(coprod.inl : A ⟶ A ⨿ A) p, ?_⟩
      apply (genericPointCoproductEquiv (branchNode K)).injective
      exact (hx p).trans h.symm
    · refine ⟨(coprod.inr : A ⟶ A ⨿ A) p, ?_⟩
      apply (genericPointCoproductEquiv (branchNode K)).injective
      exact (hy p).trans h.symm

end
end GromovWitten.AlgebraicGeometry.Curves.StableReduction

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction
open LocalNode
noncomputable section
variable (K : Type u) [Field K]

set_option backward.isDefEq.respectTransparency false in
instance nodeGenericPairToTotal_surjectiveOnStalks :
    SurjectiveOnStalks (nodeGenericPairToTotal K) := by
  apply IsZariskiLocalAtSource.of_openCover
    (P := @SurjectiveOnStalks) (coprodOpenCover.{u, 0} (branchGeneric K) (branchGeneric K))
  intro i
  cases i <;> dsimp [coprodOpenCover] <;>
    simp only [nodeGenericPairToTotal, coprod.inl_desc, coprod.inr_desc] <;>
    infer_instance

instance nodeGenericPairToTotal_isIso : IsIso (nodeGenericPairToTotal K) := by
  let A := branchGeneric K
  let _ : DiscreteTopology (A ⨿ A : Scheme) :=
    (coprodMk A A).discreteTopology_iff.mp inferInstance
  let e := Equiv.ofBijective (nodeGenericPairToTotal K) (nodeGenericPairToTotal_bijective K)
  let _ : IsPreimmersion (nodeGenericPairToTotal K) := {
    isEmbedding := e.toHomeomorphOfDiscrete.isEmbedding
    stalkMap_surjective := (nodeGenericPairToTotal K).stalkMap_surjective }
  let _ : Surjective (nodeGenericPairToTotal K) := ⟨(nodeGenericPairToTotal_bijective K).2⟩
  exact isIso_of_preimmersion_surjective_reduced_discrete _

def standardNodeTotalNormalizationIso :
    (standardNodeBranchPairMap K).normalization ≅ totalNormalization (branchNode K) :=
  (Scheme.Hom.normalizationCongr (nodeGenericPairToTotal_toScheme K)).symm ≪≫
    Scheme.Hom.normalizationPrecompIso (genericPointsToScheme (branchNode K))
      (asIso (nodeGenericPairToTotal K))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)] lemma standardNodeTotalNormalizationIso_hom_toScheme :
    (standardNodeTotalNormalizationIso K).hom ≫ totalNormalizationToScheme (branchNode K) =
      (standardNodeBranchPairMap K).fromNormalization := by
  dsimp only [standardNodeTotalNormalizationIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, Scheme.Hom.normalizationPrecompIso_hom_fromNormalization]
  apply (Iso.inv_comp_eq _).mpr
  exact (Scheme.Hom.normalizationCongr_hom_fromNormalization
    (nodeGenericPairToTotal_toScheme K)).symm

end
end GromovWitten.AlgebraicGeometry.Curves.StableReduction

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction
open LocalNode
noncomputable section
variable (K : Type u) [Field K]

def standardNodeTotalNormalizationFibreEquiv (r : Spec (.of K)) :
    {p : totalNormalization (branchNode K) //
      totalNormalizationToScheme (branchNode K) p = nodeOriginSpec K 1 one_ne_zero r} ≃
      Fin 2 :=
  (Scheme.fibreEquivOfIso (standardNodeTotalNormalizationIso K)
    (standardNodeBranchPairMap K).fromNormalization (totalNormalizationToScheme (branchNode K))
    (standardNodeTotalNormalizationIso_hom_toScheme K) _).symm.trans
      (standardNodeNormalizationFibreEquiv K r)

end
end GromovWitten.AlgebraicGeometry.Curves.StableReduction
