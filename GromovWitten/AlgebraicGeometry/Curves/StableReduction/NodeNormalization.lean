/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.ModelNormalizationGeneric
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode
import GromovWitten.AlgebraicGeometry.Curves.Normalization

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves

/-!
# Normalization of the standard node in its generic branches

The two branches of the standard node are affine lines. This file records the normalization
calculation needed to use those branches as the actual geometric endpoints of a nodal fibre:
we map the coproduct of the two generic points into the node, normalize that map, and identify
the result with the coproduct of the normalized axes. The source is deliberately the generic
point coproduct, rather than the axes themselves; normalizing the integral axis inclusion would
only restate that the axis is already its own normalization.
-/

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

universe u
noncomputable section

open LocalNode

theorem affineLine_isNormalScheme (K : Type u) [Field K] :
    IsNormalScheme (Spec (.of (Polynomial K))) := by
  let X : Scheme := Spec (.of (Polynomial K))
  let _ : IsIntegral X := by infer_instance
  intro U hne
  let hU : IsAffineOpen U.1 := U.2
  let B := Γ(X, U.1)
  let _ : IsDomain B := inferInstance
  let xu (P : Ideal B) [P.IsMaximal] : U.1 := by
    change Ideal Γ(X, U.1) at P
    let p : Spec Γ(X, U.1) := ⟨P, inferInstance⟩
    refine ⟨hU.fromSpec p, by
      change hU.fromSpec p ∈ (U.1 : Set X)
      rw [← hU.range_fromSpec]
      exact ⟨p, rfl⟩⟩
  let Rₚ (P : Ideal B) [P.IsMaximal] : Type u :=
    (X.presheaf.stalk (xu P).1).carrier
  let _ (P : Ideal B) [P.IsMaximal] : Algebra B (Rₚ P) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (xu P)
  let _ (P : Ideal B) [P.IsMaximal] : IsLocalization.AtPrime (Rₚ P) P := by
    let hloc := hU.isLocalization_stalk (xu P)
    let p : Spec Γ(X, U.1) := ⟨P, inferInstance⟩
    have hfrom : hU.fromSpec (hU.primeIdealOf (xu P)) = hU.fromSpec p := by
      calc
        hU.fromSpec (hU.primeIdealOf (xu P)) = (xu P).1 :=
          hU.fromSpec_primeIdealOf _
        _ = hU.fromSpec p := rfl
    have hp : hU.primeIdealOf (xu P) = p :=
      hU.fromSpec.isOpenEmbedding.injective hfrom
    simpa only [Rₚ, hp] using hloc
  refine IsIntegrallyClosed.of_isLocalization_maximal (Rₚ := Rₚ) (fun P _ => ?_)
  change Ideal Γ(X, U.1) at P
  let p : Spec (Γ(X, U.1)) := ⟨P, inferInstance⟩
  let x : U.1 := xu P
  let _ : Algebra B (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf x
  let htop : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  let xtop : (⊤ : X.Opens) := ⟨x.1, Set.mem_univ _⟩
  let q := htop.primeIdealOf xtop
  let _ : Algebra (Γ(X, (⊤ : X.Opens))) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf xtop
  let _ : IsLocalization.AtPrime (X.presheaf.stalk x) q.asIdeal :=
    htop.isLocalization_stalk xtop
  have htopIC : IsIntegrallyClosed (Γ(X, (⊤ : X.Opens))) := by
    exact IsIntegrallyClosed.of_equiv
      (h := (inferInstance : IsIntegrallyClosed (Polynomial K)))
      (Scheme.ΓSpecIso (.of (Polynomial K))).symm.commRingCatIsoToRingEquiv
  let _ : IsIntegrallyClosed (Γ(X, (⊤ : X.Opens))) := htopIC
  change IsIntegrallyClosed (X.presheaf.stalk x)
  exact isIntegrallyClosed_of_isLocalization (X.presheaf.stalk x)
    q.asIdeal.primeCompl q.asIdeal.primeCompl_le_nonZeroDivisors

abbrev branchAxis (K : Type u) [Field K] : Scheme := Spec (.of (Polynomial K))
abbrev branchNode (K : Type u) [Field K] : Scheme :=
  Spec (.of (LocalNode.Ring K 0 1))

abbrev xBranch (K : Type u) [Field K] : branchAxis K ⟶ branchNode K :=
  LocalNode.xBranchSpec K 1 one_ne_zero

abbrev yBranch (K : Type u) [Field K] : branchAxis K ⟶ branchNode K :=
  LocalNode.yBranchSpec K 1 one_ne_zero

abbrev branchGeneric (K : Type u) [Field K] : Scheme :=
  Spec (.of (branchAxis K).functionField)

abbrev xGenericMap (K : Type u) [Field K] : branchGeneric K ⟶ branchNode K :=
  Normalization.genericPointMap (branchAxis K) ≫ xBranch K

abbrev yGenericMap (K : Type u) [Field K] : branchGeneric K ⟶ branchNode K :=
  Normalization.genericPointMap (branchAxis K) ≫ yBranch K

def standardNodeBranchPairMap (K : Type u) [Field K] :
    (branchGeneric K ⨿ branchGeneric K) ⟶ branchNode K :=
  coprod.desc (xGenericMap K) (yGenericMap K)

def standardNodeAxesMap (K : Type u) [Field K] :
    (branchAxis K ⨿ branchAxis K) ⟶ branchNode K :=
  coprod.desc (xBranch K) (yBranch K)

noncomputable def branchGenericNormalizationIso (K : Type u) [Field K]
    (b : branchAxis K ⟶ branchNode K) [IsIntegralHom b] :
    (Normalization.genericPointMap (branchAxis K) ≫ b).normalization ≅
      branchAxis K := by
  let g := Normalization.genericPointMap (branchAxis K)
  let _ : IsNormalScheme (branchAxis K) := affineLine_isNormalScheme K
  let _ : IsIso (Normalization.toCurve (branchAxis K)) :=
    Normalization.isIso_toCurve_of_isNormalScheme (branchAxis K)
      (affineLine_isNormalScheme K)
  exact
    Scheme.Hom.normalizationIntegralPostcompIso g b ≪≫
      asIso (Normalization.toCurve (branchAxis K))

noncomputable def standardNodeNormalizationCoprodIso (K : Type u) [Field K] :
    (coprod.inl ≫ standardNodeBranchPairMap K).normalization ⨿
        (coprod.inr ≫ standardNodeBranchPairMap K).normalization ≅
      (standardNodeBranchPairMap K).normalization := by
  exact Scheme.Hom.normalizationCoprodIso (standardNodeBranchPairMap K)
    (coprodIsCoprod (branchGeneric K) (branchGeneric K))

theorem standardNodeNormalizationCoprodIso_hom_fromNormalization_inl
    (K : Type u) [Field K] :
    coprod.inl ≫ (standardNodeNormalizationCoprodIso K).hom ≫
        (standardNodeBranchPairMap K).fromNormalization =
      (coprod.inl ≫ standardNodeBranchPairMap K).fromNormalization := by
  exact Scheme.Hom.inl_normalizationCoprodIso_hom_fromNormalization
    (standardNodeBranchPairMap K)
    (coprodIsCoprod (branchGeneric K) (branchGeneric K))

theorem standardNodeNormalizationCoprodIso_hom_fromNormalization_inr
    (K : Type u) [Field K] :
    coprod.inr ≫ (standardNodeNormalizationCoprodIso K).hom ≫
        (standardNodeBranchPairMap K).fromNormalization =
      (coprod.inr ≫ standardNodeBranchPairMap K).fromNormalization := by
  exact Scheme.Hom.inr_normalizationCoprodIso_hom_fromNormalization
    (standardNodeBranchPairMap K)
    (coprodIsCoprod (branchGeneric K) (branchGeneric K))

theorem standardNodeBranchPairMap_inl (K : Type u) [Field K] :
    coprod.inl ≫ standardNodeBranchPairMap K = xGenericMap K := by
  simp [standardNodeBranchPairMap, xGenericMap, coprod.inl_desc]

theorem standardNodeBranchPairMap_inr (K : Type u) [Field K] :
    coprod.inr ≫ standardNodeBranchPairMap K = yGenericMap K := by
  simp [standardNodeBranchPairMap, yGenericMap, coprod.inr_desc]

noncomputable def standardNodeBranchNormalizationIsoInl (K : Type u) [Field K] :
    (coprod.inl ≫ standardNodeBranchPairMap K).normalization ≅ branchAxis K := by
  exact eqToIso (congrArg (fun h : branchGeneric K ⟶ branchNode K => h.normalization)
      (standardNodeBranchPairMap_inl K)) ≪≫
    branchGenericNormalizationIso K (xBranch K)

noncomputable def standardNodeBranchNormalizationIsoInr (K : Type u) [Field K] :
    (coprod.inr ≫ standardNodeBranchPairMap K).normalization ≅ branchAxis K := by
  exact eqToIso (congrArg (fun h : branchGeneric K ⟶ branchNode K => h.normalization)
      (standardNodeBranchPairMap_inr K)) ≪≫
    branchGenericNormalizationIso K (yBranch K)

noncomputable def standardNodeNormalizationIso (K : Type u) [Field K] :
    (branchAxis K ⨿ branchAxis K) ≅
      (standardNodeBranchPairMap K).normalization := by
  let f := standardNodeBranchPairMap K
  let b₁ := standardNodeBranchNormalizationIsoInl K
  let b₂ := standardNodeBranchNormalizationIsoInr K
  let c := standardNodeNormalizationCoprodIso K
  change (branchAxis K ⨿ branchAxis K) ≅ f.normalization
  exact coprod.mapIso b₁.symm b₂.symm ≪≫ c

end
end GromovWitten.AlgebraicGeometry.Curves.StableReduction
