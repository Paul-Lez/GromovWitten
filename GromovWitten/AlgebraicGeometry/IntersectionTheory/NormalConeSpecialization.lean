/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Cones.DeformationSpecialization
import GromovWitten.AlgebraicGeometry.Cones.NormalConeDimension
import GromovWitten.AlgebraicGeometry.Curves.SmoothPureDimension
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChowGroup
import GromovWitten.AlgebraicGeometry.IntersectionTheory.FiniteTypeDimension
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChernClasses

/-!
# Cycle specialization to an affine normal cone

For an affine finite-type scheme `Spec R` over a field and a closed subscheme cut out by `I`,
this file constructs the specialization of an integral cycle `Spec (R ⧸ P)` as the actual
fundamental cycle of the affine normal cone of `I.map (Ideal.Quotient.mk P)`, pushed forward by
the closed immersion supplied by the quotient deformation.  The associated-graded cone is kept
with its generic-length multiplicities; no component projection is used.

The resulting operation is named `cycleSpecialization`: rational-equivalence descent is not
claimed here.
-/

open CategoryTheory Topology TopologicalSpace AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

universe u

noncomputable section

namespace NormalConeSpecialization

abbrev affineScheme (R : Type u) [CommRing R] := Spec (CommRingCat.of R)

/-! ## Finite-type affine structures -/

noncomputable def structureMap (k R : Type u) [Field k] [CommRing R] [Algebra k R] :
    affineScheme R ⟶ affineScheme k :=
  Spec.map (CommRingCat.ofHom (algebraMap k R))

instance locallyOfFiniteType_structureMap
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] :
    LocallyOfFiniteType (structureMap k R) := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

noncomputable def dimension (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] : DimensionFunction (affineScheme R) :=
  FiniteTypeDimension.dimensionFunction (structureMap k R)

theorem quotient_finiteType
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (P : Ideal R) : Algebra.FiniteType k (R ⧸ P) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k P)
    (Ideal.Quotient.mkₐ_surjective k P)

theorem quotient_isNoetherianRing
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (P : Ideal R) : IsNoetherianRing (R ⧸ P) :=
  Algebra.FiniteType.isNoetherianRing k _

noncomputable instance associatedGraded_finiteType
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    Algebra.FiniteType R (AffineNormalCone.associatedGradedRing R I) := by
  exact Algebra.FiniteType.of_surjective
    (Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R (reesAlgebra I)) I))
    (Ideal.Quotient.mkₐ_surjective R _)

instance associatedGraded_isNoetherianRing
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    IsNoetherianRing (AffineNormalCone.associatedGradedRing R I) :=
  Algebra.FiniteType.isNoetherianRing R _

theorem associatedGraded_finiteType_over_field
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] [IsNoetherianRing R] (I : Ideal R) :
    Algebra.FiniteType k (AffineNormalCone.associatedGradedRing R I) := by
  exact Algebra.FiniteType.trans (S := R) inferInstance inferInstance

instance associatedGraded_locallyNoetherian
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    IsLocallyNoetherian (AffineNormalCone.scheme R I) := by
  apply isLocallyNoetherian_Spec.mpr
  infer_instance

/-! ## Canonical dimensions and purity -/

noncomputable def normalConeDimension
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) :
    DimensionFunction (AffineNormalCone.scheme R I) := by
  let _ : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let _ : Algebra.FiniteType k (AffineNormalCone.associatedGradedRing R I) :=
    associatedGraded_finiteType_over_field k R I
  exact dimension k (AffineNormalCone.associatedGradedRing R I)

theorem ringKrullDim_quotient_eq_natDim
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (P : Ideal R) [P.IsPrime] :
    ringKrullDim (R ⧸ P) =
      (Int.toNat (dimension k R ⟨P, inferInstance⟩) : ℕ∞) := by
  let x : PrimeSpectrum R := ⟨P, inferInstance⟩
  have hco := GromovWitten.Algebra.PrimeSpectrum.coheight_eq_ringKrullDim_quotient x
  have hdim := VectorBundle.coheight_eq_dimension R (dimension k R) x
  calc
    ringKrullDim (R ⧸ P) = ringKrullDim (R ⧸ x.asIdeal) := by rfl
    _ = (Order.coheight x : ℕ∞) := hco.symm
    _ = (Int.toNat (dimension k R x) : ℕ∞) := by exact_mod_cast hdim
    _ = (Int.toNat (dimension k R ⟨P, inferInstance⟩) : ℕ∞) := by rfl

theorem pure_normalCone
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) [IsDomain R]
    (hI : I ≠ ⊤) :
    Curves.PureTopologicalDimension
      (Int.toNat (dimension k R (genericPoint (affineScheme R))))
      (AffineNormalCone.scheme R I) := by
  let n := Int.toNat (dimension k R (genericPoint (affineScheme R)))
  let _ : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have hn : ringKrullDim R = (n : ℕ∞) := by
    have hbot := ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)
    have hquot := ringKrullDim_quotient_eq_natDim k R (P := (⊥ : Ideal R))
    have hgen : (genericPoint (affineScheme R) : PrimeSpectrum R) =
        (⊥ : PrimeSpectrum R) := by
      exact genericPoint_eq_bot_of_affine (CommRingCat.of R)
    calc
      ringKrullDim R = ringKrullDim (R ⧸ (⊥ : Ideal R)) := hbot.symm
      _ = (Int.toNat (dimension k R
          (⊥ : PrimeSpectrum R)) : ℕ∞) := hquot
      _ = (n : ℕ∞) := by rw [← hgen]
  exact GromovWitten.Algebra.pureTopologicalDimension_normalCone' k I hI n hn

/-! ## Integral generators -/

noncomputable def quotientConeDimension
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) (P : Ideal R) :
    DimensionFunction
      (AffineNormalCone.scheme (R ⧸ P) (Ideal.map (Ideal.Quotient.mk P) I)) := by
  let _ : IsNoetherianRing (R ⧸ P) := quotient_isNoetherianRing k R P
  let _ : Algebra.FiniteType k (AffineNormalCone.associatedGradedRing
      (R ⧸ P) (Ideal.map (Ideal.Quotient.mk P) I)) :=
    associatedGraded_finiteType_over_field k (R ⧸ P)
      (Ideal.map (Ideal.Quotient.mk P) I)
  exact normalConeDimension k (R ⧸ P) (Ideal.map (Ideal.Quotient.mk P) I)

private theorem fundamentalCycle_eq_zero_of_subsingleton
    {A : Type u} [CommRing A] (hA : Subsingleton A) :
    (Spec (CommRingCat.of A)).fundamentalCycle = 0 := by
  let hEmpty : IsEmpty (Spec (CommRingCat.of A)) := ⟨by
    intro x
    have htop : (x : PrimeSpectrum A).asIdeal = ⊤ := by
      apply top_unique
      intro a ha
      have ha0 : a = 0 := @Subsingleton.elim A hA a 0
      simp [ha0]
    exact Ideal.IsPrime.ne_top (x : PrimeSpectrum A).isPrime htop
  ⟩
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  exact (hEmpty.false x).elim

noncomputable def integralNormalConeCycle
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I P : Ideal R) [P.IsPrime] :
    AlgebraicCycle (AffineNormalCone.scheme R I) ℚ := by
  let _ : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let _ : IsNoetherianRing (R ⧸ P) := quotient_isNoetherianRing k R P
  let _ : Algebra.FiniteType k (R ⧸ P) := quotient_finiteType k R P
  let J : Ideal (R ⧸ P) := Ideal.map (Ideal.Quotient.mk P) I
  let _ : Algebra.FiniteType k (AffineNormalCone.associatedGradedRing (R ⧸ P) J) :=
    associatedGraded_finiteType_over_field k (R ⧸ P) J
  let source := AffineNormalCone.scheme (R ⧸ P) J
  let target := AffineNormalCone.scheme R I
  let f : source ⟶ target := AffineDeformationSpace.quotientNormalConeMap R I P
  exact AlgebraicCycle.map f
    (quotientConeDimension k R I P) (normalConeDimension k R I)
    source.fundamentalCycle

theorem integralNormalConeCycle_imageIdeal_top
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I P : Ideal R) [P.IsPrime]
    (h : Ideal.map (Ideal.Quotient.mk P) I = ⊤) :
    integralNormalConeCycle k R I P = 0 := by
  let _ : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let _ : IsNoetherianRing (R ⧸ P) := quotient_isNoetherianRing k R P
  let J : Ideal (R ⧸ P) := Ideal.map (Ideal.Quotient.mk P) I
  have hJ : J = ⊤ := h
  have hsub : Subsingleton (AffineNormalCone.associatedGradedRing (R ⧸ P) J) := by
    change Subsingleton ((reesAlgebra J) ⧸
      Ideal.map (algebraMap (R ⧸ P) (reesAlgebra J)) J)
    rw [hJ, Ideal.map_top]
    infer_instance
  have hzero : (AffineNormalCone.scheme (R ⧸ P) J).fundamentalCycle = 0 := by
    exact fundamentalCycle_eq_zero_of_subsingleton hsub
  unfold integralNormalConeCycle
  change AlgebraicCycle.map
      (AffineDeformationSpace.quotientNormalConeMap R I P)
      (quotientConeDimension k R I P) (normalConeDimension k R I)
      (AffineNormalCone.scheme (R ⧸ P) J).fundamentalCycle = 0
  rw [hzero]
  exact GromovWitten.AlgebraicGeometry.IntersectionTheory.AlgebraicCycle.map_zero
    (AffineDeformationSpace.quotientNormalConeMap R I P)
    (quotientConeDimension k R I P) (normalConeDimension k R I)

attribute [local instance] specializationOrder in
theorem quotientConeDimension_of_isMax
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I P : Ideal R) [P.IsPrime]
    (hJ : Ideal.map (Ideal.Quotient.mk P) I ≠ ⊤)
    (x : AffineNormalCone.scheme (R ⧸ P) (Ideal.map (Ideal.Quotient.mk P) I))
    (hx : IsMax x) :
    quotientConeDimension k R I P x = dimension k R ⟨P, inferInstance⟩ := by
  let _ : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let _ : Algebra.FiniteType k (R ⧸ P) := quotient_finiteType k R P
  let _ : IsNoetherianRing (R ⧸ P) := quotient_isNoetherianRing k R P
  let n := Int.toNat (dimension k R ⟨P, inferInstance⟩)
  have hn : ringKrullDim (R ⧸ P) = (n : ℕ∞) := by
    simpa [n] using (ringKrullDim_quotient_eq_natDim k R P)
  have hpure := GromovWitten.Algebra.pureTopologicalDimension_normalCone'
    k (Ideal.map (Ideal.Quotient.mk P) I) hJ n hn
  have hcomp : closure ({x} : Set _) ∈ irreducibleComponents
      (AffineNormalCone.scheme (R ⧸ P)
        (Ideal.map (Ideal.Quotient.mk P) I)) := by
    rw [Curves.closure_singleton_mem_irreducibleComponents_iff]
    intro y hy
    change x ≤ y at hy
    exact le_antisymm (hx hy) hy
  have hp := hpure _ hcomp
  have ht := Curves.topologicalKrullDim_closure_singleton x
  have hcast : ((Order.height x : ℕ∞) : WithBot ℕ∞) =
      ((n : ℕ∞) : WithBot ℕ∞) := by
    calc
      ((Order.height x : ℕ∞) : WithBot ℕ∞) =
          topologicalKrullDim (closure ({x} : Set _)) := ht.symm
      _ = ((n : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hp
  have hheight : (Order.height x : ℕ∞) = n := by
    exact_mod_cast hcast
  have hnat : Int.toNat (quotientConeDimension k R I P x) = n := by
    apply ENat.natCast_inj.mp
    exact (quotientConeDimension k R I P).height_eq x |>.symm.trans hheight
  have hdimx : quotientConeDimension k R I P x = Int.ofNat n := by
    rw [← Int.toNat_of_nonneg
      ((quotientConeDimension k R I P).nonnegative x)]
    exact congrArg Int.ofNat hnat
  have hdimP : dimension k R ⟨P, inferInstance⟩ = Int.ofNat n := by
    rw [← Int.toNat_of_nonneg
      ((dimension k R).nonnegative ⟨P, inferInstance⟩)]
    rfl
  exact hdimx.trans hdimP.symm

noncomputable def quotientConeFundamental
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I P : Ideal R) [P.IsPrime] :
    cyclesOfDimension
      (AffineNormalCone.scheme (R ⧸ P) (Ideal.map (Ideal.Quotient.mk P) I))
      (quotientConeDimension k R I P)
      (dimension k R ⟨P, inferInstance⟩) := by
  let _ : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let _ : Algebra.FiniteType k (R ⧸ P) := quotient_finiteType k R P
  let _ : IsNoetherianRing (R ⧸ P) := quotient_isNoetherianRing k R P
  let J : Ideal (R ⧸ P) := Ideal.map (Ideal.Quotient.mk P) I
  by_cases hJ : J = ⊤
  · exact 0
  · apply cyclesOfDimension.fundamental
    intro x hx
    exact quotientConeDimension_of_isMax k R I P hJ x hx

noncomputable def integralNormalConeGraded
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I P : Ideal R) [P.IsPrime] :
    cyclesOfDimension (AffineNormalCone.scheme R I)
      (normalConeDimension k R I) (dimension k R ⟨P, inferInstance⟩) := by
  let _ : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let _ : Algebra.FiniteType k (R ⧸ P) := quotient_finiteType k R P
  let _ : IsNoetherianRing (R ⧸ P) := quotient_isNoetherianRing k R P
  let f := AffineDeformationSpace.quotientNormalConeMap R I P
  exact (cyclesOfDimension.properPushforward f
    (quotientConeFundamental k R I P))

/-! The other extreme is the identity immersion.  It is useful to record this separately:
when the image ideal is zero, the source normal cone is the original integral quotient and
its generic coefficient is one.  In particular this case must not be identified with the
empty-cone case above. -/

theorem integralNormalConeCycle_imageIdeal_bot_apply
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I P : Ideal R) [P.IsPrime]
    (h : Ideal.map (Ideal.Quotient.mk P) I = (⊥ : Ideal (R ⧸ P)))
    (x : AffineNormalCone.scheme (R ⧸ P)
      (Ideal.map (Ideal.Quotient.mk P) I)) (hx : IsMax x) :
    integralNormalConeCycle k R I P
      ((AffineDeformationSpace.quotientNormalConeMap R I P).base x) = 1 := by
  let _ : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let _ : IsNoetherianRing (R ⧸ P) := quotient_isNoetherianRing k R P
  let _ : Algebra.FiniteType k (R ⧸ P) := quotient_finiteType k R P
  let _ : IsLocallyNoetherian (AffineNormalCone.scheme (R ⧸ P)
      (Ideal.map (Ideal.Quotient.mk P) I)) :=
    associatedGraded_locallyNoetherian (R ⧸ P)
      (Ideal.map (Ideal.Quotient.mk P) I)
  let _ : _root_.IsReduced (AffineNormalCone.associatedGradedRing (R ⧸ P)
      (Ideal.map (Ideal.Quotient.mk P) I)) := by
    rw [h]
    exact isReduced_of_injective (AffineNormalCone.associatedGradedRingBotEquiv (R ⧸ P))
      (AffineNormalCone.associatedGradedRingBotEquiv (R ⧸ P)).injective
  rw [show integralNormalConeCycle k R I P =
      AlgebraicCycle.map (AffineDeformationSpace.quotientNormalConeMap R I P)
        (quotientConeDimension k R I P) (normalConeDimension k R I)
        (AffineNormalCone.scheme (R ⧸ P)
          (Ideal.map (Ideal.Quotient.mk P) I)).fundamentalCycle by
    rfl]
  have hdim : quotientConeDimension k R I P =
      fun a ↦ normalConeDimension k R I
        ((AffineDeformationSpace.quotientNormalConeMap R I P).base a) := by
    funext a
    exact DimensionFunction.apply_eq_of_isClosedImmersion
      (quotientConeDimension k R I P) (normalConeDimension k R I)
      (AffineDeformationSpace.quotientNormalConeMap R I P) a
  rw [hdim]
  rw [AlgebraicCycle.map_closedImmersion_apply_image]
  exact (AffineNormalCone.scheme (R ⧸ P)
    (Ideal.map (Ideal.Quotient.mk P) I)).fundamentalCycle_apply_of_isMax_of_isReduced x hx

theorem integralNormalConeGraded_coe
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I P : Ideal R) [P.IsPrime] :
    (integralNormalConeGraded k R I P : AlgebraicCycle
      (AffineNormalCone.scheme R I) ℚ) =
      integralNormalConeCycle k R I P := by
  unfold integralNormalConeGraded quotientConeFundamental
  by_cases hJ : Ideal.map (Ideal.Quotient.mk P) I = ⊤
  · simp [hJ, integralNormalConeCycle_imageIdeal_top k R I P hJ]
  · simp only [dif_neg hJ]
    unfold integralNormalConeCycle
    rfl

/-! ## Linear extension over affine cycles -/

private theorem finite_support_affine
    (R : Type u) [CommRing R] (c : AlgebraicCycle (affineScheme R) ℚ) :
    (Function.support (c : affineScheme R → ℚ)).Finite := by
  have h := c.locallyFiniteSupport.finite_inter_support_of_isCompact
    (isCompact_univ (X := affineScheme R))
  simpa using h

noncomputable def integralTerm
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) (V : affineScheme R) :
    AlgebraicCycle (AffineNormalCone.scheme R I) ℚ :=
  integralNormalConeCycle k R I V.asIdeal

private theorem finite_support_summand
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R)
    (c : AlgebraicCycle (affineScheme R) ℚ) :
    Function.HasFiniteSupport (fun V ↦
      (c : affineScheme R → ℚ) V • integralTerm k R I V) :=
  (finite_support_affine R c).subset fun V hV hz ↦ hV (by
    change (c : affineScheme R → ℚ) V = 0 at hz
    change (c : affineScheme R → ℚ) V • integralTerm k R I V = 0
    rw [hz, zero_smul])

private theorem finite_support_graded_summand
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R)
    (c : AlgebraicCycle (affineScheme R) ℚ) :
    Function.HasFiniteSupport (fun V ↦
      (c : affineScheme R → ℚ) V •
        (integralNormalConeGraded k R I V.asIdeal : AlgebraicCycle
          (AffineNormalCone.scheme R I) ℚ)) :=
  (finite_support_affine R c).subset fun V hV hz ↦ hV (by
    change (c : affineScheme R → ℚ) V = 0 at hz
    change (c : affineScheme R → ℚ) V •
      (integralNormalConeGraded k R I V.asIdeal : AlgebraicCycle
        (AffineNormalCone.scheme R I) ℚ) = 0
    rw [hz, zero_smul])

noncomputable def cycleSpecialization
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) :
    AlgebraicCycle (affineScheme R) ℚ →ₗ[ℚ]
      AlgebraicCycle (AffineNormalCone.scheme R I) ℚ where
  toFun c := ∑ᶠ V, (c : affineScheme R → ℚ) V • integralTerm k R I V
  map_add' c d := by
    have h : ∀ V, ((c + d : AlgebraicCycle (affineScheme R) ℚ) :
        affineScheme R → ℚ) V • integralTerm k R I V =
        (c : affineScheme R → ℚ) V • integralTerm k R I V +
          (d : affineScheme R → ℚ) V • integralTerm k R I V := by
      intro V
      have hcd : ((c + d : AlgebraicCycle (affineScheme R) ℚ) :
          affineScheme R → ℚ) V = (c : affineScheme R → ℚ) V +
            (d : affineScheme R → ℚ) V := by simp
      rw [hcd, add_smul]
    simp only [h]
    exact finsum_add_distrib (finite_support_summand k R I c)
      (finite_support_summand k R I d)
  map_smul' q c := by
    have h : ∀ V, ((q • c : AlgebraicCycle (affineScheme R) ℚ) :
        affineScheme R → ℚ) V • integralTerm k R I V =
        q • ((c : affineScheme R → ℚ) V • integralTerm k R I V) := by
      intro V
      rw [Function.locallyFinsuppWithin.coe_rational_smul]
      simp [smul_smul]
    simp only [RingHom.id_apply, h]
    exact (smul_finsum' q (finite_support_summand k R I c)).symm

@[simp]
theorem cycleSpecialization_apply
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R)
    (c : AlgebraicCycle (affineScheme R) ℚ) :
    cycleSpecialization k R I c =
      ∑ᶠ V, (c : affineScheme R → ℚ) V • integralTerm k R I V :=
  rfl

/-! The linear specialization is determined on the actual point cycles.  This is the
single-cycle calculation used before extending over the finite support of an affine cycle. -/

theorem cycleSpecialization_point
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) (i : ℤ)
    (V : affineScheme R) (hV : dimension k R V = i) :
    cycleSpecialization k R I
        (cyclesOfDimension.point V hV : AlgebraicCycle (affineScheme R) ℚ) =
      integralTerm k R I V := by
  rw [cycleSpecialization_apply]
  rw [finsum_eq_single _ V]
  · simp [cyclesOfDimension.point_apply_self]
  · intro W hW
    simp [cyclesOfDimension.point_apply_of_ne V W hV hW]

noncomputable def cycleSpecializationGraded
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) (i : ℤ) :
    cyclesOfDimension (affineScheme R) (dimension k R) i →ₗ[ℚ]
      cyclesOfDimension (AffineNormalCone.scheme R I)
        (normalConeDimension k R I) i where
  toFun z := by
    classical
    refine ⟨∑ᶠ V, (z.1 : affineScheme R → ℚ) V •
      (integralNormalConeGraded k R I V.asIdeal : AlgebraicCycle
        (AffineNormalCone.scheme R I) ℚ), ?_⟩
    intro y hy
    rw [VectorBundle.finsum_cycle_apply
      (fun V ↦ (z.1 : affineScheme R → ℚ) V •
        (integralNormalConeGraded k R I V.asIdeal : AlgebraicCycle
          (AffineNormalCone.scheme R I) ℚ))
      (finite_support_graded_summand k R I z.1) y]
    apply finsum_eq_zero_of_forall_eq_zero
    intro V
    by_cases hzero : (z.1 : affineScheme R → ℚ) V = 0
    · simp [hzero]
    · have hdim : dimension k R V = i := by
        by_contra hne
        exact hzero (z.2 V hne)
      have hterm :
          (integralNormalConeGraded k R I V.asIdeal :
            AlgebraicCycle (AffineNormalCone.scheme R I) ℚ) y = 0 :=
        (integralNormalConeGraded k R I V.asIdeal).2 y (by
          intro h
          apply hy
          exact h.trans hdim)
      simp [hterm]
  map_add' z w := by
    apply Subtype.ext
    have h : ∀ V, ((z + w : cyclesOfDimension (affineScheme R)
        (dimension k R) i).1 : affineScheme R → ℚ) V •
        (integralNormalConeGraded k R I V.asIdeal : AlgebraicCycle
          (AffineNormalCone.scheme R I) ℚ) =
        (z.1 : affineScheme R → ℚ) V •
          (integralNormalConeGraded k R I V.asIdeal : AlgebraicCycle
            (AffineNormalCone.scheme R I) ℚ) +
        (w.1 : affineScheme R → ℚ) V •
          (integralNormalConeGraded k R I V.asIdeal : AlgebraicCycle
            (AffineNormalCone.scheme R I) ℚ) := by
      intro V
      have hzw : ((z + w : cyclesOfDimension (affineScheme R)
          (dimension k R) i).1 : affineScheme R → ℚ) V =
          (z.1 : affineScheme R → ℚ) V + (w.1 : affineScheme R → ℚ) V := by
        simp
      rw [hzw, add_smul]
    simp only [h]
    exact finsum_add_distrib
      (finite_support_graded_summand k R I z.1)
      (finite_support_graded_summand k R I w.1)
  map_smul' q z := by
    apply Subtype.ext
    have h : ∀ V, (((q • z : cyclesOfDimension (affineScheme R)
        (dimension k R) i).1 : affineScheme R → ℚ) V) •
        (integralNormalConeGraded k R I V.asIdeal : AlgebraicCycle
          (AffineNormalCone.scheme R I) ℚ) =
        q • ((z.1 : affineScheme R → ℚ) V •
          (integralNormalConeGraded k R I V.asIdeal : AlgebraicCycle
            (AffineNormalCone.scheme R I) ℚ)) := by
      intro V
      change (q * (z.1 : affineScheme R → ℚ) V) •
        (integralNormalConeGraded k R I V.asIdeal : AlgebraicCycle
          (AffineNormalCone.scheme R I) ℚ) = _
      simp [smul_smul]
    simp only [RingHom.id_apply, h]
    exact (smul_finsum' q (finite_support_graded_summand k R I z.1)).symm

theorem cycleSpecializationGraded_coe
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) (i : ℤ)
    (z : cyclesOfDimension (affineScheme R) (dimension k R) i) :
    (cycleSpecializationGraded k R I i z : AlgebraicCycle
      (AffineNormalCone.scheme R I) ℚ) =
      cycleSpecialization k R I z.1 := by
  apply finsum_congr
  intro V
  rw [integralNormalConeGraded_coe]
  rfl

end NormalConeSpecialization

end

end GromovWitten.AlgebraicGeometry.IntersectionTheory
