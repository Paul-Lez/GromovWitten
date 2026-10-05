/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.NormalizationFinite
import GromovWitten.AlgebraicGeometry.Curves.ProperCurveTopology
import GromovWitten.AlgebraicGeometry.Curves.RegularProperCurveCohomology
import GromovWitten.AlgebraicGeometry.Curves.FiniteMorphismHigherDirectImage
import GromovWitten.AlgebraicGeometry.Curves.AffinePushforwardDerived
import GromovWitten.AlgebraicGeometry.Curves.AffineHigherDirectImageSections
import GromovWitten.AlgebraicGeometry.Curves.ClosedSupportCohomology
import GromovWitten.AlgebraicGeometry.Curves.FiniteCohomologyExact
import GromovWitten.AlgebraicGeometry.Curves.ModuleOpenBaseChange
import GromovWitten.AlgebraicGeometry.Curves.ModuleStalk
import GromovWitten.AlgebraicGeometry.Curves.CoherentHigherDirectImage
import GromovWitten.AlgebraicGeometry.SheafCohomology.CoherentExactSequences
import GromovWitten.AlgebraicGeometry.Curves.CurveHigherVanishing
import GromovWitten.AlgebraicGeometry.RegularScheme
import Mathlib.RingTheory.DedekindDomain.Basic

/-!
# Cohomology and higher direct images on proper integral curves

Over a characteristic-zero field, the normalization comparison and closed-support finiteness show
that every cohomology module of a finitely presented module is finite. Over any field, proper
integral curves have no higher direct images in degrees at least two.
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
open _root_.AlgebraicGeometry
noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry

private theorem dimensionLEOne_sections_of_closed_nonGeneric
    {X : Scheme.{u}} [IsIntegral X]
    (hpt : ∀ x : X, x ≠ genericPoint X → IsClosed ({x} : Set X))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    Ring.DimensionLEOne Γ(X, U) := by
  let A := Γ(X, U)
  have hzero : IsGenericPoint (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) Set.univ := by
    rw [IsGenericPoint, PrimeSpectrum.closure_singleton, PrimeSpectrum.zeroLocus_bot]
  have hgen : (genericPoint (Spec A) : PrimeSpectrum A).asIdeal = ⊥ := by
    have heq := hzero.eq (genericPoint_spec (Spec A))
    exact congrArg PrimeSpectrum.asIdeal heq.symm
  constructor
  intro p hp hprime
  let q : Spec A := ⟨p, hprime⟩
  have hneq : hU.fromSpec q ≠ genericPoint X := by
    intro heq
    have hpoint : q = genericPoint (Spec A) := hU.fromSpec.isOpenEmbedding.injective
      (heq.trans (genericPoint_eq_of_isOpenImmersion hU.fromSpec).symm)
    apply hp
    exact (congrArg PrimeSpectrum.asIdeal hpoint).trans hgen
  have hclosed := (hpt (hU.fromSpec q) hneq).preimage hU.fromSpec.continuous
  have hset : hU.fromSpec ⁻¹' ({hU.fromSpec q} : Set X) = ({q} : Set (Spec A)) := by
    ext r
    exact hU.fromSpec.isOpenEmbedding.injective.eq_iff
  rw [hset] at hclosed
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp hclosed

set_option backward.isDefEq.respectTransparency false in
private theorem resTrdeg_genericPoint_eq_of_open_iso
    {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (CommRingCat.of k)) (ν : Y ⟶ X)
    (U : X.Opens) [Nonempty U] [IsIso (ν ∣_ U)] :
    IntersectionTheory.FiniteTypeDimension.resTrdeg (ν ≫ f) (genericPoint Y) =
      IntersectionTheory.FiniteTypeDimension.resTrdeg f (genericPoint X) := by
  let V := ν ⁻¹ᵁ U
  have _ : Nonempty V := ⟨inv (ν ∣_ U) (Classical.arbitrary U)⟩
  have hj := IntersectionTheory.FiniteTypeDimension.resTrdeg_comp
    (ν ≫ f) V.ι (genericPoint V)
  have hg := IntersectionTheory.FiniteTypeDimension.resTrdeg_comp
    (U.ι ≫ f) (ν ∣_ U) (genericPoint V)
  have hb := IntersectionTheory.FiniteTypeDimension.resTrdeg_comp f U.ι (genericPoint U)
  have hcomp : V.ι ≫ (ν ≫ f) = (ν ∣_ U) ≫ (U.ι ≫ f) := by
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  rw [genericPoint_eq_of_isOpenImmersion V.ι] at hj
  rw [genericPoint_eq_of_isOpenImmersion (ν ∣_ U)] at hg
  rw [genericPoint_eq_of_isOpenImmersion U.ι] at hb
  exact hj.symm.trans ((congrArg
    (fun g => IntersectionTheory.FiniteTypeDimension.resTrdeg g (genericPoint V)) hcomp).trans
    (hg.trans hb))

private theorem normalization_scheme_isRegular_of_resTrdeg_one
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hdim : IntersectionTheory.FiniteTypeDimension.resTrdeg f (genericPoint X) = 1) :
    SchemeIsRegular (Curves.Normalization.scheme X) := by
  let N := Curves.Normalization.scheme X
  let ν := Curves.Normalization.toCurve X
  have hνfinite : IsFinite ν := Curves.Normalization.isFinite_toCurve X k f
  have hpt : ∀ y : X, y ≠ genericPoint X → IsClosed ({y} : Set X) :=
    isClosed_singleton_of_ne_genericPoint_of_resTrdeg f hdim
  have _ : IsFinite ν := hνfinite
  intro x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := ν x) trivial
  let W := ν ⁻¹ᵁ U
  have hxW : x ∈ W := hxU
  let _ : Nonempty U := ⟨⟨ν x, hxU⟩⟩
  let _ : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hW : IsAffineOpen W := hU.preimage ν
  let A := Γ(X, U)
  let B := Γ(N, W)
  have hAnoeth : IsNoetherianRing A := by
    let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    exact IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hAdim : Ring.DimensionLEOne A :=
    dimensionLEOne_sections_of_closed_nonGeneric hpt U hU
  let _ : IsDomain A := _root_.AlgebraicGeometry.IsIntegral.component_integral U
  let _ : Algebra A B := (ν.app U).hom.toAlgebra
  have hABfinite : Module.Finite A B := RingHom.finite_algebraMap.mp (ν.finite_app U hU)
  let _ : Module.Finite A B := hABfinite
  let _ : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have hBdim : Ring.DimensionLEOne B := Ring.DimensionLEOne.of_isIntegral A B
  have hBnoeth : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  let _ : IsIntegral N := Curves.Normalization.scheme_isIntegral X
  have hBdomain : IsDomain B := _root_.AlgebraicGeometry.IsIntegral.component_integral W
  have hBic : IsIntegrallyClosed B := Curves.Normalization.isIntegrallyClosed_sections X U hU
  have hBded : IsDedekindDomain B := by
    rw [isDedekindDomain_iff B (FractionRing B)]
    exact ⟨hBdomain, hBnoeth, hBdim,
      fun {_} hx => (isIntegrallyClosed_iff (FractionRing B)).mp hBic hx⟩
  have hBregular : IsRegularRing B := by
    let _ : IsDedekindDomain B := hBded
    infer_instance
  have hWregular : SchemeIsRegular W.toScheme :=
    SchemeIsRegular.of_iso hW.isoSpec.symm (SchemeIsRegular.spec B)
  let xW : W.toScheme := ⟨x, hxW⟩
  have hxWreg : IsRegularLocalRing (W.toScheme.presheaf.stalk xW) := hWregular xW
  let _ : IsIso (W.ι.stalkMap xW) := by infer_instance
  exact IsRegularLocalRing.of_ringEquiv
    ((asIso (W.ι.stalkMap xW)).commRingCatIsoToRingEquiv.symm)

private theorem finite_cohomology_on_normalization
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X]
    (s : X ⟶ Spec (CommRingCat.of k)) [IsProper s]
    (hdim : IntersectionTheory.FiniteTypeDimension.resTrdeg s (genericPoint X) = 1)
    (M : (Curves.Normalization.scheme X).Modules) [M.IsFinitePresentation] (n : ℕ) :
    Module.Finite k
      (Curves.cohomologyModuleCat k (Curves.Normalization.toCurve X ≫ s) M n) := by
  let ν := Curves.Normalization.toCurve X
  have hνfinite : IsFinite ν := Curves.Normalization.isFinite_toCurve X k s
  have _ : IsFinite ν := hνfinite
  have _ : IsProper ν := inferInstance
  have _ : LocallyOfFiniteType ν := Curves.Normalization.locallyOfFiniteType_toCurve X k s
  have _ : IsIntegral (Curves.Normalization.scheme X) :=
    Curves.Normalization.scheme_isIntegral X
  have _ : IsProper (ν ≫ s) := inferInstance
  have hregular : SchemeIsRegular (Curves.Normalization.scheme X) :=
    normalization_scheme_isRegular_of_resTrdeg_one k s hdim
  obtain ⟨U, hU, hUne, hiso⟩ :=
    Curves.Normalization.exists_nonempty_isIso_morphismRestrict_toCurve X k s
  let _ : Nonempty U := hUne
  let _ : IsIso (ν ∣_ U) := hiso
  have hdimN : IntersectionTheory.FiniteTypeDimension.resTrdeg (ν ≫ s)
      (genericPoint (Curves.Normalization.scheme X)) = 1 :=
    (resTrdeg_genericPoint_eq_of_open_iso s ν U).trans hdim
  let C : RegularProperCurve k := RegularProperCurve.mk
    (Curves.Normalization.scheme X) (ν ≫ s) hregular hdimN
  exact C.finite_cohomology M n

private theorem finite_cohomology_of_normalization_pushforward
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X]
    (s : X ⟶ Spec (CommRingCat.of k)) [IsProper s]
    (hdim : IntersectionTheory.FiniteTypeDimension.resTrdeg s (genericPoint X) = 1)
    (M : (Curves.Normalization.scheme X).Modules) [M.IsFinitePresentation] (n : ℕ) :
    Module.Finite k
      (Curves.cohomologyModuleCat k s
        ((Scheme.Modules.pushforward (Curves.Normalization.toCurve X)).obj M) n) := by
  let N := Curves.Normalization.scheme X
  let ν := Curves.Normalization.toCurve X
  have hνfinite : IsFinite ν := Curves.Normalization.isFinite_toCurve X k s
  have _ : IsFinite ν := hνfinite
  have _ : LocallyOfFiniteType s := inferInstance
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have _ : IsLocallyNoetherian N :=
    LocallyOfFiniteType.isLocallyNoetherian (ν ≫ s)
  have hP : ((Scheme.Modules.pushforward ν).obj M).IsFinitePresentation :=
    Curves.finite_pushforward_isFinitePresentation ν M
  let P := (Scheme.Modules.pushforward ν).obj M
  let _ : P.IsFinitePresentation := hP
  let _ : P.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation P
  let _ : M.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation M
  let e : Curves.cohomologyModuleCat k s P n ≅
      Curves.cohomologyModuleCat k (ν ≫ s) M n :=
    (Curves.higherDirectImageSectionsIsoCohomology (R := CommRingCat.of k) s P n).symm ≪≫
      (moduleSpecΓFunctor (R := CommRingCat.of k)).mapIso
        (Curves.affinePushforwardHigherDirectImageIso ν s M n) ≪≫
      Curves.higherDirectImageSectionsIsoCohomology (R := CommRingCat.of k) (ν ≫ s) M n
  have hfinite := finite_cohomology_on_normalization k s hdim M n
  let _ : Module.Finite k (Curves.cohomologyModuleCat k (ν ≫ s) M n) := hfinite
  exact Module.Finite.equiv e.toLinearEquiv.symm

end GromovWitten.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

private theorem topologicalKrullDim_le_one_of_resTrdeg_one
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (s : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType s]
    (hdim : IntersectionTheory.FiniteTypeDimension.resTrdeg s (genericPoint X) = 1) :
    topologicalKrullDim X ≤ 1 := by
  change Order.krullDim (IrreducibleCloseds X) ≤ 1
  rw [Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints]
  rw [Order.krullDim_eq_iSup_height]
  refine iSup_le fun x => ?_
  have h : Order.height x ≤ 1 :=
    (Order.height_mono (IntersectionTheory.HomogeneityLocal.isTop_genericPoint X x)).trans
      (le_of_eq ((IntersectionTheory.FiniteTypeDimension.height_eq_resTrdeg s _).trans hdim))
  exact WithBot.coe_le_coe.mpr h




set_option backward.isDefEq.respectTransparency false in
/-- A finitely presented module on a proper integral curve has finite cohomology in every degree
when the base field has characteristic zero. -/
theorem finite_cohomology_of_proper_integral_curve
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X]
    (s : X ⟶ Spec (CommRingCat.of k)) [IsProper s]
    (hdim : IntersectionTheory.FiniteTypeDimension.resTrdeg s (genericPoint X) = 1)
    (M : X.Modules) [M.IsFinitePresentation] (n : ℕ) :
    Module.Finite k (cohomologyModuleCat k s M n) := by
  let ν := Normalization.toCurve X
  let N := Normalization.scheme X
  let Mν : N.Modules := (Scheme.Modules.pullback ν).obj M
  let _ : Mν.IsFinitePresentation := inferInstance
  let _ : LocallyOfFiniteType s := inferInstance
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have hνfinite : IsFinite ν := Normalization.isFinite_toCurve X k s
  let _ : IsFinite ν := hνfinite
  have hPfp : ((Scheme.Modules.pushforward ν).obj Mν).IsFinitePresentation :=
    finite_pushforward_isFinitePresentation ν Mν
  let P : X.Modules := (Scheme.Modules.pushforward ν).obj Mν
  let _ : P.IsFinitePresentation := hPfp
  let _ : P.IsQuasicoherent :=
    SheafOfModules.instIsQuasicoherentOfIsFinitePresentation P
  let _ : M.IsQuasicoherent :=
    SheafOfModules.instIsQuasicoherentOfIsFinitePresentation M
  let φ : M ⟶ P := (Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app M
  have hKfp : (kernel φ).IsFinitePresentation :=
    GromovWitten.AlgebraicGeometry.SheafCohomology.isFinitePresentation_kernel φ
  have hCfp : (cokernel φ).IsFinitePresentation :=
    GromovWitten.AlgebraicGeometry.SheafCohomology.isFinitePresentation_cokernel φ
  let _ : (kernel φ).IsFinitePresentation := hKfp
  let _ : (kernel φ).IsQuasicoherent :=
    SheafOfModules.instIsQuasicoherentOfIsFinitePresentation (kernel φ)
  let _ : (cokernel φ).IsFinitePresentation := hCfp
  obtain ⟨U, _hUaff, hUne, hUiso⟩ :=
    Normalization.exists_nonempty_isIso_morphismRestrict_toCurve X k s
  let _ : Nonempty U := hUne
  let _ : IsIso (ν ∣_ U) := hUiso
  have hunit : IsIso ((Scheme.Modules.pullback U.ι).map φ) :=
    pullbackPushforwardUnit_isIso_of_isIso_restrict (X := N) (Y := X) ν U M
  let _ : IsIso ((Scheme.Modules.pullback U.ι).map φ) := hunit
  have hgen : genericPoint X ∈ U := Normalization.genericPoint_mem_of_nonempty X U
  have hstalk : IsIso ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (genericPoint X)).map φ) :=
    stalk_isIso_of_open_pullback (X := X) φ U (genericPoint X) hgen
  let _ : IsIso ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (genericPoint X)).map φ) := hstalk
  have htrivial := kernel_cokernel_stalk_subsingleton_of_stalk_isIso (X := X) φ (genericPoint X)
  have hKclosed : ∀ x : X, Nontrivial ((kernel φ).presheaf.stalk x) →
      IsClosed ({x} : Set X) := by
    intro x hx
    rcases eq_or_ne x (genericPoint X) with rfl | hne
    · exact False.elim ((not_nontrivial_iff_subsingleton.mpr htrivial.1) hx)
    · exact isClosed_singleton_of_ne_genericPoint_of_resTrdeg s hdim x hne
  have hCclosed : ∀ x : X, Nontrivial ((cokernel φ).presheaf.stalk x) →
      IsClosed ({x} : Set X) := by
    intro x hx
    rcases eq_or_ne x (genericPoint X) with rfl | hne
    · exact False.elim ((not_nontrivial_iff_subsingleton.mpr htrivial.2) hx)
    · exact isClosed_singleton_of_ne_genericPoint_of_resTrdeg s hdim x hne
  have hKfinite : ∀ m : ℕ,
      Module.Finite (CommRingCat.of k)
        (cohomologyModuleCat (CommRingCat.of k) s (kernel φ) m) := by
    intro m
    exact finite_cohomology_of_closed_support s (kernel φ) hKclosed m
  have hPfinite : ∀ m : ℕ,
      Module.Finite (CommRingCat.of k)
        (cohomologyModuleCat (CommRingCat.of k) s P m) := by
    intro m
    exact GromovWitten.AlgebraicGeometry.finite_cohomology_of_normalization_pushforward
      k s hdim Mν m
  have hCfinite : ∀ m : ℕ,
      Module.Finite (CommRingCat.of k)
        (cohomologyModuleCat (CommRingCat.of k) s (cokernel φ) m) := by
    intro m
    exact finite_cohomology_of_closed_support s (cokernel φ) hCclosed m
  exact finite_cohomology_of_finite_kernel_cokernel s φ hKfinite hPfinite hCfinite n

/-- For any field, higher direct images of modules on a proper integral curve vanish in degrees
at least two. -/
theorem isZero_higherDirectImageModule_of_proper_integral_curve
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X]
    (s : X ⟶ Spec (CommRingCat.of k)) [IsProper s]
    (hdim : IntersectionTheory.FiniteTypeDimension.resTrdeg s (genericPoint X) = 1)
    (M : X.Modules) (n : ℕ) :
    IsZero (higherDirectImageModule s M (n + 2)) := by
  let _ : LocallyOfFiniteType s := inferInstance
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  let _ : IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := inferInstance }
  exact isZero_higherDirectImageModule_of_isNoetherian_topologicalKrullDim_le_one
    s (topologicalKrullDim_le_one_of_resTrdeg_one s hdim) M n

/-- Over a characteristic-zero field, higher direct images of a finitely presented module on a
proper integral curve are finitely presented. -/
theorem isFinitePresentation_higherDirectImageModule_of_proper_integral_curve
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X]
    (s : X ⟶ Spec (CommRingCat.of k)) [IsProper s]
    (hdim : IntersectionTheory.FiniteTypeDimension.resTrdeg s (genericPoint X) = 1)
    (M : X.Modules) [M.IsFinitePresentation] (n : ℕ) :
    (higherDirectImageModule s M n).IsFinitePresentation := by
  let _ : LocallyOfFiniteType s := inferInstance
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  let _ : M.IsQuasicoherent :=
    SheafOfModules.instIsQuasicoherentOfIsFinitePresentation M
  exact
    (isFinitePresentation_higherDirectImageModule_iff_finite_cohomology
      (R := CommRingCat.of k) s M n).2
      (finite_cohomology_of_proper_integral_curve k s hdim M n)

end GromovWitten.AlgebraicGeometry.Curves
