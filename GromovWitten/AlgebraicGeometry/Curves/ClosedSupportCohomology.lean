/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.Algebra.FiniteModuleSupport
import GromovWitten.AlgebraicGeometry.Curves.ModuleStalk
import GromovWitten.AlgebraicGeometry.Curves.QuasiCoherentPushforward
import GromovWitten.AlgebraicGeometry.Curves.AffineFinitePresentation
import GromovWitten.AlgebraicGeometry.Curves.FinitePresentationPullback
import GromovWitten.AlgebraicGeometry.Curves.OpenPullbackSectionsLinear
import GromovWitten.AlgebraicGeometry.Curves.ArithmeticGenus
import GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteSupport
import GromovWitten.AlgebraicGeometry.SheafCohomology.FlasqueCohomology
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Finiteness of cohomology with closed support

On a quasi-compact, locally finite type scheme over a Noetherian Jacobson affine base, a finitely
presented module whose nonzero stalks are closed has finite global sections. Its degree-zero
cohomology is therefore finite over the base ring.
-/

open CategoryTheory Limits AlgebraicGeometry
noncomputable section
universe u v
namespace GromovWitten.AlgebraicGeometry.Curves

set_option backward.isDefEq.respectTransparency false in
private lemma affineModuleSupport_iff_stalk_nontrivial {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] (p : PrimeSpectrum R) :
    p ∈ Module.support R (moduleSpecΓFunctor.obj M : Type u) ↔
      Nontrivial (M.presheaf.stalk p) := by
  let N := moduleSpecΓFunctor.obj M
  let e : LocalizedModule p.asIdeal.primeCompl N ≃ₗ[R]
      ((tilde N).presheaf.stalk p) := IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N)
    (show N →ₗ[R] ((tilde N).presheaf.stalk p) from (tilde.toStalk N p).hom)
  have _ : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let e' := (moduleStalk (Spec R) p).mapIso (asIso M.fromTildeΓ)
  exact e.toEquiv.nontrivial_congr.trans e'.toLinearEquiv.toEquiv.nontrivial_congr

set_option backward.isDefEq.respectTransparency false in
private lemma openPullback_nontrivial_stalk_iff {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) (x : X) :
    Nontrivial (((Scheme.Modules.pullback f).obj M).presheaf.stalk x) ↔
      Nontrivial (M.presheaf.stalk (f x)) := by
  let e₁ := (Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor _ x).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm
  let e₂ := (Scheme.Modules.restrictStalkNatIso f x).app M
  let e := e₁ ≪≫ e₂
  exact (Equiv.ofBijective e.hom (ConcreteCategory.bijective_of_isIso e.hom)).nontrivial_congr

/-- On an affine finite-type chart, finite closed-point support makes the restricted module of
sections finite over the base ring. -/
theorem finite_restricted_sections_of_closed_support
    {R A : CommRingCat.{u}} [IsNoetherianRing R] [IsJacobsonRing R]
    (φ : R ⟶ A) (hφ : φ.hom.FiniteType)
    (M : (Spec A).Modules) [M.IsFinitePresentation]
    (h : ∀ p : PrimeSpectrum A,
      Nontrivial (M.presheaf.stalk p) → IsClosed ({p} : Set (PrimeSpectrum A))) :
    Module.Finite R
      ((ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj M)) := by
  let _ : Algebra R A := φ.hom.toAlgebra
  have _ : Algebra.FiniteType R A := hφ
  have _ : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  let N := moduleSpecΓFunctor.obj M
  have _ : M.IsQuasicoherent :=
    SheafOfModules.instIsQuasicoherentOfIsFinitePresentation M
  have _ : Module.FinitePresentation A (N : Type u) :=
    moduleSpecΓ_isFinitePresentation M (R := A)
  let _ : Module R (N : Type u) := Module.compHom (N : Type u) φ.hom
  have _ : IsScalarTower R A (N : Type u) := IsScalarTower.of_compHom R A (N : Type u)
  have hmax : ∀ p : PrimeSpectrum A,
      p ∈ Module.support A (N : Type u) → p.asIdeal.IsMaximal := by
    intro p hp
    have hp' : Nontrivial (M.presheaf.stalk p) :=
      (affineModuleSupport_iff_stalk_nontrivial M p).mp hp
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp (h p hp')
  have hfin : Module.Finite R (N : Type u) :=
    Module.finite_of_finiteType_of_support_maximal
      (R := R) (A := A) (N := (N : Type u)) hmax
  change Module.Finite R ((ModuleCat.restrictScalars φ.hom).obj N)
  exact hfin

private lemma finite_baseSections_of_finite_cover
    {R : CommRingCat.{u}} [IsNoetherianRing R] {X : Scheme.{u}}
    (s : X ⟶ Spec R) (M : X.Modules) {ι : Type v} [Finite ι]
    (U : ι → X.Opens) (hU : iSup U = ⊤)
    (hfin : ∀ i, Module.Finite R (baseSectionModule s (U i) M)) :
    Module.Finite R (baseSectionModule s ⊤ M) := by
  let ψ : baseSectionModule s ⊤ M →ₗ[R] ∀ i, baseSectionModule s (U i) M :=
    LinearMap.pi fun i => (baseSectionRestrictionMap s M (homOfLE (le_top (a := U i)))).hom
  apply Module.Finite.of_injective ψ
  intro a b hab
  apply TopCat.Presheaf.IsSheaf.section_ext ((moduleToSheafAb X).obj M).property
  intro x _
  have hx : x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨U i, le_top, hi, congrFun hab i⟩

set_option backward.isDefEq.respectTransparency false in
/-- A finitely presented module with closed nonzero stalks on a quasi-compact, locally finite
type scheme over a Noetherian Jacobson affine base has finite global sections. -/
theorem finite_sections_of_closed_support
    {R : CommRingCat.{u}} [IsNoetherianRing R] [IsJacobsonRing R]
    {X : Scheme.{u}} (s : X ⟶ Spec R) [LocallyOfFiniteType s] [QuasiCompact s]
    (M : X.Modules) [M.IsFinitePresentation]
    (h : ∀ x : X, Nontrivial (M.presheaf.stalk x) → IsClosed ({x} : Set X)) :
    Module.Finite R (baseSectionModule s ⊤ M) := by
  have hlocal (U : X.Opens) (hU : IsAffineOpen U) :
      Module.Finite R (baseSectionModule s U M) := by
    let f := hU.fromSpec
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (f ≫ s)
    have hft : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    have hφft : φ.hom.FiniteType := HasRingHomProperty.Spec_iff.mp hft
    let N := (Scheme.Modules.pullback f).obj M
    have hN : Module.Finite R
        ((ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj N)) := by
      apply finite_restricted_sections_of_closed_support φ hφft N
      intro p hp
      have hclosed := h (f p) ((openPullback_nontrivial_stalk_iff f M p).mp hp)
      have hpre := hclosed.preimage f.continuous
      have hset : f ⁻¹' ({f p} : Set X) = {p} := by
        ext q
        simp only [Set.mem_singleton_iff, Set.mem_preimage,
          f.isOpenEmbedding.injective.eq_iff]
      rw [← hset]
      exact hpre
    have hfin := Module.Finite.equiv (openPullbackSectionsLinearEquiv s f φ hφ.symm M)
    change Module.Finite R (baseSectionModule s hU.fromSpec.opensRange M) at hfin
    rw [hU.opensRange_fromSpec] at hfin
    exact hfin
  have _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  let 𝒰 := X.affineCover.finiteSubcover
  exact finite_baseSections_of_finite_cover s M (fun i => (𝒰.f i).opensRange)
    𝒰.iSup_opensRange (fun i => hlocal _ (isAffineOpen_opensRange (𝒰.f i)))

set_option backward.isDefEq.respectTransparency false in
/-- A finitely presented module with closed nonzero stalks on a compact locally Noetherian scheme
has finite support. -/
theorem finite_nonzero_stalk_support_of_closed_support
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (M : X.Modules) [M.IsFinitePresentation]
    (h : ∀ x : X, Nontrivial (M.presheaf.stalk x) → IsClosed ({x} : Set X)) :
    {x : X | Nontrivial (M.presheaf.stalk x)}.Finite := by
  have hlocal (U : X.Opens) (hU : IsAffineOpen U) :
      ({x : X | Nontrivial (M.presheaf.stalk x)} ∩ U).Finite := by
    let A := Γ(X, U)
    let f := hU.fromSpec
    let N := (Scheme.Modules.pullback f).obj M
    have _ : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have _ : Module.FinitePresentation A (moduleSpecΓFunctor.obj N : Type u) :=
      moduleSpecΓ_isFinitePresentation N
    have hclosed (p : Spec A) (hp : Nontrivial (N.presheaf.stalk p)) :
        IsClosed ({p} : Set (Spec A)) := by
      have hpre := (h (f p) ((openPullback_nontrivial_stalk_iff f M p).mp hp)).preimage
        f.continuous
      have hset : f ⁻¹' ({f p} : Set X) = {p} := by
        ext q
        simp only [Set.mem_singleton_iff, Set.mem_preimage,
          f.isOpenEmbedding.injective.eq_iff]
      rw [← hset]
      exact hpre
    have hfin : {p : Spec A | Nontrivial (N.presheaf.stalk p)}.Finite := by
      have hs := Module.support_finite_of_isNoetherianRing_of_support_maximal
        (N := (moduleSpecΓFunctor.obj N : Type u)) (fun p hp =>
          (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp
            (hclosed p ((affineModuleSupport_iff_stalk_nontrivial N p).mp hp)))
      have heq : {p : Spec A | Nontrivial (N.presheaf.stalk p)} =
          Module.support A (moduleSpecΓFunctor.obj N : Type u) := by
        ext p
        exact (affineModuleSupport_iff_stalk_nontrivial N p).symm
      rw [heq]
      exact hs
    apply (hfin.image f).subset
    rintro x ⟨hx, hxU⟩
    have hxrange : x ∈ Set.range f := by
      change x ∈ Set.range hU.fromSpec
      rw [hU.range_fromSpec]
      exact hxU
    obtain ⟨p, hp⟩ := hxrange
    refine ⟨p, ?_, hp⟩
    apply (openPullback_nontrivial_stalk_iff f M p).mpr
    change Nontrivial (M.presheaf.stalk x) at hx
    simpa only [hp] using hx
  let 𝒰 := X.affineCover.finiteSubcover
  have hfin := Set.finite_iUnion (fun i : 𝒰.I₀ =>
    hlocal (𝒰.f i).opensRange (isAffineOpen_opensRange (𝒰.f i)))
  apply hfin.subset
  intro x hx
  obtain ⟨i, hi⟩ := 𝒰.isOpenCover_opensRange.exists_mem x
  exact Set.mem_iUnion.mpr ⟨i, hx, hi⟩

private theorem moduleToSheafAb_isFlasque_of_finite_closed_support
    {X : Scheme.{u}} (M : X.Modules)
    (hfinite : {x : X | Nontrivial (M.presheaf.stalk x)}.Finite)
    (hclosed : ∀ x : X, Nontrivial (M.presheaf.stalk x) → IsClosed ({x} : Set X)) :
    TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj M) := by
  let S := hfinite.toFinset
  apply GromovWitten.AlgebraicGeometry.SheafCohomology.isFlasque_of_finite_closed_support
    ((moduleToSheafAb X).obj M) S
  · intro x hx
    exact hclosed x (hfinite.mem_toFinset.mp hx)
  · intro y hy
    have hzero : ¬ Nontrivial
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).obj
          ((moduleToSheafAb X).obj M).1)) := by
      change ¬ Nontrivial (M.presheaf.stalk y)
      intro hy'
      exact hy (hfinite.mem_toFinset.mpr hy')
    let _ : Subsingleton
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).obj
          ((moduleToSheafAb X).obj M).1)) := not_nontrivial_iff_subsingleton.mp hzero
    exact AddCommGrpCat.isZero_of_subsingleton _

set_option backward.isDefEq.respectTransparency false in
/-- Under a finite-presentation and closed-support hypothesis, degree-zero cohomology is finite
over a Noetherian Jacobson affine base. -/
theorem finite_cohomology_zero_of_closed_support
    {R : CommRingCat.{u}} [IsNoetherianRing R] [IsJacobsonRing R]
    {X : Scheme.{u}} (s : X ⟶ Spec R) [LocallyOfFiniteType s] [QuasiCompact s]
    (M : X.Modules)
    [M.IsFinitePresentation]
    (h : ∀ x : X, Nontrivial (M.presheaf.stalk x) → IsClosed ({x} : Set X)) :
    Module.Finite R (cohomologyModuleCat R s M 0) := by
  have hsections : Module.Finite R (baseSectionModule s ⊤ M) :=
    finite_sections_of_closed_support s M h
  have htop : baseToSections s ⊤ = (Scheme.ΓSpecIso R).inv ≫ s.appTop := by
    unfold baseToSections
    change (Scheme.ΓSpecIso R).inv ≫ s.appTop ≫ X.presheaf.map (𝟙 _) = _
    rw [X.presheaf.map_id, Category.comp_id]
  have hsections' : Module.Finite R (sectionsModuleCat R s M) := by
    let e : baseSectionModule s ⊤ M ≃ₗ[R] sectionsModuleCat R s M :=
      { toFun := id
        invFun := id
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := by
          intro r x
          change (baseToSections s ⊤).hom r • x = baseRingHom R s r • x
          rw [htop]
          rfl }
    exact Module.Finite.equiv e
  exact Module.Finite.equiv (cohomologyZeroBaseLinearEquiv R s M).symm

/-- A finitely presented module with closed nonzero stalks on a compact locally Noetherian scheme
has vanishing positive cohomology. -/
theorem isZero_cohomology_succ_of_closed_support
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (M : X.Modules) [M.IsFinitePresentation]
    (h : ∀ x : X, Nontrivial (M.presheaf.stalk x) → IsClosed ({x} : Set X))
    (n : ℕ) : IsZero (AddCommGrpCat.of (cohomology X M (n + 1))) := by
  have hsupp : {x : X | Nontrivial (M.presheaf.stalk x)}.Finite :=
    finite_nonzero_stalk_support_of_closed_support M h
  have hflasque : TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj M) :=
    moduleToSheafAb_isFlasque_of_finite_closed_support M hsupp h
  let _ : TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj M) := hflasque
  have hz := GromovWitten.AlgebraicGeometry.SheafCohomology.isZero_sheafH_of_isFlasque
    ((moduleToSheafAb X).obj M) n
  rw [cohomology_eq]
  exact hz

set_option backward.isDefEq.respectTransparency false in
/-- Every degree of cohomology is finite for a finitely presented module with closed nonzero
stalks on a quasi-compact, locally finite type scheme over a Noetherian Jacobson affine base. -/
theorem finite_cohomology_of_closed_support
    {R : CommRingCat.{u}} [IsNoetherianRing R] [IsJacobsonRing R]
    {X : Scheme.{u}} (s : X ⟶ Spec R) [LocallyOfFiniteType s] [QuasiCompact s]
    (M : X.Modules) [M.IsFinitePresentation]
    (h : ∀ x : X, Nontrivial (M.presheaf.stalk x) → IsClosed ({x} : Set X))
    (n : ℕ) :
    Module.Finite R (cohomologyModuleCat R s M n) := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  cases n with
  | zero =>
    exact finite_cohomology_zero_of_closed_support s M h
  | succ n =>
    have hz : IsZero (AddCommGrpCat.of (cohomology X M (n + 1))) :=
      isZero_cohomology_succ_of_closed_support M h n
    have hs : Subsingleton (cohomologyModuleCat R s M (n + 1)) := by
      apply AddCommGrpCat.subsingleton_of_isZero
      exact hz
    let _ : Subsingleton (cohomologyModuleCat R s M (n + 1)) := hs
    infer_instance

end GromovWitten.AlgebraicGeometry.Curves
