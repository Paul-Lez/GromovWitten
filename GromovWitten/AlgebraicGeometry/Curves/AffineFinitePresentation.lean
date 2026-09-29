/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.FinitePresentationPullback
import GromovWitten.AlgebraicGeometry.Curves.QuasiCoherentPushforward
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.RingTheory.LocalProperties.FinitePresentation

/-!
# Finite presentation of affine global sections

A finitely presented module sheaf on `Spec R` has finitely presented global sections
when `R` is Noetherian. The proof restricts the finite local presentations to
basic opens and applies the localization span criterion.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
open AlgebraicGeometry Scheme.Modules
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves

private lemma affineFP_global_finite {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] (P : M.Presentation) [P.IsFinite] :
    Module.Finite R (Γ(M, (⊤ : (Spec R).Opens)) : Type u) := by
  let eV := tildeFinsupp (R := R) P.generators.I
  have hIso : IsIso M.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let : IsIso M.fromTildeΓ := hIso
  let : IsIso eV.hom := eV.isIso_hom
  have hP : Epi P.generators.π := P.generators.epi
  have heV : Epi eV.hom := by
    exact ⟨fun {Z} g h e => by
      simpa only [eV.inv_hom_id_assoc] using
        congrArg (fun k => eV.inv ≫ k) e⟩
  let ψ : tilde (ModuleCat.of R (P.generators.I →₀ R)) ⟶ M :=
    eV.hom ≫ P.generators.π
  have hψ : Epi ψ := by exact epi_comp' heV hP
  let φ := ψ ≫ inv M.fromTildeΓ
  have hφ : Epi φ := by exact epi_comp' hψ (inferInstance : Epi (inv M.fromTildeΓ))
  let : Epi φ := hφ
  let γ : ModuleCat.of R (P.generators.I →₀ R) ⟶ moduleSpecΓFunctor.obj M :=
    (tilde.fullyFaithfulFunctor (R := R)).preimage φ
  have hγ : Epi γ := by
    constructor
    intro Z g h e
    apply (tilde.fullyFaithfulFunctor (R := R)).map_injective
    apply (cancel_epi φ).1
    have hmap : tilde.map γ = φ := by
      exact (tilde.fullyFaithfulFunctor (R := R)).map_preimage φ
    rw [← hmap]
    change tilde.map γ ≫ tilde.map g = tilde.map γ ≫ tilde.map h
    simpa only [tilde.map_comp, tilde.functor] using
      congrArg (fun k => tilde.map k) e
  let : P.generators.IsFiniteType :=
    SheafOfModules.Presentation.IsFinite.isFiniteType_generators
  let : Finite P.generators.I :=
    SheafOfModules.GeneratingSections.IsFiniteType.finite
  let : Module.Finite R (ModuleCat.of R (P.generators.I →₀ R) : Type u) := inferInstance
  apply Module.Finite.of_surjective γ.hom'
  exact (ModuleCat.epi_iff_surjective γ).mp hγ

private lemma affineFP_finite_of_semilinearEquiv {A B M N : Type u} [CommRing A] [CommRing B]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
    (σ : A →+* B) (τ : B →+* A) [RingHomInvPair σ τ] [RingHomInvPair τ σ]
    (e : M ≃ₛₗ[σ] N) [Module.Finite A M] : Module.Finite B N := by
  let : RingHomSurjective σ := ⟨fun y ↦ ⟨τ y, by
    exact congrArg (fun f ↦ f y) (inferInstance : RingHomInvPair σ τ).comp_eq₂⟩⟩
  rw [Module.finite_def]
  have hfg := Submodule.FG.map e.toLinearMap (Module.Finite.fg_top (R := A) (M := M))
  rw [Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective] at hfg
  exact hfg

private lemma affineFP_finite_sections_congr {X : Scheme.{u}} (M : X.Modules)
    {U V : X.Opens} (hUV : U = V)
    (h : Module.Finite Γ(X, U) (Γ(M, U) : Type u)) :
    Module.Finite Γ(X, V) (Γ(M, V) : Type u) := by
  subst V
  exact h

private lemma affineFP_global_fp_of_presentation {A : CommRingCat.{u}} (M : (Spec A).Modules)
    (P : M.Presentation) [P.IsFinite] [IsNoetherianRing A] :
    Module.FinitePresentation A (Γ(M, (⊤ : (Spec A).Opens)) : Type u) := by
  let : M.IsQuasicoherent := P.isQuasicoherent
  let : Module.Finite A (Γ(M, (⊤ : (Spec A).Opens)) : Type u) :=
    affineFP_global_finite M P
  exact Module.finitePresentation_of_finite A _

private lemma affineFP_affine_open_local_fp {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (U : (Spec R).Opens) (hU : IsAffineOpen U) (P : (M.restrict U.ι).Presentation)
    [P.IsFinite] [IsNoetherianRing R] :
    Module.FinitePresentation Γ(Spec R, U) (Γ(M, U) : Type u) := by
  let A : CommRingCat := Γ(Spec R, U)
  let M' : (Spec A).Modules := (restrictFunctor hU.isoSpec.inv).obj (M.restrict U.ι)
  let : PreservesColimitsOfSize.{u, u} (restrictFunctor hU.isoSpec.inv) :=
    (restrictAdjunction hU.isoSpec.inv).leftAdjoint_preservesColimits
  let P' : M'.Presentation := presentationRestrict hU.isoSpec.inv P
  let : P.generators.IsFiniteType :=
    SheafOfModules.Presentation.IsFinite.isFiniteType_generators
  let : P.relations.IsFiniteType :=
    SheafOfModules.Presentation.IsFinite.isFiniteType_relations
  have : P'.IsFinite := by
    refine { isFiniteType_generators := ?_, isFiniteType_relations := ?_ }
    · dsimp [P', presentationRestrict]
      constructor
      change Finite P.generators.I
      exact SheafOfModules.GeneratingSections.IsFiniteType.finite
    · dsimp [P', presentationRestrict]
      constructor
      change Finite P.relations.I
      exact SheafOfModules.GeneratingSections.IsFiniteType.finite
  let : M'.IsQuasicoherent := P'.isQuasicoherent
  have : IsNoetherianRing A := by
    exact IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hfp : Module.FinitePresentation A (Γ(M', (⊤ : (Spec A).Opens)) : Type u) :=
    affineFP_global_fp_of_presentation M' P'
  have hUimg : U.ι ''ᵁ hU.isoSpec.inv ''ᵁ (⊤ : (Spec A).Opens) = U := by
    rw [AlgebraicGeometry.Scheme.Hom.image_top_eq_opensRange,
      AlgebraicGeometry.Scheme.Hom.opensRange_of_isIso,
      AlgebraicGeometry.Scheme.Hom.image_top_eq_opensRange]
    exact Scheme.Opens.opensRange_ι U
  dsimp [A] at hUimg
  let f : Spec A ⟶ Spec R := hU.isoSpec.inv ≫ U.ι
  let M'' : (Spec A).Modules := (restrictFunctor f).obj M
  let iComp : M'' ≅ M' := (restrictFunctorComp hU.isoSpec.inv U.ι).app M
  let eComp : Γ(M'', (⊤ : (Spec A).Opens)) ≃+ Γ(M', (⊤ : (Spec A).Opens)) :=
    AddEquiv.ofBijective
      (Scheme.Modules.Hom.app iComp.hom (⊤ : (Spec A).Opens)).hom (by
      constructor
      · intro x y h
        have happ := congrArg (fun z ↦
          Scheme.Modules.Hom.app z (⊤ : (Spec A).Opens)) iComp.hom_inv_id
        simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at happ
        have h' := congrArg (fun z ↦ z x) happ
        have hx : (Scheme.Modules.Hom.app iComp.inv (⊤ : (Spec A).Opens)).hom
            ((Scheme.Modules.Hom.app iComp.hom (⊤ : (Spec A).Opens)).hom x) = x := by
          simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using h'
        have hy : (Scheme.Modules.Hom.app iComp.inv (⊤ : (Spec A).Opens)).hom
            ((Scheme.Modules.Hom.app iComp.hom (⊤ : (Spec A).Opens)).hom y) = y := by
          have h'' := congrArg (fun z ↦ z y) happ
          simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using h''
        exact hx.symm.trans ((congrArg
          (fun z ↦ (Scheme.Modules.Hom.app iComp.inv (⊤ : (Spec A).Opens)).hom z) h).trans hy)
      · intro y
        refine ⟨(Scheme.Modules.Hom.app iComp.inv (⊤ : (Spec A).Opens)).hom y, ?_⟩
        have happ := congrArg (fun z ↦
          Scheme.Modules.Hom.app z (⊤ : (Spec A).Opens)) iComp.inv_hom_id
        simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at happ
        have h' := congrArg (fun z ↦ z y) happ
        exact h')
  let eRestrict := Scheme.Modules.restrictAppIso f M (⊤ : (Spec A).Opens)
  let eRestrictAdd : Γ(M.restrict f, (⊤ : (Spec A).Opens)) ≃+
      Γ(M, f ''ᵁ (⊤ : (Spec A).Opens)) :=
    AddEquiv.ofBijective eRestrict.hom.hom (by
      constructor
      · intro x y h
        have h' := congrArg eRestrict.inv h
        exact (Iso.hom_inv_id_apply eRestrict x).symm.trans
          (h'.trans (Iso.hom_inv_id_apply eRestrict y))
      · intro y
        exact ⟨eRestrict.inv.hom y, by simp⟩)
  let eAdd : Γ(M', (⊤ : (Spec A).Opens)) ≃+
      Γ(M, f ''ᵁ (⊤ : (Spec A).Opens)) := by
    simpa [M''] using eComp.symm.trans eRestrictAdd
  let eR : A ≃+* Γ(Spec R, f ''ᵁ (⊤ : (Spec A).Opens)) :=
    (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv.trans
      (Scheme.Hom.appIso f (⊤ : (Spec A).Opens)).symm.commRingCatIsoToRingEquiv
  let : RingHomInvPair eR.toRingHom eR.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv eR
  let : RingHomInvPair eR.symm.toRingHom eR.toRingHom :=
    RingHomInvPair.of_ringEquiv eR.symm
  let eMap : Γ(M', (⊤ : (Spec A).Opens)) →ₛₗ[eR.toRingHom]
      Γ(M, f ''ᵁ (⊤ : (Spec A).Opens)) :=
    { toFun := eAdd
      map_add' := eAdd.map_add
      map_smul' := by
        intro r x
        have hcomp (z : Γ(M'', (⊤ : (Spec A).Opens))) :
            eComp (r • z) = r • eComp z := by
          let r' := (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv r
          change (Scheme.Modules.Hom.app iComp.hom (⊤ : (Spec A).Opens)).hom
              (r' • z) = r' •
                (Scheme.Modules.Hom.app iComp.hom (⊤ : (Spec A).Opens)).hom z
          exact Scheme.Modules.Hom.app_smul iComp.hom r' z
        have hcomp_inv : eComp.symm (r • x) = r • eComp.symm x := by
          apply eComp.injective
          rw [eComp.apply_symm_apply, hcomp, eComp.apply_symm_apply]
        change eAdd (r • x) = eR r • eAdd x
        dsimp [eAdd, eRestrictAdd, eR]
        rw [hcomp_inv]
        let r' := (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv r
        change (Scheme.Modules.restrictAppIso f M (⊤ : (Spec A).Opens)).hom.hom
            (r' • eComp.symm x) =
          (Scheme.Hom.appIso f (⊤ : (Spec A).Opens)).inv.hom r' •
            (Scheme.Modules.restrictAppIso f M (⊤ : (Spec A).Opens)).hom.hom
              (eComp.symm x)
        exact Scheme.Modules.smul_restrictAppIso_hom_apply f M
          (⊤ : (Spec A).Opens) r' (eComp.symm x) }
  let eSemi : Γ(M', (⊤ : (Spec A).Opens)) ≃ₛₗ[eR.toRingHom]
      Γ(M, f ''ᵁ (⊤ : (Spec A).Opens)) :=
    LinearEquiv.ofBijective eMap eAdd.bijective
  let : Module.Finite A (Γ(M', (⊤ : (Spec A).Opens)) : Type u) := inferInstance
  let : Module.Finite Γ(Spec R, f ''ᵁ (⊤ : (Spec A).Opens))
      (Γ(M, f ''ᵁ (⊤ : (Spec A).Opens)) : Type u) := by
    exact affineFP_finite_of_semilinearEquiv eR.toRingHom eR.symm.toRingHom eSemi
  have hUimg' : f ''ᵁ (⊤ : (Spec A).Opens) = U := by
    change (hU.isoSpec.inv ≫ U.ι) ''ᵁ (⊤ : (Spec A).Opens) = U
    rw [Scheme.Hom.comp_image]
    exact hUimg
  have hfin : Module.Finite Γ(Spec R, U)
      (Γ(M, U) : Type u) := by
    exact affineFP_finite_sections_congr M hUimg' (inferInstance :
      Module.Finite Γ(Spec R, f ''ᵁ (⊤ : (Spec A).Opens))
        (Γ(M, f ''ᵁ (⊤ : (Spec A).Opens)) : Type u))
  exact Module.finitePresentation_of_finite Γ(Spec R, U) (Γ(M, U) : Type u)


private noncomputable def affineFP_restrict_map {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (U : (Spec R).Opens) : Γ(M, ⊤) →ₗ[R] Γ(M, U) := by
  exact {
    toFun := M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
    map_add' := by intros; simp
    map_smul' := by
      intro r x
      exact M.map_smul_Spec (homOfLE (show U ≤ ⊤ from le_top)).op r x
  }

private lemma affineFP_restrict_loc {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] (f : R) :
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen f
  IsLocalizedModule.Away f (affineFP_restrict_map M U) := by
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen f
  let e := modulesSpecToSheaf.mapIso (asIso M.fromTildeΓ)
  have hloc : IsLocalizing (modulesSpecToSheaf.obj M) :=
    (isLocalizing_iff_of_iso e).mp (isLocalizing_tilde _)
  let : IsLocalizedModule.Away f
      ((modulesSpecToSheaf.obj M).obj.map (homOfLE le_top).op).hom := hloc f
  change IsLocalizedModule.Away f
    ((modulesSpecToSheaf.obj M).obj.map (homOfLE le_top).op).hom
  exact hloc f

private lemma affineFP_sections_finitePresentation
    {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]
    (t : Set R) (ht : Ideal.span t = ⊤)
    (h : ∀ g : t, let U : (Spec R).Opens := PrimeSpectrum.basicOpen g.1
      Module.FinitePresentation
        (Γ(Spec R, U) : Type u) (Γ(M, U) : Type u)) :
    Module.FinitePresentation R ((Γ(M, (⊤ : (Spec R).Opens)) : Type u)) := by
  let U : t → (Spec R).Opens := fun g => PrimeSpectrum.basicOpen g.1
  let F : ∀ g : t, (Γ(M, (⊤ : (Spec R).Opens)) : Type u) →ₗ[R]
      Γ(M, U g) := fun g => affineFP_restrict_map M (U g)
  have hF : ∀ g : t, IsLocalizedModule.Away g.1 (F g) := by
    intro g
    exact affineFP_restrict_loc M g.1
  let (g : t) : IsLocalizedModule.Away g.1 (F g) := hF g
  apply Module.FinitePresentation.of_localizationSpan'
    (M := (Γ(M, (⊤ : (Spec R).Opens)) : Type u))
    (Rₚ := fun g : t => (Γ(Spec R, U g) : Type u))
    (Mₚ := fun g : t => (Γ(M, U g) : Type u)) t ht F
  intro g
  exact h g



private lemma affineFP_basic_iSup_le {R : CommRingCat.{u}}
    (q : TopologicalSpace.Opens (PrimeSpectrum R)) :
    q ≤ ⨆ f : {f : R // PrimeSpectrum.basicOpen f ≤ q},
      PrimeSpectrum.basicOpen f.1 := by
  obtain ⟨Us, hUs, hq⟩ :=
    (Opens.isBasis_iff_cover.mp PrimeSpectrum.isBasis_basic_opens q)
  rw [hq]
  refine sSup_le ?_
  intro U hU
  obtain ⟨f, hf⟩ := hUs hU
  let z : {f : R // PrimeSpectrum.basicOpen f ≤ sSup Us} :=
    ⟨f, by rw [hf]; exact le_sSup hU⟩
  have hle : PrimeSpectrum.basicOpen z.1 ≤
      ⨆ f : {f : R // PrimeSpectrum.basicOpen f ≤ sSup Us}, PrimeSpectrum.basicOpen f.1 :=
    le_iSup (fun f : {f : R // PrimeSpectrum.basicOpen f ≤ sSup Us} =>
      PrimeSpectrum.basicOpen f.1) z
  exact hf ▸ hle


private lemma affineFP_basic_open_presentation
    {R : CommRingCat.{u}} (M : (Spec R).Modules) {I : Type u}
    (X : I → (Spec R).Opens)
    (pres : ∀ i, (M.over (X i)).Presentation)
    (hfin : ∀ i, (pres i).IsFinite)
    (f : R) (i : I) (hfi : PrimeSpectrum.basicOpen f ≤ X i) :
    ∃ P : (M.restrict ((Spec R).basicOpen ((Scheme.ΓSpecIso R).inv f)).ι).Presentation,
      P.IsFinite := by
  let U : (Spec R).Opens := (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv f)
  have hfi' : U ≤ X i := by
    dsimp [U]
    rw [AlgebraicGeometry.basicOpen_eq_of_affine]
    exact hfi
  let : (pres i).IsFinite := hfin i
  let P0 := modulePresentationRestrict (X i) (pres i)
  have hP0 : P0.IsFinite := modulePresentationRestrict_isFinite (X i) (pres i)
  let : P0.IsFinite := hP0
  let : P0.generators.IsFiniteType :=
    SheafOfModules.Presentation.IsFinite.isFiniteType_generators
  let : P0.relations.IsFiniteType :=
    SheafOfModules.Presentation.IsFinite.isFiniteType_relations
  let t := (Spec R).homOfLE (U := U) (V := X i) hfi'
  let P1 := presentationRestrict t P0
  have hP1 : P1.IsFinite := by
    refine { isFiniteType_generators := ?_, isFiniteType_relations := ?_ }
    · dsimp [P1, presentationRestrict]
      constructor
      change Finite P0.generators.I
      exact SheafOfModules.GeneratingSections.IsFiniteType.finite
    · dsimp [P1, presentationRestrict]
      constructor
      change Finite P0.relations.I
      exact SheafOfModules.GeneratingSections.IsFiniteType.finite
  let : P1.IsFinite := hP1
  let : P1.generators.IsFiniteType :=
    SheafOfModules.Presentation.IsFinite.isFiniteType_generators
  let : P1.relations.IsFiniteType :=
    SheafOfModules.Presentation.IsFinite.isFiniteType_relations
  let e : restrictFunctor (X i).ι ⋙ restrictFunctor t ≅
      restrictFunctor U.ι :=
    (restrictFunctorComp t (X i).ι).symm ≪≫
      restrictFunctorCongr (by
        exact Scheme.homOfLE_ι (Spec R) hfi')
  let eM := e.app M
  let P := @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ eM.hom
    (Iso.isIso_hom eM) P1
  have hP : P.IsFinite := by
    refine { isFiniteType_generators := ?_, isFiniteType_relations := ?_ }
    · constructor
      change Finite P1.generators.I
      exact SheafOfModules.GeneratingSections.IsFiniteType.finite
    · constructor
      change Finite P1.relations.I
      exact SheafOfModules.GeneratingSections.IsFiniteType.finite
  exact ⟨P, hP⟩


private lemma affineFP_span_basic_refinement_eq_top {R : CommRingCat.{u}} {I : Type*}
    (X : I → Opens (PrimeSpectrum R)) (hcover : IsOpenCover X) :
    Ideal.span {f : R | ∃ i, PrimeSpectrum.basicOpen f ≤ X i} = ⊤ := by
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp
  apply top_unique
  rw [← hcover.iSup_eq_top]
  refine iSup_le fun i => (affineFP_basic_iSup_le (R := R) (X i)).trans ?_
  refine iSup_le fun f => ?_
  exact le_iSup_of_le f.1 (le_iSup_of_le ⟨i, f.2⟩ le_rfl)


private lemma affineFP_finitePresentation_sections_congr {R : CommRingCat.{u}}
    (M : (Spec R).Modules) {U V : (Spec R).Opens} (hUV : U = V)
    (h : Module.FinitePresentation Γ(Spec R, U) (Γ(M, U) : Type u)) :
    Module.FinitePresentation Γ(Spec R, V) (Γ(M, V) : Type u) := by
  subst V
  exact h

/-- Global sections of a finitely presented module on an affine Noetherian scheme
are finitely presented. -/
lemma moduleSpecΓ_isFinitePresentation
    {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsFinitePresentation] [IsNoetherianRing R] :
    Module.FinitePresentation R (Γ(M, (⊤ : (Spec R).Opens)) : Type u) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  let X : q.I → Opens (PrimeSpectrum R) := q.X
  have hcover : IsOpenCover X := by
    exact (Opens.coversTop_iff _ _).mp q.coversTop
  let t : Set R := {f | ∃ i, PrimeSpectrum.basicOpen f ≤ X i}
  have ht : Ideal.span t = ⊤ := by
    exact affineFP_span_basic_refinement_eq_top X hcover
  let : M.IsQuasicoherent := q.isQuasicoherent
  apply affineFP_sections_finitePresentation M t ht
  intro g
  obtain ⟨i, hi⟩ := g.property
  let U : (Spec R).Opens := (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv g.1)
  obtain ⟨P, hP⟩ := affineFP_basic_open_presentation M X
    (fun j => q.presentation j) (fun j => hq.isFinite_presentation j) g.1 i hi
  let : P.IsFinite := hP
  have hU : IsAffineOpen U := by
    exact (isAffineOpen_top (Spec R)).basicOpen _
  have hfp : Module.FinitePresentation Γ(Spec R, U) (Γ(M, U) : Type u) :=
    affineFP_affine_open_local_fp M U hU P
  apply affineFP_finitePresentation_sections_congr M
    (AlgebraicGeometry.basicOpen_eq_of_affine g.1)
  exact hfp

/-- A finitely presented module on an affine Noetherian spectrum has a finite presentation. -/
lemma presentation_of_spec_isFinitePresentation {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsFinitePresentation] [IsNoetherianRing R] :
    ∃ P : M.Presentation, P.IsFinite := by
  let A : ModuleCat R := moduleSpecΓFunctor.obj M
  let : M.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation M
  let : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let : Module.FinitePresentation R (A : Type u) := by
    exact moduleSpecΓ_isFinitePresentation M (R := R)
  obtain ⟨s, hs, hker⟩ := (inferInstance : Module.FinitePresentation R (A : Type u)).out
  obtain ⟨t, ht⟩ := hker
  let P0 := presentationTilde A (s : Set A) hs (t : Set _) ht
  have hP0 : P0.IsFinite := by
    refine { isFiniteType_generators := ?_, isFiniteType_relations := ?_ }
    · constructor
      change Finite s
      infer_instance
    · constructor
      change Finite t
      infer_instance
  let e : tilde A ≅ M := by
    change tilde (moduleSpecΓFunctor.obj M) ≅ M
    exact @asIso _ _ _ _ M.fromTildeΓ
      (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M)
  let : P0.IsFinite := hP0
  let P := modulePresentationOfIso e.symm P0
  exact ⟨P, modulePresentationOfIso_isFinite e.symm P0⟩

/-- A finitely presented module on an affine locally Noetherian scheme has a finite presentation. -/
lemma presentation_of_affine_isFinitePresentation {Z : Scheme.{u}} [IsAffine Z]
    [IsLocallyNoetherian Z] (M : Z.Modules) [M.IsFinitePresentation] :
    ∃ P : M.Presentation, P.IsFinite := by
  let : IsNoetherianRing Γ(Z, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Z⟩
  let N := (Scheme.Modules.pushforward Z.isoSpec.hom).obj M
  have hN : N.IsFinitePresentation := by
    let e := Scheme.Modules.restrictFunctorIsoPullback Z.isoSpec.inv
    have hPB : ((Scheme.Modules.pullback Z.isoSpec.inv).obj M).IsFinitePresentation := inferInstance
    have hR : ((Scheme.Modules.restrictFunctor Z.isoSpec.inv).obj M).IsFinitePresentation :=
      (SheafOfModules.isFinitePresentation (Spec Γ(Z, ⊤)).ringCatSheaf).prop_of_iso
        (e.symm.app M) hPB
    exact (SheafOfModules.isFinitePresentation (Spec Γ(Z, ⊤)).ringCatSheaf).prop_of_iso
      ((modulePushforwardIsoRestrict Z.isoSpec).app M).symm hR
  let : N.IsFinitePresentation := hN
  obtain ⟨PN, hPN⟩ := presentation_of_spec_isFinitePresentation N
  let : PN.IsFinite := hPN
  let PB := modulePresentationPullback Z.isoSpec.hom PN
  have hPB : PB.IsFinite := modulePresentationPullback_isFinite Z.isoSpec.hom PN
  let eR := (Scheme.Modules.restrictFunctorIsoPullback Z.isoSpec.hom).app N
  let eC := (Scheme.Modules.restrictFunctorAdjCounitIso Z.isoSpec.hom).app M
  let e : (Scheme.Modules.pullback Z.isoSpec.hom).obj N ≅ M := eR.symm ≪≫ eC
  let P := modulePresentationOfIso e.symm PB
  have hP : P.IsFinite := by
    let : PB.IsFinite := hPB
    exact modulePresentationOfIso_isFinite e.symm PB
  exact ⟨P, hP⟩

end GromovWitten.AlgebraicGeometry.Curves
