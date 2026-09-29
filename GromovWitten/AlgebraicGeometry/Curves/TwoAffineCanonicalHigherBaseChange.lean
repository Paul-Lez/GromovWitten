/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.TwoAffineHigherVanishing
import GromovWitten.AlgebraicGeometry.Curves.RelativeCechDerived
import GromovWitten.AlgebraicGeometry.Curves.RelativeCechComplexBaseChange
import GromovWitten.AlgebraicGeometry.Curves.RelativeOpenAffineBaseChange
import GromovWitten.AlgebraicGeometry.Curves.HigherBaseChange
import GromovWitten.CategoryTheory.ShortComplexKernelComparison

/-!
# Canonical higher base change for a two-affine cover

For a two-affine cover, the relative Cech comparison proves the canonical flat
higher base-change map in degrees zero and one.  Together with the higher
vanishing theorem, this gives the all-degree result under the explicit
quasicoherence, affine-overlap, and locally Noetherian hypotheses below; the
degree-zero comparison itself does not require Noetherian hypotheses.
-/

open CategoryTheory Limits TopologicalSpace
open _root_.AlgebraicGeometry
open HomologicalComplex
open Scheme.Modules
open GromovWitten.AlgebraicGeometry.SheafCohomology
noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X S T Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The canonical flat higher-base-change map is an isomorphism in degrees
`n + 2` for a two-affine cover of the source. -/
theorem moduleFlatHigherBaseChange_twoAffineCover_isIso
    (f : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g f b) [Flat b]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [IsAffineHom (U.ι ≫ f)] [IsAffineHom (V.ι ≫ f)]
    [IsAffineHom ((U ⊓ V).ι ≫ f)]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsIso ((moduleFlatHigherBaseChangeNatTrans f b p g h (n + 2)).app M) := by
  let hU := (isPullback_morphismRestrict p U).paste_vert h
  let hV := (isPullback_morphismRestrict p V).paste_vert h
  let hI := (isPullback_morphismRestrict p (U ⊓ V)).paste_vert h
  let _ : IsAffineHom ((p ⁻¹ᵁ U).ι ≫ g) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hU inferInstance
  let _ : IsAffineHom ((p ⁻¹ᵁ V).ι ≫ g) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hV inferInstance
  let _ : IsAffineHom (((p ⁻¹ᵁ U) ⊓ (p ⁻¹ᵁ V)).ι ≫ g) := by
    rw [← Scheme.Hom.preimage_inf]
    exact MorphismProperty.of_isPullback (P := @IsAffineHom) hI inferInstance
  have hcover' : (p ⁻¹ᵁ U) ⊔ (p ⁻¹ᵁ V) = ⊤ := by
    change p ⁻¹ᵁ (U ⊔ V) = ⊤
    rw [hcover]
    rfl
  have hsource : IsZero (higherDirectImageModule f M (n + 2)) :=
    isZero_higherDirectImageModule_twoAffineCover f U V hcover M n
  have htarget : IsZero (higherDirectImageModule g
      ((Scheme.Modules.pullback p).obj M) (n + 2)) :=
    isZero_higherDirectImageModule_twoAffineCover g (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)
      hcover' ((Scheme.Modules.pullback p).obj M) n
  exact (Scheme.Modules.pullback b).map_isZero hsource |>.isIso htarget
    ((moduleFlatHigherBaseChangeNatTrans f b p g h (n + 2)).app M)

set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero canonical base change is invertible for a two-affine cover. -/
lemma moduleHigherBaseChange_zero_isIso_of_twoAffine
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b)
    [(Scheme.Modules.pullback b).PreservesHomology]
    [(Scheme.Modules.pullback p).PreservesHomology]
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [IsAffineHom (U.ι ≫ s)] [IsAffineHom (V.ι ≫ s)]
    [IsAffineHom ((U ⊓ V).ι ≫ s)] :
    IsIso ((moduleHigherBaseChangeNatTrans s b p g h 0).app M) := by
  let F := Scheme.Modules.pullback b
  have : PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  have : PreservesFiniteColimits F := F.preservesFiniteColimits_of_preservesHomology
  let L := Scheme.Modules.pullback p
  let I := injectiveResolution M
  let J := injectiveResolution (L.obj M)
  let Up := p ⁻¹ᵁ U
  let Vp := p ⁻¹ᵁ V
  have hcover' : Up ⊔ Vp = ⊤ := by
    dsimp only [Up, Vp]
    rw [← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]
  let a : (CochainComplex.single₀ Y.Modules).obj (L.obj M) ⟶
      (L.mapHomologicalComplex (.up ℕ)).obj I.cocomplex :=
    (singleMapHomologicalComplex L (.up ℕ) 0).inv.app M ≫
      (L.mapHomologicalComplex (.up ℕ)).map I.ι
  have : QuasiIso a := by dsimp only [a]; infer_instance
  obtain ⟨φ, hφ, _⟩ := J.exists_desc_of_quasiIso a
  have hφ' : (singleMapHomologicalComplex L (.up ℕ) 0).inv.app M ≫
      (L.mapHomologicalComplex (.up ℕ)).map I.ι ≫ φ = J.ι := by
    simpa only [a, Category.assoc] using hφ
  let CS := relativeCechComplexMV I.cocomplex s U V
  let CT := relativeCechComplexMV J.cocomplex g Up Vp
  have hs : CS.ShortExact := relativeCechComplexMV_shortExact I.cocomplex s U V hcover
    (fun n => module_isFlasque_of_injective (I.cocomplex.X n))
  have ht : CT.ShortExact := relativeCechComplexMV_shortExact J.cocomplex g Up Vp hcover'
    (fun n => module_isFlasque_of_injective (J.cocomplex.X n))
  let Φ : CS.map (F.mapHomologicalComplex (.up ℕ)) ⟶ CT :=
    relativeCechComplexBaseChange I.cocomplex s b p g h U V ≫
      relativeCechComplexMVMap φ g Up Vp
  have hsF : (CS.map (F.mapHomologicalComplex (.up ℕ))).ShortExact :=
    hs.map_of_exact (F.mapHomologicalComplex (.up ℕ))
  have : IsIso ((relativeOpenBaseChangeNatTrans s b p g h.w U).app M) :=
    relativeOpenBaseChangeNatTrans_isIso s b p g h U M
  have : IsIso ((relativeOpenBaseChangeNatTrans s b p g h.w V).app M) :=
    relativeOpenBaseChangeNatTrans_isIso s b p g h V M
  have : IsIso ((relativeOpenBaseChangeNatTrans s b p g h.w (U ⊓ V)).app M) :=
    relativeOpenBaseChangeNatTrans_isIso s b p g h (U ⊓ V) M
  have : IsIso ((relativeCechPairBaseChangeNatTrans s b p g h.w U V).app M) :=
    relativeCechPairBaseChangeNatTrans_isIso s b p g h.w U V M
  have : IsIso (HomologicalComplex.homologyMap Φ.τ₂ 0) :=
    NatTrans.baseChange_homologyMap_zero_isIso
      (relativeCechPairBaseChangeNatTrans s b p g h.w U V) M φ hφ'
  have : IsIso (HomologicalComplex.homologyMap Φ.τ₃ 0) :=
    NatTrans.baseChange_homologyMap_zero_isIso
      (relativeOpenBaseChangeNatTrans s b p g h.w (U ⊓ V)) M φ hφ'
  have : Mono (CS.map (F.mapHomologicalComplex (.up ℕ))).f := hsF.mono_f
  have : Mono CT.f := ht.mono_f
  have : Mono (HomologicalComplex.homologyMap
      (CS.map (F.mapHomologicalComplex (.up ℕ))).f 0) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel _ 0
      (by intro i hi; change i + 1 = 0 at hi; omega)
  have : Mono (HomologicalComplex.homologyMap CT.f 0) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel _ 0
      (by intro i hi; change i + 1 = 0 at hi; omega)
  let H₀ := HomologicalComplex.homologyFunctor T.Modules (.up ℕ) 0
  have : Mono (H₀.mapShortComplex.obj
      (CS.map (F.mapHomologicalComplex (.up ℕ)))).f := by
    change Mono (HomologicalComplex.homologyMap
      (CS.map (F.mapHomologicalComplex (.up ℕ))).f 0)
    infer_instance
  have : Mono (H₀.mapShortComplex.obj CT).f := by
    change Mono (HomologicalComplex.homologyMap CT.f 0)
    infer_instance
  have : IsIso (H₀.mapShortComplex.map Φ).τ₂ := by
    change IsIso (HomologicalComplex.homologyMap Φ.τ₂ 0)
    infer_instance
  have : Mono (H₀.mapShortComplex.map Φ).τ₃ := by
    change Mono (HomologicalComplex.homologyMap Φ.τ₃ 0)
    infer_instance
  have h₀ := ShortComplex.isIso_τ₁_of_exact_of_mono_f
    (H₀.mapShortComplex.map Φ)
    (hsF.homology_exact₂ 0)
  exact (NatTrans.rightDerivedBaseChange_isIso_iff
    (modulePushforwardBaseChangeNatTrans s b p g h) M 0 φ hφ').mpr h₀

set_option backward.isDefEq.respectTransparency false in
/-- Degree-one canonical base change is invertible for a two-affine cover when
`X` and `Y` are locally Noetherian and the coefficients are quasicoherent. -/
lemma moduleHigherBaseChange_one_isIso_of_twoAffine
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b)
    [(Scheme.Modules.pullback b).PreservesHomology]
    [(Scheme.Modules.pullback p).PreservesHomology]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [IsAffineHom (U.ι ≫ s)] [IsAffineHom (V.ι ≫ s)]
    [IsAffineHom ((U ⊓ V).ι ≫ s)] :
    IsIso ((moduleHigherBaseChangeNatTrans s b p g h 1).app M) := by
  let F := Scheme.Modules.pullback b
  have : PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  have : PreservesFiniteColimits F := F.preservesFiniteColimits_of_preservesHomology
  let L := Scheme.Modules.pullback p
  let I := injectiveResolution M
  let J := injectiveResolution (L.obj M)
  let Up := p ⁻¹ᵁ U
  let Vp := p ⁻¹ᵁ V
  have : IsAffineHom (Up.ι ≫ g) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      ((isPullback_morphismRestrict p U).paste_vert h) inferInstance
  have : IsAffineHom (Vp.ι ≫ g) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      ((isPullback_morphismRestrict p V).paste_vert h) inferInstance
  have hcover' : Up ⊔ Vp = ⊤ := by
    dsimp only [Up, Vp]
    rw [← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]
  let a : (CochainComplex.single₀ Y.Modules).obj (L.obj M) ⟶
      (L.mapHomologicalComplex (.up ℕ)).obj I.cocomplex :=
    (singleMapHomologicalComplex L (.up ℕ) 0).inv.app M ≫
      (L.mapHomologicalComplex (.up ℕ)).map I.ι
  have : QuasiIso a := by dsimp only [a]; infer_instance
  obtain ⟨φ, hφ, _⟩ := J.exists_desc_of_quasiIso a
  have hφ' : (singleMapHomologicalComplex L (.up ℕ) 0).inv.app M ≫
      (L.mapHomologicalComplex (.up ℕ)).map I.ι ≫ φ = J.ι := by
    simpa only [a, Category.assoc] using hφ
  let CS := relativeCechComplexMV I.cocomplex s U V
  let CT := relativeCechComplexMV J.cocomplex g Up Vp
  have hs : CS.ShortExact := relativeCechComplexMV_shortExact I.cocomplex s U V hcover
    (fun n => module_isFlasque_of_injective (I.cocomplex.X n))
  have ht : CT.ShortExact := relativeCechComplexMV_shortExact J.cocomplex g Up Vp hcover'
    (fun n => module_isFlasque_of_injective (J.cocomplex.X n))
  let Φ : CS.map (F.mapHomologicalComplex (.up ℕ)) ⟶ CT :=
    relativeCechComplexBaseChange I.cocomplex s b p g h U V ≫
      relativeCechComplexMVMap φ g Up Vp
  have hsF : (CS.map (F.mapHomologicalComplex (.up ℕ))).ShortExact :=
    hs.map_of_exact (F.mapHomologicalComplex (.up ℕ))
  have hzS : IsZero (((F.mapHomologicalComplex (.up ℕ)).obj CS.X₂).homology 1) :=
    (F.map_isZero (isZero_relativeCechPair_homology_one I s U V)).of_iso
      ((CS.X₂.sc 1).mapHomologyIso F)
  have hzT : IsZero (CT.X₂.homology 1) := isZero_relativeCechPair_homology_one J g Up Vp
  have : IsIso ((relativeOpenBaseChangeNatTrans s b p g h.w U).app M) :=
    relativeOpenBaseChangeNatTrans_isIso s b p g h U M
  have : IsIso ((relativeOpenBaseChangeNatTrans s b p g h.w V).app M) :=
    relativeOpenBaseChangeNatTrans_isIso s b p g h V M
  have : IsIso ((relativeOpenBaseChangeNatTrans s b p g h.w (U ⊓ V)).app M) :=
    relativeOpenBaseChangeNatTrans_isIso s b p g h (U ⊓ V) M
  have : IsIso ((relativeCechPairBaseChangeNatTrans s b p g h.w U V).app M) :=
    relativeCechPairBaseChangeNatTrans_isIso s b p g h.w U V M
  have : IsIso (HomologicalComplex.homologyMap Φ.τ₂ 0) :=
    NatTrans.baseChange_homologyMap_zero_isIso
      (relativeCechPairBaseChangeNatTrans s b p g h.w U V) M φ hφ'
  have : IsIso (HomologicalComplex.homologyMap Φ.τ₃ 0) :=
    NatTrans.baseChange_homologyMap_zero_isIso
      (relativeOpenBaseChangeNatTrans s b p g h.w (U ⊓ V)) M φ hφ'
  have h₁ := ShortComplex.ShortExact.homologyMap_isIso_of_isZero_middle
    Φ 0 1 rfl hsF ht hzS hzT
  exact (NatTrans.rightDerivedBaseChange_isIso_iff
    (modulePushforwardBaseChangeNatTrans s b p g h) M 1 φ hφ').mpr h₁

/-- The degree-one flat comparison is invertible under the same two-affine
cover hypotheses. -/
theorem moduleFlatHigherBaseChange_one_isIso_of_twoAffine
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b) [Flat b]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [IsAffineHom (U.ι ≫ s)] [IsAffineHom (V.ι ≫ s)]
    [IsAffineHom ((U ⊓ V).ι ≫ s)] :
    IsIso ((moduleFlatHigherBaseChangeNatTrans s b p g h 1).app M) := by
  let _ : Flat p := MorphismProperty.of_isPullback (P := @Flat) h.flip inferInstance
  exact moduleHigherBaseChange_one_isIso_of_twoAffine s b p g h M U V hcover

/-- Degree-zero flat base change is invertible for a two-affine cover. -/
theorem moduleFlatHigherBaseChange_zero_isIso_of_twoAffine
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b) [Flat b]
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [IsAffineHom (U.ι ≫ s)] [IsAffineHom (V.ι ≫ s)]
    [IsAffineHom ((U ⊓ V).ι ≫ s)] :
    IsIso ((moduleFlatHigherBaseChangeNatTrans s b p g h 0).app M) := by
  let _ : Flat p := MorphismProperty.of_isPullback (P := @Flat) h.flip inferInstance
  exact moduleHigherBaseChange_zero_isIso_of_twoAffine s b p g h M U V hcover

/-- Flat higher base change is invertible in every degree for a two-affine cover. -/
theorem moduleFlatHigherBaseChange_isIso_of_twoAffine
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b) [Flat b]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [IsAffineHom (U.ι ≫ s)] [IsAffineHom (V.ι ≫ s)]
    [IsAffineHom ((U ⊓ V).ι ≫ s)] (n : ℕ) :
    IsIso ((moduleFlatHigherBaseChangeNatTrans s b p g h n).app M) := by
  cases n with
  | zero =>
      exact moduleFlatHigherBaseChange_zero_isIso_of_twoAffine
        s b p g h M U V hcover
  | succ n =>
      cases n with
      | zero =>
          exact moduleFlatHigherBaseChange_one_isIso_of_twoAffine
            s b p g h M U V hcover
      | succ n =>
          exact moduleFlatHigherBaseChange_twoAffineCover_isIso
            s b p g h U V hcover M n

end GromovWitten.AlgebraicGeometry.Curves
