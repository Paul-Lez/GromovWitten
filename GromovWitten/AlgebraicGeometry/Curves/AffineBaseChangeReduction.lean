/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChangeTransport
import GromovWitten.AlgebraicGeometry.Curves.QuasiCoherentPushforward

/-!
# Reducing affine base change to spectra

Transport through the canonical affine scheme isomorphisms reduces an affine square to spectra.
Compatible affine neighborhoods on both bases, open base change, and horizontal pasting then
reduce arbitrary affine morphisms to squares in which all four schemes are affine.
-/

open CategoryTheory Limits TopologicalSpace
open _root_.AlgebraicGeometry
namespace GromovWitten.AlgebraicGeometry.Curves
universe u
noncomputable section
section Affine
variable {X S T Z : Scheme.{u}} [IsAffine X] [IsAffine S] [IsAffine T] [IsAffine Z]

omit [IsAffine X] [IsAffine S] [IsAffine T] [IsAffine Z] in
private lemma moduleBaseChange_isIso_of_map_eq
    (f f' : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g g' : Z ⟶ T)
    (h' : IsPullback p g' f' b)
    (hf : f' = f) (hg : g' = g)
    (N : X.Modules)
    (hSpec : ∀ (h : IsPullback p g f b),
      IsIso ((modulePushforwardBaseChangeNatTrans f b p g h).app N)) :
    IsIso ((modulePushforwardBaseChangeNatTrans f' b p g' h').app N) := by
  subst f'
  subst g'
  exact hSpec h'

set_option backward.isDefEq.respectTransparency false in
/-- It suffices to prove affine base change after identifying schemes with spectra. -/
lemma moduleBaseChange_isIso_of_isoSpec
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b)
    (hSpec : ∀ (h' : IsPullback (Spec.map p.appTop) (Spec.map g.appTop)
        (Spec.map f.appTop) (Spec.map b.appTop))
      (N : (Spec (X.presheaf.obj (.op ⊤))).Modules), N.IsQuasicoherent →
      IsIso ((modulePushforwardBaseChangeNatTrans (Spec.map f.appTop) (Spec.map b.appTop)
        (Spec.map p.appTop) (Spec.map g.appTop) h').app N))
    (M : X.Modules) [M.IsQuasicoherent] :
    IsIso ((modulePushforwardBaseChangeNatTrans f b p g h).app M) := by
  have hT : IsPullback Z.isoSpec.inv (Spec.map g.appTop) g T.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨(Scheme.isoSpec_inv_naturality g).symm⟩
  apply (moduleBaseChange_paste_isIso_iff_of_isIso f b p g
    T.isoSpec.inv Z.isoSpec.inv (Spec.map g.appTop) h hT M).mp
  let hA := hT.paste_horiz h
  have hX : IsPullback (Spec.map p.appTop) (𝟙 _)
      X.isoSpec.inv (Z.isoSpec.inv ≫ p) :=
    IsPullback.of_vert_isIso ⟨by simpa using Scheme.isoSpec_inv_naturality p⟩
  let N := (Scheme.Modules.pullback X.isoSpec.inv).obj M
  have hN : N.IsQuasicoherent := inferInstance
  let e : M ≅ (Scheme.Modules.pushforward X.isoSpec.inv).obj N :=
    asIso ((Scheme.Modules.pullbackPushforwardAdjunction X.isoSpec.inv).unit.app M)
  apply (NatTrans.isIso_app_iff_of_iso
    (modulePushforwardBaseChangeNatTrans f (T.isoSpec.inv ≫ b)
      (Z.isoSpec.inv ≫ p) (Spec.map g.appTop) hA) e).mpr
  apply (moduleBaseChange_vertical_paste_isIso_iff_of_isIso_first X.isoSpec.inv f
    (T.isoSpec.inv ≫ b) (Z.isoSpec.inv ≫ p) (Spec.map g.appTop)
    (Spec.map p.appTop) (𝟙 _) hX hA N).mp
  let hB := hX.paste_vert hA
  have hS : IsPullback (T.isoSpec.inv ≫ b) (𝟙 _)
      S.isoSpec.hom (Spec.map b.appTop) := by
    apply IsPullback.of_vert_isIso
    constructor
    calc
      T.isoSpec.inv ≫ b ≫ S.isoSpec.hom =
          T.isoSpec.inv ≫ (b ≫ S.isoSpec.hom) := rfl
      _ = T.isoSpec.inv ≫ (T.isoSpec.hom ≫ Spec.map b.appTop) := by
        rw [Scheme.isoSpec_hom_naturality b]
      _ = Spec.map b.appTop := by simp
  apply (moduleBaseChange_vertical_paste_isIso_iff_of_isIso (X.isoSpec.inv ≫ f)
    S.isoSpec.hom (Spec.map b.appTop) (T.isoSpec.inv ≫ b) (𝟙 _)
    (Spec.map p.appTop) (𝟙 _ ≫ Spec.map g.appTop) hB hS N).mp
  have hf : (X.isoSpec.inv ≫ f) ≫ S.isoSpec.hom = Spec.map f.appTop := by
    calc
      (X.isoSpec.inv ≫ f) ≫ S.isoSpec.hom =
          X.isoSpec.inv ≫ (f ≫ S.isoSpec.hom) := Category.assoc _ _ _
      _ = X.isoSpec.inv ≫ (X.isoSpec.hom ≫ Spec.map f.appTop) := by
        rw [Scheme.isoSpec_hom_naturality f]
      _ = Spec.map f.appTop := by simp
  have hg : (𝟙 _ ≫ Spec.map g.appTop) ≫ 𝟙 _ = Spec.map g.appTop := by simp
  exact moduleBaseChange_isIso_of_map_eq _ _ _ _ _ _ (hB.paste_vert hS) hf hg N
    (fun h' => hSpec h' N hN)
end Affine

private lemma moduleBaseChange_paste_congr_isIso {X S T Z V W : Scheme.{u}}
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (c : V ⟶ T) (q : W ⟶ Z) (k : W ⟶ V)
    (h₁ : IsPullback p g f b) (h₂ : IsPullback q k g c)
    (b' : V ⟶ S) (p' : W ⟶ X) (hb : c ≫ b = b') (hp : q ≫ p = p')
    (h' : IsPullback p' k f b') (M : X.Modules)
    [IsIso ((modulePushforwardBaseChangeNatTrans f b p g h₁).app M)]
    [IsIso ((modulePushforwardBaseChangeNatTrans g c q k h₂).app
      ((Scheme.Modules.pullback p).obj M))] :
    IsIso ((modulePushforwardBaseChangeNatTrans f b' p' k h').app M) := by
  subst b'
  subst p'
  exact moduleBaseChange_paste_isIso f b p g c q k h₁ h₂ M
set_option backward.isDefEq.respectTransparency false in
/-- Base change for affine morphisms reduces to squares of affine schemes. -/
lemma moduleBaseChange_isIso_of_affine_squares
    (hAffine : ∀ (X S T Z : Scheme.{u}) [IsAffine X] [IsAffine S] [IsAffine T]
      [IsAffine Z] (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
      (h : IsPullback p g f b) (M : X.Modules) [M.IsQuasicoherent],
      IsIso ((modulePushforwardBaseChangeNatTrans f b p g h).app M))
    {X S T Z : Scheme.{u}} (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) [IsAffineHom f] (M : X.Modules) [M.IsQuasicoherent] :
    IsIso ((modulePushforwardBaseChangeNatTrans f b p g h).app M) := by
  apply moduleBaseChange_isIso_of_open_cover f b p g h M
  intro x
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := b x) (by simp)
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (U := b ⁻¹ᵁ U)
    (x := x) hxU
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
  have hWU : g ⁻¹ᵁ V ≤ p ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, h.w, Scheme.Hom.comp_preimage]
    exact g.preimage_mono hVU
  let c := b.resLE U V hVU
  let q := p.resLE (f ⁻¹ᵁ U) (g ⁻¹ᵁ V) hWU
  have h₂ : IsPullback q (g ∣_ V) (f ∣_ U) c := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
      Scheme.Hom.isPullback_resLE h hVU le_rfl (show g ⁻¹ᵁ V =
        p ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ g ⁻¹ᵁ V from (inf_eq_right.mpr hWU).symm)
  have : IsAffine (g ⁻¹ᵁ V).toScheme := .of_isPullback h₂
  have h₁ := (isPullback_morphismRestrict f U).flip
  have : IsIso ((modulePushforwardBaseChangeNatTrans f U.ι (f ⁻¹ᵁ U).ι
      (f ∣_ U) h₁).app M) := moduleBaseChange_open_isIso f U M
  have : IsIso ((modulePushforwardBaseChangeNatTrans (f ∣_ U) c q (g ∣_ V) h₂).app
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M)) := hAffine _ _ _ _ _ _ _ _ _ _
  refine ⟨V, hxV, ?_⟩
  exact moduleBaseChange_paste_congr_isIso f U.ι (f ⁻¹ᵁ U).ι (f ∣_ U)
    c q (g ∣_ V) h₁ h₂ (V.ι ≫ b) ((g ⁻¹ᵁ V).ι ≫ p)
    (b.resLE_comp_ι hVU) (p.resLE_comp_ι hWU)
    ((isPullback_morphismRestrict g V).flip.paste_horiz h) M

end
end GromovWitten.AlgebraicGeometry.Curves
