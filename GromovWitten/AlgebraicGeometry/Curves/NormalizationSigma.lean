/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import Mathlib.AlgebraicGeometry.Normalization

/-!
# Relative normalization of finite coproducts

A finite coproduct of integral morphisms is integral. Applying this fact to the universal
property of normalization identifies normalization of a finite coproduct with the coproduct
of the relative normalizations of its summands, including an empty index type.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Hom

private lemma integral_sigma_desc_fin (X : Scheme.{u}) :
    ∀ (n : ℕ) (Y : Fin n → Scheme.{u}) (g : ∀ i, Y i ⟶ X),
      (∀ i, IsIntegralHom (g i)) → IsIntegralHom (Sigma.desc g)
  | 0, Y, g, hg => by
      let c₀ : Cofan Y := Cofan.mk (⊥_ Scheme.{u}) (fun i => i.elim0)
      have h₀ : IsColimit c₀ := by
        refine ⟨fun s => initial.to s.pt, ?_, ?_⟩
        · intro s i
          exact i.as.elim0
        · intro s m hm
          exact initial.hom_ext _ _
      let e : (⊥_ Scheme.{u}) ≅ ∐ Y :=
        h₀.coconePointUniqueUpToIso (coproductIsCoproduct Y)
      have he : e.hom ≫ Sigma.desc g = initial.to X := initial.hom_ext _ _
      have he' : Sigma.desc g = e.inv ≫ initial.to X := by
        apply (cancel_epi e.hom).1
        simp [he]
      rw [he']
      infer_instance
  | n + 1, Y, g, hg => by
      let Y₁ : Fin n → Scheme.{u} := fun i => Y i.succ
      let g₁ : ∀ i, Y₁ i ⟶ X := fun i => g i.succ
      have hg₁ : ∀ i, IsIntegralHom (g₁ i) := fun i => hg i.succ
      have hi₁ : IsIntegralHom (Sigma.desc g₁) :=
        integral_sigma_desc_fin X n Y₁ g₁ hg₁
      let c₁ : Cofan (fun i : Fin n => Y i.succ) :=
        Cofan.mk (∐ Y₁) (Sigma.ι Y₁)
      let c₂ : BinaryCofan (Y 0) c₁.pt :=
        BinaryCofan.mk coprod.inl coprod.inr
      let h₁ : IsColimit c₁ := coproductIsCoproduct Y₁
      let h₂ : IsColimit c₂ := coprodIsCoprod _ _
      let h : IsColimit (extendCofan c₁ c₂) := extendCofanIsColimit Y h₁ h₂
      let e : (Y 0 ⨿ ∐ Y₁) ≅ ∐ Y :=
        h.coconePointUniqueUpToIso (coproductIsCoproduct Y)
      let g₂ : (Y 0 ⨿ ∐ Y₁) ⟶ X := coprod.desc (g 0) (Sigma.desc g₁)
      have hi₂ : IsIntegralHom g₂ := by infer_instance
      have he : e.hom ≫ Sigma.desc g = g₂ := by
        apply coprod.hom_ext
        · have H := h.comp_coconePointUniqueUpToIso_hom
            (coproductIsCoproduct Y) (Discrete.mk 0)
          have H' : coprod.inl ≫ e.hom = Sigma.ι Y 0 := by
            rw [extendCofan_ι_app] at H
            dsimp [c₁, c₂] at H
            change coprod.inl ≫ e.hom = Sigma.ι Y 0 at H
            exact H
          change coprod.inl ≫ e.hom ≫ Sigma.desc g = coprod.inl ≫ g₂
          calc
            _ = (coprod.inl ≫ e.hom) ≫ Sigma.desc g := by simp only [Category.assoc]
            _ = Sigma.ι Y 0 ≫ Sigma.desc g := by rw [H']
            _ = g 0 := by simp
            _ = coprod.inl ≫ g₂ := by
              symm
              exact coprod.inl_desc (g 0) (Sigma.desc g₁)
        · apply (coproductIsCoproduct Y₁).hom_ext
          intro i
          have H := h.comp_coconePointUniqueUpToIso_hom
            (coproductIsCoproduct Y) (Discrete.mk i.as.succ)
          have H' : Sigma.ι Y₁ i.as ≫ coprod.inr ≫ e.hom = Sigma.ι Y i.as.succ := by
            rw [extendCofan_ι_app] at H
            dsimp [c₁, c₂] at H
            change Sigma.ι Y₁ i.as ≫ coprod.inr ≫ e.hom = Sigma.ι Y i.as.succ at H
            exact H
          change Sigma.ι Y₁ i.as ≫ coprod.inr ≫ e.hom ≫ Sigma.desc g =
            Sigma.ι Y₁ i.as ≫ coprod.inr ≫ g₂
          calc
            _ = (Sigma.ι Y₁ i.as ≫ coprod.inr ≫ e.hom) ≫ Sigma.desc g := by
              simp only [Category.assoc]
            _ = Sigma.ι Y i.as.succ ≫ Sigma.desc g := by rw [H']
            _ = g i.as.succ := by simp
            _ = Sigma.ι Y₁ i.as ≫ coprod.inr ≫ g₂ := by
              symm
              change Sigma.ι Y₁ i.as ≫
                (coprod.inr ≫ coprod.desc (g 0) (Sigma.desc g₁)) = g i.as.succ
              rw [coprod.inr_desc]
              exact Sigma.ι_desc g₁ i.as
      have he' : Sigma.desc g = e.inv ≫ g₂ := by
        apply (cancel_epi e.hom).1
        simp [he]
      rw [he']
      infer_instance

private lemma integral_sigma_desc_finite {ι : Type v} [Small.{u, v} ι] [Finite ι]
    (X : Scheme.{u}) (Y : ι → Scheme.{u}) (g : ∀ i, Y i ⟶ X)
    (hg : ∀ i, IsIntegralHom (g i)) : IsIntegralHom (Sigma.desc g) := by
  let _ : Fintype ι := Fintype.ofFinite _
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let Y' : Fin (Fintype.card ι) → Scheme.{u} := Y ∘ e.symm
  let g' : ∀ i, Y' i ⟶ X := fun i => g (e.symm i)
  have hg' : ∀ i, IsIntegralHom (g' i) := fun i => hg (e.symm i)
  have hi' : IsIntegralHom (Sigma.desc g') :=
    integral_sigma_desc_fin X (Fintype.card ι) Y' g' hg'
  let r : (∐ Y') ≅ ∐ Y := Sigma.reindex e.symm Y
  have hr : r.hom ≫ Sigma.desc g = Sigma.desc g' := by
    apply Sigma.hom_ext
    intro i
    simp [r, Y', g', e]
  have he : Sigma.desc g = r.inv ≫ Sigma.desc g' := by
    apply (cancel_epi r.hom).1
    simp [hr]
  rw [he]
  infer_instance

section GenericFinite

variable {ι : Type v} [Small.{u, v} ι] [Finite ι]
variable {S : ι → Scheme.{u}} {X : Scheme.{u}}
variable (f : (∐ S) ⟶ X) [QuasiCompact f] [QuasiSeparated f]
variable [∀ i, QuasiCompact (Sigma.ι S i ≫ f)]
variable [∀ i, QuasiSeparated (Sigma.ι S i ≫ f)]

private noncomputable def sigmaToNormalization : (∐ S) ⟶
    ∐ fun i => (Sigma.ι S i ≫ f).normalization :=
  Sigma.desc fun i => (Sigma.ι S i ≫ f).toNormalization ≫
    Sigma.ι (fun i => (Sigma.ι S i ≫ f).normalization) i

private noncomputable def sigmaFromNormalization :
    (∐ fun i => (Sigma.ι S i ≫ f).normalization) ⟶ X :=
  Sigma.desc fun i => (Sigma.ι S i ≫ f).fromNormalization

omit [Finite ι] [QuasiCompact f] [QuasiSeparated f] in
private lemma sigmaNormalization_factorization :
    f = sigmaToNormalization f ≫ sigmaFromNormalization f := by
  apply Sigma.hom_ext
  intro i
  simp [sigmaToNormalization, sigmaFromNormalization]

private instance : IsIntegralHom (sigmaFromNormalization f) := by
  apply integral_sigma_desc_finite X
  intro i
  infer_instance

/-- The normalization of a finite coproduct is the coproduct of the relative
normalizations of its summands. -/
noncomputable def normalizationSigmaIso :
    (∐ fun i => (Sigma.ι S i ≫ f).normalization) ≅ f.normalization where
  hom := Sigma.desc fun i =>
    (Sigma.ι S i ≫ f).normalizationDesc
      (Sigma.ι S i ≫ f.toNormalization) f.fromNormalization (by simp)
  inv := f.normalizationDesc (sigmaToNormalization f) (sigmaFromNormalization f)
    (sigmaNormalization_factorization f)
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    refine Scheme.Hom.normalization.hom_ext (Sigma.ι S i ≫ f) _ _
      (sigmaFromNormalization f) ?_ (by simp [sigmaFromNormalization])
      (by simp [sigmaFromNormalization])
    simp [sigmaToNormalization, sigmaFromNormalization]
  inv_hom_id := by
    refine Scheme.Hom.normalization.hom_ext f _ _ f.fromNormalization ?_
      ?_ (by simp)
    · apply Sigma.hom_ext
      intro i
      simp [sigmaToNormalization]
    · have hh :
          (Sigma.desc (fun i =>
            (Sigma.ι S i ≫ f).normalizationDesc
              (Sigma.ι S i ≫ f.toNormalization) f.fromNormalization (by simp))) ≫
            f.fromNormalization = sigmaFromNormalization f := by
        apply Sigma.hom_ext
        intro i
        dsimp [sigmaFromNormalization]
        rw [← Category.assoc, Sigma.ι_desc, normalizationDesc_comp, Sigma.ι_desc]
      rw [Category.assoc, hh]
      exact normalizationDesc_comp _ _ _ (sigmaNormalization_factorization f)

@[reassoc (attr := simp)]
lemma toNormalization_sigma_ι_normalizationSigmaIso_hom (i : ι) :
    (Sigma.ι S i ≫ f).toNormalization ≫ Sigma.ι
        (fun i => (Sigma.ι S i ≫ f).normalization) i ≫
        (normalizationSigmaIso f).hom =
      Sigma.ι S i ≫ f.toNormalization := by
  simp [normalizationSigmaIso]

@[reassoc (attr := simp)]
lemma sigma_ι_normalizationSigmaIso_hom_fromNormalization (i : ι) :
    Sigma.ι (fun i => (Sigma.ι S i ≫ f).normalization) i ≫
        (normalizationSigmaIso f).hom ≫ f.fromNormalization =
      (Sigma.ι S i ≫ f).fromNormalization := by
  simp [normalizationSigmaIso]

@[simp]
lemma normalizationSigmaIso_inv_sigmaFromNormalization :
    (normalizationSigmaIso f).inv ≫ sigmaFromNormalization f = f.fromNormalization := by
  simp [normalizationSigmaIso, sigmaFromNormalization]

end GenericFinite

end AlgebraicGeometry.Scheme.Hom
