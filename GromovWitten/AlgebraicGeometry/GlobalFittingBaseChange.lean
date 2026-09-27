/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import GromovWitten.AlgebraicGeometry.GlobalFittingIdeals
import GromovWitten.AlgebraicGeometry.Curves.CartierDivisors
/-!
# Base change and étale restriction of differential Fitting ideals

The global relative differential Fitting ideal commutes with arbitrary cartesian
base change and with étale restriction of the source. The proofs compute on
adapted affine pairs; cartesian affine sections form a pushout of rings.
-/

open CategoryTheory Opposite Limits
open AlgebraicGeometry
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.RelativeFittingLocus
variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {g : X' ⟶ X} {b : Y' ⟶ Y}
/-- Differential Fitting ideals commute with base change on affine pullback opens. -/
lemma idealOnPair_baseChange (H : IsPullback g f' f b)
    [LocallyOfFinitePresentation f] (i : ℕ)
    (U : Y.affineOpens) (U' : Y'.affineOpens) (V : X.affineOpens) (W : X'.affineOpens)
    (hU : U'.1 ≤ b ⁻¹ᵁ U.1) (hV : V.1 ≤ f ⁻¹ᵁ U.1)
    (hW : W.1 = g ⁻¹ᵁ V.1 ⊓ f' ⁻¹ᵁ U'.1) :
    idealOnPair f' i U' W (by rw [hW]; exact inf_le_right) =
      (idealOnPair f i U V hV).map
        (g.appLE V.1 W.1 (by rw [hW]; exact inf_le_left)).hom := by
  let iRS := pairAlgebra b U U' hU
  let iRA := pairAlgebra f U V hV
  let iSB := pairAlgebra f' U' W (by rw [hW]; exact inf_le_right)
  let iAB := pairAlgebra g V W (by rw [hW]; exact inf_le_left)
  let iRB : Algebra Γ(Y, U.1) Γ(X', W.1) :=
    ((f.appLE U.1 V.1 hV) ≫
      g.appLE V.1 W.1 (by rw [hW]; exact inf_le_left)).hom.toAlgebra
  have htA : IsScalarTower Γ(Y, U.1) Γ(X, V.1) Γ(X', W.1) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have htS : IsScalarTower Γ(Y, U.1) Γ(Y', U'.1) Γ(X', W.1) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((f.appLE U.1 V.1 hV) ≫ g.appLE V.1 W.1 _).hom =
      ((b.appLE U.1 U'.1 hU) ≫ f'.appLE U'.1 W.1 _).hom
    congr 1
    simp only [Scheme.Hom.appLE_comp_appLE, H.w]
  have hfp : _root_.Algebra.FinitePresentation Γ(Y, U.1) Γ(X, V.1) :=
    f.finitePresentation_appLE U.2 V.2 hV
  have hp := (isIso_pushoutSection_iff H hU hV hW).mp
    (isIso_pushoutSection_of_isAffineOpen H hU hV hW U.2 U'.2 V.2)
  have hpush : _root_.Algebra.IsPushout Γ(Y, U.1) Γ(Y', U'.1) Γ(X, V.1) Γ(X', W.1) :=
    CommRingCat.isPushout_iff_isPushout.mp hp.flip
  exact Algebra.differentialFittingIdeal_baseChange
    Γ(Y, U.1) Γ(Y', U'.1) Γ(X, V.1) Γ(X', W.1) i


/-- The global differential Fitting ideal commutes with arbitrary base change. -/
lemma globalIdealSheaf_baseChange (H : IsPullback g f' f b)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation f'] (i : ℕ) :
    globalIdealSheaf f' i = (globalIdealSheaf f i).comap g := by
  apply Scheme.IdealSheafData.ext_of_locally_eq
  intro x
  obtain ⟨⟨U, V⟩, hxV, hV⟩ := exists_affinePair f (g x)
  have hxU : f' x ∈ b ⁻¹ᵁ U.1 := by
    change b (f' x) ∈ U.1
    rw [← Scheme.Hom.comp_apply, ← H.w, Scheme.Hom.comp_apply]
    exact hV hxV
  obtain ⟨_, ⟨U', hU', rfl⟩, hxU', hU⟩ :=
    Y'.isBasis_affineOpens.exists_subset_of_mem_open hxU (b ⁻¹ᵁ U.1).isOpen
  let W := g ⁻¹ᵁ V.1 ⊓ f' ⁻¹ᵁ U'
  have : IsAffine U.1 := U.2
  have : IsAffine V.1 := V.2
  have : IsAffine U' := hU'
  have hW : IsAffineOpen W :=
    .of_isIso (Scheme.Hom.isPullback_resLE H hU hV rfl).isoPullback.hom
  refine ⟨⟨W, hW⟩, ⟨hxV, hxU'⟩, ?_⟩
  calc
    _ = idealOnPair f' i ⟨U', hU'⟩ ⟨W, hW⟩ inf_le_right :=
      globalIdealSheaf_ideal f' i ⟨U', hU'⟩ ⟨W, hW⟩ inf_le_right
    _ = (idealOnPair f i U V hV).map (g.appLE V.1 W inf_le_left).hom :=
      idealOnPair_baseChange H i U ⟨U', hU'⟩ V ⟨W, hW⟩ hU hV rfl
    _ = ((globalIdealSheaf f i).ideal V).map (g.appLE V.1 W inf_le_left).hom :=
      congrArg (Ideal.map (g.appLE V.1 W inf_le_left).hom)
        (globalIdealSheaf_ideal f i U V hV).symm
    _ = ((globalIdealSheaf f i).comap g).ideal ⟨W, hW⟩ :=
      (Curves.idealSheaf_comap_ideal (globalIdealSheaf f i) g V ⟨W, hW⟩ inf_le_left).symm


/-- An étale change of the source extends the affine differential Fitting ideal. -/
lemma idealOnPair_comp_etale {Z : Scheme.{u}} (f : X ⟶ Y) (e : Z ⟶ X)
    [LocallyOfFinitePresentation f] [Etale e] (i : ℕ)
    (U : Y.affineOpens) (V : X.affineOpens) (W : Z.affineOpens)
    (hV : V.1 ≤ f ⁻¹ᵁ U.1) (hW : W.1 ≤ e ⁻¹ᵁ V.1) :
    idealOnPair (e ≫ f) i U W (fun _ hz => hV (hW hz)) =
      (idealOnPair f i U V hV).map (e.appLE V.1 W.1 hW).hom := by
  let iRA := pairAlgebra f U V hV
  let iRB := pairAlgebra (e ≫ f) U W (fun _ hz => hV (hW hz))
  let iAB := pairAlgebra e V W hW
  have ht : IsScalarTower Γ(Y, U.1) Γ(X, V.1) Γ(Z, W.1) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((e ≫ f).appLE U.1 W.1 _).hom =
      (f.appLE U.1 V.1 hV ≫ e.appLE V.1 W.1 hW).hom
    rw [Scheme.Hom.appLE_comp_appLE]
  have hfp : _root_.Algebra.FinitePresentation Γ(Y, U.1) Γ(X, V.1) :=
    f.finitePresentation_appLE U.2 V.2 hV
  have he : _root_.Algebra.Etale Γ(X, V.1) Γ(Z, W.1) := e.etale_appLE V.2 W.2 hW
  exact Algebra.differentialFittingIdeal_of_formallyEtale Γ(Y, U.1) Γ(X, V.1) Γ(Z, W.1) i

/-- Differential Fitting ideals commute with étale restriction of the source. -/
lemma globalIdealSheaf_comp_etale {Z : Scheme.{u}} (f : X ⟶ Y) (e : Z ⟶ X)
    [LocallyOfFinitePresentation f] [Etale e] (i : ℕ) :
    globalIdealSheaf (e ≫ f) i = (globalIdealSheaf f i).comap e := by
  apply Scheme.IdealSheafData.ext_of_locally_eq
  intro z
  obtain ⟨⟨U, V⟩, hzV, hV⟩ := exists_affinePair f (e z)
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, hWV⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open hzV (e ⁻¹ᵁ V.1).isOpen
  refine ⟨⟨W, hW⟩, hzW, ?_⟩
  calc
    _ = idealOnPair (e ≫ f) i U ⟨W, hW⟩ (fun _ hz => hV (hWV hz)) :=
      globalIdealSheaf_ideal (e ≫ f) i U ⟨W, hW⟩ (fun _ hz => hV (hWV hz))
    _ = (idealOnPair f i U V hV).map (e.appLE V.1 W hWV).hom :=
      idealOnPair_comp_etale f e i U V ⟨W, hW⟩ hV hWV
    _ = ((globalIdealSheaf f i).ideal V).map (e.appLE V.1 W hWV).hom :=
      congrArg (Ideal.map (e.appLE V.1 W hWV).hom) (globalIdealSheaf_ideal f i U V hV).symm
    _ = ((globalIdealSheaf f i).comap e).ideal ⟨W, hW⟩ :=
      (Curves.idealSheaf_comap_ideal (globalIdealSheaf f i) e V ⟨W, hW⟩ hWV).symm
end GromovWitten.AlgebraicGeometry.RelativeFittingLocus
