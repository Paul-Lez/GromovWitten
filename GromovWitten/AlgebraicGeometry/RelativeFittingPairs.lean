/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import GromovWitten.AlgebraicGeometry.FittingIdealsSheaf
/-!
# Differential Fitting ideals on affine pairs

For a locally finitely presented morphism, the differential Fitting ideal on an
adapted source affine open is compatible with restriction of both affine opens.
It is independent of the target affine neighborhood, including when the target
is not separated.
-/

open CategoryTheory Opposite
open AlgebraicGeometry
namespace GromovWitten.AlgebraicGeometry.RelativeFittingLocus
universe u
noncomputable section
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
/-- The section algebra associated to an adapted source and target affine pair. -/
@[instance_reducible]
def pairAlgebra (U : Y.affineOpens) (V : X.affineOpens) (h : V.1 ≤ f ⁻¹ᵁ U.1) :
    Algebra Γ(Y, U.1) Γ(X, V.1) := (f.appLE U.1 V.1 h).hom.toAlgebra

/-- The relative differential Fitting ideal on an adapted affine pair. -/
def idealOnPair (i : ℕ) (U : Y.affineOpens) (V : X.affineOpens)
    (h : V.1 ≤ f ⁻¹ᵁ U.1) : Ideal Γ(X, V.1) :=
  @Algebra.differentialFittingIdeal Γ(Y, U.1) _ Γ(X, V.1) _ (pairAlgebra f U V h) i

/-- Restricting either affine open transports the differential Fitting ideal. -/
lemma idealOnPair_restrict [LocallyOfFinitePresentation f] (i : ℕ)
    {U U' : Y.affineOpens} {V V' : X.affineOpens} (hU : U' ≤ U) (hV : V' ≤ V)
    (h : V.1 ≤ f ⁻¹ᵁ U.1) (h' : V'.1 ≤ f ⁻¹ᵁ U'.1) :
    idealOnPair f i U' V' h' =
      (idealOnPair f i U V h).map (X.presheaf.map (homOfLE hV).op).hom := by
  let iRA : Algebra Γ(Y, U.1) Γ(X, V.1) := pairAlgebra f U V h
  let iSB : Algebra Γ(Y, U'.1) Γ(X, V'.1) := pairAlgebra f U' V' h'
  let iRS : Algebra Γ(Y, U.1) Γ(Y, U'.1) :=
    (Y.presheaf.map (homOfLE hU).op).hom.toAlgebra
  let iAB : Algebra Γ(X, V.1) Γ(X, V'.1) :=
    (X.presheaf.map (homOfLE hV).op).hom.toAlgebra
  let iRB : Algebra Γ(Y, U.1) Γ(X, V'.1) :=
    pairAlgebra f U V' ((show V'.1 ≤ V.1 from hV).trans h)
  have htA : IsScalarTower Γ(Y, U.1) Γ(X, V.1) Γ(X, V'.1) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    exact congrArg CommRingCat.Hom.hom (f.appLE_map h (homOfLE hV).op).symm
  have htS : IsScalarTower Γ(Y, U.1) Γ(Y, U'.1) Γ(X, V'.1) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    exact congrArg CommRingCat.Hom.hom (f.map_appLE h' (homOfLE hU).op).symm
  have hRA : _root_.Algebra.FinitePresentation Γ(Y, U.1) Γ(X, V.1) :=
    f.finitePresentation_appLE U.2 V.2 h
  have hSB : _root_.Algebra.FinitePresentation Γ(Y, U'.1) Γ(X, V'.1) :=
    f.finitePresentation_appLE U'.2 V'.2 h'
  have hRS : _root_.Algebra.Etale Γ(Y, U.1) Γ(Y, U'.1) := by
    have he := Scheme.Hom.etale_appLE (𝟙 Y) U.2 U'.2 (by simpa using hU)
    have hm : (𝟙 Y : Y ⟶ Y).appLE U.1 U'.1 (by simpa using hU) =
        Y.presheaf.map (homOfLE hU).op := by
      rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
      exact Category.id_comp _
    rw [hm] at he
    exact he
  have hAB : _root_.Algebra.Etale Γ(X, V.1) Γ(X, V'.1) := by
    have he := Scheme.Hom.etale_appLE (𝟙 X) V.2 V'.2 (by simpa using hV)
    have hm : (𝟙 X : X ⟶ X).appLE V.1 V'.1 (by simpa using hV) =
        X.presheaf.map (homOfLE hV).op := by
      rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
      exact Category.id_comp _
    rw [hm] at he
    exact he
  exact Algebra.differentialFittingIdeal_of_etale_restriction
    Γ(Y, U.1) Γ(Y, U'.1) Γ(X, V.1) Γ(X, V'.1) i

/-- The ideal does not depend on which target affine contains the source image. -/
lemma idealOnPair_independent [LocallyOfFinitePresentation f] (i : ℕ)
    (U₁ U₂ : Y.affineOpens) (V : X.affineOpens)
    (h₁ : V.1 ≤ f ⁻¹ᵁ U₁.1) (h₂ : V.1 ≤ f ⁻¹ᵁ U₂.1) :
    idealOnPair f i U₁ V h₁ = idealOnPair f i U₂ V h₂ := by
  rw [V.2.ideal_ext_iff]
  intro x hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show f x ∈ U₁.1 ⊓ U₂.1 from ⟨h₁ hx, h₂ hx⟩) (U₁.1 ⊓ U₂.1).isOpen
  obtain ⟨_, ⟨V', hV', rfl⟩, hxV', hVV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ V.1 ⊓ f ⁻¹ᵁ W from ⟨hx, hxW⟩) (V.1 ⊓ f ⁻¹ᵁ W).isOpen
  have e₁ := idealOnPair_restrict f i (U' := ⟨W, hW⟩) (V' := ⟨V', hV'⟩)
    (U := U₁) (V := V) (fun z hz => (hWU hz).1) (fun z hz => (hVV hz).1)
    h₁ (fun z hz => (hVV hz).2)
  have e₂ := idealOnPair_restrict f i (U' := ⟨W, hW⟩) (V' := ⟨V', hV'⟩)
    (U := U₂) (V := V) (fun z hz => (hWU hz).2) (fun z hz => (hVV hz).1)
    h₂ (fun z hz => (hVV hz).2)
  have e := e₁.symm.trans e₂
  apply_fun Ideal.map (X.presheaf.germ V' x hxV').hom at e
  simpa only [Ideal.map_map, ← CommRingCat.hom_comp, X.presheaf.germ_res,
    TopCat.Presheaf.germ_res'] using e

end
end GromovWitten.AlgebraicGeometry.RelativeFittingLocus
