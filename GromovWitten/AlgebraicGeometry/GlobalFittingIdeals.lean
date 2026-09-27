/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import GromovWitten.AlgebraicGeometry.RelativeFittingPairs
import GromovWitten.AlgebraicGeometry.IdealSheafGluing
/-!
# Global relative differential Fitting ideals

For an arbitrary locally finitely presented scheme morphism, the differential
Fitting ideals on adapted affine pairs determine a global ideal sheaf. This
construction agrees with the affine-target construction and does not require
the target to be separated.
-/

open CategoryTheory Opposite
open AlgebraicGeometry
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.RelativeFittingLocus
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The stalk ideal is independent of both affine neighborhoods. -/
lemma idealOnPair_stalk_eq [LocallyOfFinitePresentation f] (i : ℕ)
    (U₁ U₂ : Y.affineOpens) (V₁ V₂ : X.affineOpens)
    (h₁ : V₁.1 ≤ f ⁻¹ᵁ U₁.1) (h₂ : V₂.1 ≤ f ⁻¹ᵁ U₂.1)
    (x : X) (hx₁ : x ∈ V₁.1) (hx₂ : x ∈ V₂.1) :
    (idealOnPair f i U₁ V₁ h₁).map (X.presheaf.germ V₁.1 x hx₁).hom =
      (idealOnPair f i U₂ V₂ h₂).map (X.presheaf.germ V₂.1 x hx₂).hom := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ V₁.1 ⊓ V₂.1 from ⟨hx₁, hx₂⟩) (V₁.1 ⊓ V₂.1).isOpen
  have e₁ := idealOnPair_restrict f i (U := U₁) (U' := U₁) (V := V₁) (V' := ⟨V, hV⟩)
    le_rfl (fun z hz => (hVV hz).1) h₁ (fun z hz => h₁ (hVV hz).1)
  have e₂ := idealOnPair_restrict f i (U := U₂) (U' := U₂) (V := V₂) (V' := ⟨V, hV⟩)
    le_rfl (fun z hz => (hVV hz).2) h₂ (fun z hz => h₂ (hVV hz).2)
  have e := e₁.symm.trans ((idealOnPair_independent f i U₁ U₂ ⟨V, hV⟩ _ _).trans e₂)
  apply_fun Ideal.map (X.presheaf.germ V x hxV).hom at e
  simpa only [Ideal.map_map, ← CommRingCat.hom_comp, TopCat.Presheaf.germ_res'] using e

/-- Every source point lies in an affine pair adapted to the morphism. -/
lemma exists_affinePair (x : X) :
    ∃ p : Y.affineOpens × X.affineOpens, x ∈ p.2.1 ∧ p.2.1 ≤ f ⁻¹ᵁ p.1.1 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen
  exact ⟨(⟨U, hU⟩, ⟨V, hV⟩), hxV, hVU⟩

private def pairAt (x : X) : Y.affineOpens × X.affineOpens :=
  (exists_affinePair f x).choose

private lemma pairAt_spec (x : X) :
    x ∈ (pairAt f x).2.1 ∧ (pairAt f x).2.1 ≤ f ⁻¹ᵁ (pairAt f x).1.1 :=
  (exists_affinePair f x).choose_spec

/-- The relative differential Fitting ideal in a source stalk. -/
def stalkIdeal (i : ℕ) (x : X) : Ideal (X.presheaf.stalk x) :=
  (idealOnPair f i (pairAt f x).1 (pairAt f x).2 (pairAt_spec f x).2).map
    (X.presheaf.germ (pairAt f x).2.1 x (pairAt_spec f x).1).hom

/-- Compute the stalk ideal using any adapted affine pair. -/
lemma stalkIdeal_eq [LocallyOfFinitePresentation f] (i : ℕ)
    (U : Y.affineOpens) (V : X.affineOpens) (h : V.1 ≤ f ⁻¹ᵁ U.1)
    (x : X) (hx : x ∈ V.1) :
    stalkIdeal f i x = (idealOnPair f i U V h).map (X.presheaf.germ V.1 x hx).hom :=
  idealOnPair_stalk_eq f i (pairAt f x).1 U (pairAt f x).2 V (pairAt_spec f x).2 h
    x (pairAt_spec f x).1 hx

/-- The stalk ideals are locally represented by the affine differential Fitting ideals. -/
lemma stalkIdeal_locally_represented [LocallyOfFinitePresentation f] (i : ℕ) (x : X) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ ∃ I : Ideal Γ(X, V.1),
      X.RepresentsStalkIdeals (stalkIdeal f i) V I := by
  obtain ⟨⟨U, V⟩, hx, h⟩ := exists_affinePair f x
  exact ⟨V, hx, idealOnPair f i U V h, fun y hy => (stalkIdeal_eq f i U V h y hy).symm⟩

/-- The relative differential Fitting ideal sheaf over an arbitrary target. -/
def globalIdealSheaf [LocallyOfFinitePresentation f] (i : ℕ) : X.IdealSheafData :=
  X.idealSheafOfStalkIdeals (stalkIdeal f i) (stalkIdeal_locally_represented f i)

/-- On every adapted affine pair, the global ideal is the usual differential Fitting ideal. -/
lemma globalIdealSheaf_ideal [LocallyOfFinitePresentation f] (i : ℕ)
    (U : Y.affineOpens) (V : X.affineOpens) (h : V.1 ≤ f ⁻¹ᵁ U.1) :
    (globalIdealSheaf f i).ideal V = idealOnPair f i U V h :=
  X.idealSheafOfStalkIdeals_ideal _ _ V _ fun x hx => (stalkIdeal_eq f i U V h x hx).symm

/-- Over an affine target, the global construction agrees with the original construction. -/
lemma globalIdealSheaf_eq_idealSheaf [IsAffine Y] [LocallyOfFinitePresentation f] (i : ℕ) :
    globalIdealSheaf f i = idealSheaf f i := by
  ext1
  funext V
  exact globalIdealSheaf_ideal f i ⟨⊤, isAffineOpen_top Y⟩ V (le_preimage_top f V.1)
end GromovWitten.AlgebraicGeometry.RelativeFittingLocus
