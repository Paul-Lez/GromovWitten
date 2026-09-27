/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.FittingIdealsSheaf
import GromovWitten.AlgebraicGeometry.GlobalFittingIdeals
import Mathlib.Algebra.Module.Presentation.Free
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# First differential Fitting ideals on smooth relative curves

The standard smooth presentation makes the relative differentials free of rank one.
Its first Fitting ideal is therefore the unit ideal. Affine charts give the corresponding
statement for the global Fitting ideal on a smooth relative curve over any target.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry

universe u

noncomputable section

open _root_.AlgebraicGeometry

private theorem standardSmoothFittingAux
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Nontrivial S] {ι σ κ : Type} [Finite σ] [Finite ι]
    (P : Algebra.SubmersivePresentation R S ι σ)
    (hP : P.dimension = 1)
    (b : Module.Basis κ S Ω[S⁄R])
    (Q : Module.Presentation.{0, 0} S Ω[S⁄R])
    (hQ : Q = (Module.presentationFinsupp S κ).ofLinearEquiv b.repr.symm)
    (fκ : Fintype κ) (fG : Fintype Q.G) (fR : Fintype Q.R) :
    Algebra.differentialFittingIdeal R S 1 = ⊤ := by
  have hcardκ : Fintype.card κ ≤ 1 := by
    have hrank := @Algebra.SubmersivePresentation.rank_kaehlerDifferential
      R S ι σ _ _ _ inferInstance inferInstance inferInstance P
    rw [hP] at hrank
    rw [@rank_eq_card_basis S Ω[S⁄R] _ _ _ _ κ fκ b] at hrank
    exact Nat.le_of_eq (by exact_mod_cast hrank)
  change Module.fittingIdeal S Ω[S⁄R] 1 = ⊤
  rw [@Module.fittingIdeal_eq S _ Ω[S⁄R] _ _ Q fG fR 1]
  exact @Module.Presentation.fittingIdeal_eq_top_of_card_le S _ Ω[S⁄R] _ _ Q fG fR 1
    (by simpa [hQ, Module.Presentation.ofLinearEquiv] using hcardκ)

/-- The first differential Fitting ideal is the unit ideal for a standard smooth
algebra of relative dimension one. -/
theorem differentialFittingIdeal_one_eq_top_of_standardSmooth
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R S] [Nontrivial S] :
    Algebra.differentialFittingIdeal R S 1 = ⊤ := by
  obtain ⟨ι, σ, hσ, hι, P, hP⟩ :=
    (inferInstance : Algebra.IsStandardSmoothOfRelativeDimension 1 R S).out
  let κ := ((Set.range P.map)ᶜ : Set ι)
  let hκ : Finite κ := @Finite.of_injective κ ι hι Subtype.val Subtype.val_injective
  let fκ : Fintype κ := @Fintype.ofFinite κ hκ
  let b : Module.Basis κ S Ω[S⁄R] :=
    @Algebra.SubmersivePresentation.basisKaehler R S ι σ _ _ _ hσ P
  let Q : Module.Presentation.{0, 0} S Ω[S⁄R] :=
    (Module.presentationFinsupp S κ).ofLinearEquiv b.repr.symm
  let fG : Fintype Q.G := by
    simpa [Q, Module.Presentation.ofLinearEquiv] using fκ
  let fR : Fintype Q.R := by
    simpa [Q, Module.Presentation.ofLinearEquiv] using (Fintype.ofFinite (PEmpty.{1}))
  exact @standardSmoothFittingAux R S _ _ _ _ ι σ κ hσ hι P hP b Q rfl fκ fG fR

namespace RelativeFittingLocus

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y]

/-- A standard-smooth relative-dimension-one affine chart has unit first Fitting ideal
for the affine-target relative ideal on the same source open. -/
theorem idealOn_one_eq_top_of_standardSmooth
    [LocallyOfFinitePresentation f]
    {U : Y.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (hsm : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension 1) :
    idealOn f 1 ⟨V, hV⟩ = ⊤ := by
  let R := Γ(Y, (⊤ : Y.Opens))
  let S := Γ(Y, U)
  let T := Γ(X, V)
  let iRS : Algebra R S :=
    (Y.presheaf.map (homOfLE (show U ≤ (⊤ : Y.Opens) from le_top)).op).hom.toAlgebra
  let iRT : Algebra R T := baseAlgebra f ⟨V, hV⟩
  let iST : Algebra S T := (f.appLE U V e).hom.toAlgebra
  let _instRS : Algebra R S := iRS
  let _instRT : Algebra R T := iRT
  let _instST : Algebra S T := iST
  let _instSmooth : Algebra.IsStandardSmoothOfRelativeDimension 1 S T := hsm
  have htower : IsScalarTower R S T := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    exact congrArg CommRingCat.Hom.hom
      (f.map_appLE e (homOfLE (show U ≤ (⊤ : Y.Opens) from le_top)).op).symm
  let _instTower : IsScalarTower R S T := htower
  have hEtale : _root_.Algebra.Etale R S := by
    have h := Scheme.Hom.etale_appLE (𝟙 Y) (isAffineOpen_top Y) hU
      (show U ≤ (𝟙 Y) ⁻¹ᵁ (⊤ : Y.Opens) by simp)
    exact h
  let _instEtale : _root_.Algebra.Etale R S := hEtale
  have hfp : _root_.Algebra.FinitePresentation S T :=
    f.finitePresentation_appLE hU hV e
  have hbase := Algebra.differentialFittingIdeal_of_formallyUnramified_base R S T 1
  have hstd : Algebra.differentialFittingIdeal S T 1 = ⊤ := by
    by_cases hT : Nontrivial T
    · let _instT : Nontrivial T := hT
      exact differentialFittingIdeal_one_eq_top_of_standardSmooth
    · let _instT : Subsingleton T := not_nontrivial_iff_subsingleton.mp hT
      exact Subsingleton.elim _ _
  change Algebra.differentialFittingIdeal R T 1 = ⊤
  rw [← hbase, hstd]

/-! The affine calculation gives the corresponding statement for the global ideal sheaf. -/

omit [IsAffine Y] in
/-- On a smooth relative curve, the global first Fitting support is empty locally at every
point. The target need not be affine. -/
theorem not_mem_globalIdealSheaf_support_one_of_smoothOfRelativeDimension
    [LocallyOfFinitePresentation f] [SmoothOfRelativeDimension 1 f] (x : X) :
    x ∉ (globalIdealSheaf f 1).support := by
  obtain ⟨U, hU, V, hV, hxV, e, hsm⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := 1) (f := f) x
  have htop : idealOnPair f 1 ⟨U, hU⟩ ⟨V, hV⟩ e = ⊤ := by
    let _ := pairAlgebra f ⟨U, hU⟩ ⟨V, hV⟩ e
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 1 Γ(Y, U) Γ(X, V) := hsm
    change Algebra.differentialFittingIdeal Γ(Y, U) Γ(X, V) 1 = ⊤
    by_cases hT : Nontrivial Γ(X, V)
    · let _ := hT
      exact differentialFittingIdeal_one_eq_top_of_standardSmooth
    · let _ : Subsingleton Γ(X, V) := not_nontrivial_iff_subsingleton.mp hT
      exact Subsingleton.elim _ _
  intro hx
  have hz := (Scheme.IdealSheafData.mem_support_iff_of_mem
    (I := globalIdealSheaf f 1) (U := ⟨V, hV⟩) hxV).mp hx
  rw [globalIdealSheaf_ideal f 1 ⟨U, hU⟩ ⟨V, hV⟩ e, htop] at hz
  have hz' : x ∉ (V : Set X) := by simpa using hz
  exact hz' hxV

end RelativeFittingLocus

end

end GromovWitten.AlgebraicGeometry
