import GromovWitten.AlgebraicGeometry.FittingIdealsSheaf
import Mathlib.Algebra.Module.Presentation.Free
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

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

end

end GromovWitten.AlgebraicGeometry
