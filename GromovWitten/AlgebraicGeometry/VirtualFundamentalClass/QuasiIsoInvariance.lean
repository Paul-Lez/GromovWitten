/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.QuasiIsoSplitting
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.HomotopyInvariance
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.IndependenceAcyclic

/-!
# Quasi-isomorphism invariance of the virtual fundamental class

Let `X = Spec (R ⧸ I) ⊆ Spec R`, let `L = conormalComplex k R I` and let
`φ : E ⟶ L`, `ψ : F ⟶ L` be two chain maps out of perfect two-term complexes which are
related by a quasi-isomorphism `f : E ⟶ F` with `ψ⁻¹ ∘ f⁻¹ = φ⁻¹` in degree `-1`.  This file
proves that `φ` and `ψ` define the *same* virtual fundamental class.

The proof is the chain of four equalities of Behrend–Fantechi, Proposition 5.3, assembled from
the three previous layers:

1. `VirtualClass.virtualClassAt_sumAcyclic` (round 14): the class of `ψ` equals the class of
   `Ψ := ψ ⊕ 0 : F ⊕ [E⁰ = E⁰] ⟶ L`;
2. `HomotopyInvariance.virtualClassAt_congr` together with
   `LinearTwoTermComplex.QuasiIsoSplitting.coprod_comp_iso_degreeZero`: the class of `Ψ` equals
   the class of `Ψ' := Φ ∘ Θ`, where `Θ : F ⊕ [E⁰ = E⁰] ⟶ E ⊕ [F⁰ = F⁰]` is the isomorphism
   produced by the splitting of `f` and `Φ := φ ⊕ 0`, because `Ψ'` and `Ψ` differ in degree `-1`
   by a chain homotopy;
3. `VirtualClass.virtualClassAt_congr` (round 14, isomorphism invariance): the class of `Ψ'`
   equals the class of `Φ`, the compatibility `Φ⁻¹ ∘ Θ⁻¹ = Ψ'⁻¹` being `rfl`;
4. `VirtualClass.virtualClassAt_sumAcyclic` again: the class of `Φ` equals the class of `φ`.

## Main results

* `virtualClassAt_eq_of_quasiIso`: the chain above, for arbitrary trivialisations and an
  arbitrary degree `i`.  The classes of `φ` and of `ψ` live in the same Chow group `RX.ChowGroup`
  and are equal, for *arbitrary* proofs of the homogeneity and injectivity hypotheses of the two
  sides (both are `Prop`s, so proof irrelevance applies).
* `virtualClass_eq_of_quasiIso`: the same statement for the canonical trivialisations and the
  canonical degree, so that the left-hand side is literally
  `VirtualClass.virtualClass φ dimX dimE RX RE hhomE hinjE`.
* `virtualClassAt_eq_of_homotopyEquivalence`, `virtualClassAt_eq_of_quasiIso_homotopy`: the two
  corollaries, for a chain-homotopy equivalence `E ≃ F` and for compatibility of `φ` and `ψ`
  only up to a degree-zero homotopy.
* `isObstructionTheory_comp_of_isQuasiIsomorphism`, `isObstructionTheory_sumAcyclic_comp_iso`:
  the intermediate map `Ψ' = Φ ∘ Θ` is again an obstruction theory.
* `isPerfectTwoTerm_acyclicComplex`, `isPerfectTwoTerm_sumAcyclic`: the intermediate complexes
  are perfect.
* `finrank_add_finrank_of_quasiIso`, `virtualDimension_eq_of_quasiIso`: a quasi-isomorphism of
  perfect two-term complexes preserves the virtual dimension.

## Explicit hypotheses

Beyond the data of `f`, the only genuinely extra hypotheses of the main theorem are the
homogeneity `hhom₁` and injectivity `hinj₁` for the bundle space of `F ⊕ [E⁰ = E⁰]` and the two
numerical hypotheses `hcard₁`, `hcard₂` comparing the ranks of the chosen trivialisations (both
are automatic for the canonical trivialisations over a nontrivial base, see
`card_chooseBasisIndex_sum_of_quasiIso`).  Everything else — the homogeneity and injectivity
statements for `φ`, for `ψ` and for `E ⊕ [F⁰ = F⁰]` — is *derived* through the round-14 transport
lemmas `VirtualClass.principalDivisorsHomogeneous_of_sumAcyclic`,
`VirtualClass.injective_chowPullbackBundle_of_sumAcyclic`,
`VirtualClass.principalDivisorsHomogeneous_transport` and
`VirtualClass.injective_chowPullbackBundle_transport`.
-/

universe u

-- The coordinate ring `gr_I(R) ⊗_{R/I} Sym(E⁰)` of the resolved cone needs a deeper instance
-- search than the default, exactly as in `ResolvedCone.lean` and `Independence.lean`.
set_option maxSynthPendingDepth 5

open CategoryTheory AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.QuasiIsoInvariance

open IntersectionTheory hiding Scheme AlgebraicCycle
open NormalSheafPicard.AffineIntrinsicNormalSheaf

/-! ## Perfectness and obstruction theories of the intermediate complexes -/

section Algebra

variable {S : Type u} [CommRing S]

/-- The acyclic complex `[M --id--> M]` on a finite free module is a perfect two-term
complex. -/
theorem isPerfectTwoTerm_acyclicComplex (M : Type u) [AddCommGroup M] [Module S M]
    [Module.Free S M] [Module.Finite S M] :
    PicardCriteria.IsPerfectTwoTerm (VirtualClass.acyclicComplex S M) where
  free_degreeZero := inferInstance
  finite_degreeZero := inferInstance
  free_degreeOne := inferInstance
  finite_degreeOne := inferInstance

/-- Adding an acyclic summand on a finite free module preserves perfectness. -/
theorem isPerfectTwoTerm_sumAcyclic {E : LinearTwoTermComplex S}
    (hE : PicardCriteria.IsPerfectTwoTerm E) (M : Type u) [AddCommGroup M] [Module S M]
    [Module.Free S M] [Module.Finite S M] :
    PicardCriteria.IsPerfectTwoTerm (E.sum (VirtualClass.acyclicComplex S M)) :=
  hE.sum (isPerfectTwoTerm_acyclicComplex M)

/-- **The composite of an obstruction theory with a quasi-isomorphism is an obstruction
theory.**  This is `PicardCriteria.IsObstructionTheory.quasiIso_comp`, recorded here under the
name used by the chain of equalities below: it is what makes `Ψ' = Φ ∘ Θ` an obstruction
theory. -/
theorem isObstructionTheory_comp_of_isQuasiIsomorphism {A B L : LinearTwoTermComplex S}
    {Φ : LinearTwoTermComplex.Hom B L} {Θ : LinearTwoTermComplex.Hom A B}
    (hΦ : PicardCriteria.IsObstructionTheory Φ) (hΘ : Θ.IsQuasiIsomorphism) :
    PicardCriteria.IsObstructionTheory (Φ.comp Θ) :=
  hΦ.quasiIso_comp hΘ

variable {E F : LinearTwoTermComplex S}
variable [Module.Free S E.degreeZero] [Module.Finite S E.degreeZero]
variable [Module.Free S E.degreeOne] [Module.Finite S E.degreeOne]
variable [Module.Free S F.degreeZero] [Module.Finite S F.degreeZero]
variable [Module.Free S F.degreeOne] [Module.Finite S F.degreeOne]

/-- **A quasi-isomorphism of perfect two-term complexes gives `rk F⁻¹ + rk E⁰ = rk E⁻¹ + rk F⁰`.**
This is the rank identity of the short exact sequence `0 → E⁻¹ → F⁻¹ ⊕ E⁰ → F⁰ → 0`, read off
from the splitting `LinearTwoTermComplex.QuasiIsoSplitting.iso` in degree `-1`. -/
theorem finrank_add_finrank_of_quasiIso [StrongRankCondition S]
    (f : LinearTwoTermComplex.Hom E F) (hf : f.IsQuasiIsomorphism) :
    Module.finrank S F.degreeZero + Module.finrank S E.degreeOne =
      Module.finrank S E.degreeZero + Module.finrank S F.degreeOne := by
  have hiso : (F.degreeZero × E.degreeOne) ≃ₗ[S] (E.degreeZero × F.degreeOne) :=
    LinearEquiv.ofBijective (LinearTwoTermComplex.QuasiIsoSplitting.iso f hf).degreeZero
      (LinearTwoTermComplex.QuasiIsoSplitting.iso_degreeZero_bijective f hf)
  have hrank := hiso.finrank_eq
  rwa [Module.finrank_prod, Module.finrank_prod] at hrank

/-- **The rank of the bundle of `F ⊕ [E⁰ = E⁰]` splits as `rk E⁻¹ + rk F⁰`.**  This is the
numerical hypothesis `hcard₂` of the chain of equalities, for the canonical trivialisations. -/
theorem card_chooseBasisIndex_sum_of_quasiIso [Nontrivial S]
    (f : LinearTwoTermComplex.Hom E F) (hf : f.IsQuasiIsomorphism) :
    (Nat.card (Module.Free.ChooseBasisIndex S
        (F.sum (VirtualClass.acyclicComplex S E.degreeOne)).degreeZero) : ℤ) =
      (Nat.card (Module.Free.ChooseBasisIndex S E.degreeZero) : ℤ) +
        (Nat.card (Module.Free.ChooseBasisIndex S F.degreeOne) : ℤ) := by
  rw [VectorBundle.card_chooseBasisIndex, VectorBundle.card_chooseBasisIndex,
    VectorBundle.card_chooseBasisIndex]
  change ((Module.finrank S (F.degreeZero × E.degreeOne) : ℤ)) = _
  rw [Module.finrank_prod]
  have hrank := finrank_add_finrank_of_quasiIso f hf
  push_cast
  omega

end Algebra

/-! ## The homotopy relating `Ψ` and `Φ ∘ Θ` -/

section Homotopy

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {I : Ideal R}
variable {E F : LinearTwoTermComplex (R ⧸ I)}
variable [Module.Free (R ⧸ I) F.degreeOne]

/-- **The degree `-1` homotopy formula for the two obstruction theories on `F ⊕ [E⁰ = E⁰]`.**
Transporting `Φ = φ ⊕ 0` along the splitting isomorphism `Θ` gives `Ψ = ψ ⊕ 0` up to the
degree `-1` part of the chain homotopy `LinearTwoTermComplex.QuasiIsoSplitting.homotopy`.  This
is exactly the hypothesis shape consumed by `HomotopyInvariance.virtualClassAt_congr`. -/
theorem degreeZero_sumAcyclic_comp_iso
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    (ψ : LinearTwoTermComplex.Hom F (conormalComplex k R I))
    (f : LinearTwoTermComplex.Hom E F) (hf : f.IsQuasiIsomorphism)
    (hcomp : ψ.degreeZero.comp f.degreeZero = φ.degreeZero) :
    ((VirtualClass.sumAcyclic φ F.degreeOne).comp
        (LinearTwoTermComplex.QuasiIsoSplitting.iso f hf)).degreeZero =
      (VirtualClass.sumAcyclic ψ E.degreeOne).degreeZero +
        (LinearTwoTermComplex.QuasiIsoSplitting.homotopy f hf ψ).comp
          (F.sum (VirtualClass.acyclicComplex (R ⧸ I) E.degreeOne)).differential :=
  LinearTwoTermComplex.QuasiIsoSplitting.coprod_comp_iso_degreeZero f hf hcomp

/-- **The intermediate map `Ψ' = Φ ∘ Θ` is an obstruction theory** whenever `φ` is one: it is
the composite of the obstruction theory `Φ = φ ⊕ 0` with the quasi-isomorphism `Θ`. -/
theorem isObstructionTheory_sumAcyclic_comp_iso
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    (f : LinearTwoTermComplex.Hom E F) (hf : f.IsQuasiIsomorphism)
    (hφ : PicardCriteria.IsObstructionTheory φ) :
    PicardCriteria.IsObstructionTheory
      ((VirtualClass.sumAcyclic φ F.degreeOne).comp
        (LinearTwoTermComplex.QuasiIsoSplitting.iso f hf)) :=
  isObstructionTheory_comp_of_isQuasiIsomorphism
    (VirtualClass.isObstructionTheory_sumAcyclic φ F.degreeOne hφ)
    (LinearTwoTermComplex.QuasiIsoSplitting.iso_isQuasiIsomorphism f hf)

end Homotopy

/-! ## The chain of equalities -/

section Main

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R] {I : Ideal R}
variable {E F : LinearTwoTermComplex (R ⧸ I)}
variable [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
variable [Module.Free (R ⧸ I) E.degreeOne] [Module.Finite (R ⧸ I) E.degreeOne]
variable [Module.Free (R ⧸ I) F.degreeZero] [Module.Finite (R ⧸ I) F.degreeZero]
variable [Module.Free (R ⧸ I) F.degreeOne] [Module.Finite (R ⧸ I) F.degreeOne]
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
variable (ψ : LinearTwoTermComplex.Hom F (conormalComplex k R I))

/-- **Behrend–Fantechi, Proposition 5.3 (quasi-isomorphism invariance), in the degree-generic
form.**

Let `f : E ⟶ F` be a quasi-isomorphism of perfect two-term complexes and let `φ : E ⟶ L`,
`ψ : F ⟶ L` satisfy `ψ⁻¹ ∘ f⁻¹ = φ⁻¹`.  Then the virtual classes of `φ` and `ψ`, computed in
arbitrary trivialisations `eE`, `eF` and in one and the same degree `i`, are equal as elements of
`RX.ChowGroup`.

The extra data are those of the intermediate complex `F ⊕ [E⁰ = E⁰]` (the trivialisation `e₁`,
the dimension function `dim₁`, the rational-equivalence system `R₁`) and of
`E ⊕ [F⁰ = F⁰]` (`dim₂`, `R₂`); the extra *hypotheses* are the homogeneity `hhom₁` and the
injectivity `hinj₁` for `F ⊕ [E⁰ = E⁰]`, and the two rank identities `hcard₁`, `hcard₂`.  The
homogeneity and injectivity hypotheses `hhomE`, `hinjE`, `hhomF`, `hinjF` appearing in the two
sides are arbitrary: they are `Prop`s, so the conclusion is independent of their proofs. -/
theorem virtualClassAt_eq_of_quasiIso
    (f : LinearTwoTermComplex.Hom E F) (hf : f.IsQuasiIsomorphism)
    (hcomp : ψ.degreeZero.comp f.degreeZero = φ.degreeZero)
    {κE κF κ₁ : Type u} [Finite κE] [Finite κF] [Finite κ₁]
    (eE : ResolvedCone.bundleRing φ ≃ₐ[R ⧸ I] MvPolynomial κE (R ⧸ I))
    (eF : ResolvedCone.bundleRing ψ ≃ₐ[R ⧸ I] MvPolynomial κF (R ⧸ I))
    (e₁ : ResolvedCone.bundleRing (VirtualClass.sumAcyclic ψ E.degreeOne) ≃ₐ[R ⧸ I]
      MvPolynomial κ₁ (R ⧸ I))
    (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (dimF : DimensionFunction (ResolvedCone.bundleSpace ψ))
    (dim₁ : DimensionFunction
      (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic ψ E.degreeOne)))
    (dim₂ : DimensionFunction
      (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic φ F.degreeOne)))
    (i : ℤ)
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX i)
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (i + (Nat.card κE : ℤ)))
    (RF : RationalEquivalenceSystem (ResolvedCone.bundleSpace ψ) dimF (i + (Nat.card κF : ℤ)))
    (R₁ : RationalEquivalenceSystem
      (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic ψ E.degreeOne)) dim₁
      (i + (Nat.card κ₁ : ℤ)))
    (R₂ : RationalEquivalenceSystem
      (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic φ F.degreeOne)) dim₂
      (i + (Nat.card κ₁ : ℤ)))
    (hcard₁ : (Nat.card κ₁ : ℤ) = (Nat.card κF : ℤ) +
      (Nat.card (Module.Free.ChooseBasisIndex (R ⧸ I) E.degreeOne) : ℤ))
    (hcard₂ : (Nat.card κ₁ : ℤ) = (Nat.card κE : ℤ) +
      (Nat.card (Module.Free.ChooseBasisIndex (R ⧸ I) F.degreeOne) : ℤ))
    (hhom₁ : PrincipalDivisorsHomogeneous
      (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic ψ E.degreeOne)) dim₁)
    (hinj₁ : Function.Injective (VectorBundle.chowPullbackBundle e₁ dimX dim₁ i RX R₁))
    (hhomE : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinjE : Function.Injective (VectorBundle.chowPullbackBundle eE dimX dimE i RX RE))
    (hhomF : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace ψ) dimF)
    (hinjF : Function.Injective (VectorBundle.chowPullbackBundle eF dimX dimF i RX RF)) :
    VirtualClass.virtualClassAt φ eE dimX dimE i RX RE hhomE hinjE =
      VirtualClass.virtualClassAt ψ eF dimX dimF i RX RF hhomF hinjF := by
  have hΘ0 := LinearTwoTermComplex.QuasiIsoSplitting.iso_degreeZero_bijective f hf
  have hΘ1 := LinearTwoTermComplex.QuasiIsoSplitting.iso_degreeOne_bijective f hf
  have hhomotopy := degreeZero_sumAcyclic_comp_iso φ ψ f hf hcomp
  have step1 := VirtualClass.virtualClassAt_sumAcyclic ψ E.degreeOne eF e₁ dimX dimF dim₁ i
    RX RF R₁ hcard₁ hhom₁ hinj₁
  have step2 := HomotopyInvariance.virtualClassAt_congr (VirtualClass.sumAcyclic ψ E.degreeOne)
    ((VirtualClass.sumAcyclic φ F.degreeOne).comp
      (LinearTwoTermComplex.QuasiIsoSplitting.iso f hf))
    (LinearTwoTermComplex.QuasiIsoSplitting.homotopy f hf ψ) hhomotopy e₁ dimX dim₁ i RX R₁
    hhom₁ hinj₁
  have step3 := VirtualClass.virtualClassAt_congr
    ((VirtualClass.sumAcyclic φ F.degreeOne).comp
      (LinearTwoTermComplex.QuasiIsoSplitting.iso f hf))
    (VirtualClass.sumAcyclic φ F.degreeOne)
    (LinearTwoTermComplex.QuasiIsoSplitting.iso f hf) hΘ0 hΘ1 rfl e₁ dimX dim₁ dim₂ i RX R₁ R₂
    hhom₁ hinj₁
  have step4 := VirtualClass.virtualClassAt_sumAcyclic φ F.degreeOne eE
    (VirtualClass.trivializationTransport
      ((VirtualClass.sumAcyclic φ F.degreeOne).comp
        (LinearTwoTermComplex.QuasiIsoSplitting.iso f hf))
      (VirtualClass.sumAcyclic φ F.degreeOne)
      (LinearTwoTermComplex.QuasiIsoSplitting.iso f hf) hΘ0 e₁)
    dimX dimE dim₂ i RX RE R₂ hcard₂
    (VirtualClass.principalDivisorsHomogeneous_transport
      ((VirtualClass.sumAcyclic φ F.degreeOne).comp
        (LinearTwoTermComplex.QuasiIsoSplitting.iso f hf))
      (VirtualClass.sumAcyclic φ F.degreeOne)
      (LinearTwoTermComplex.QuasiIsoSplitting.iso f hf) hΘ0 dim₁ dim₂ hhom₁)
    (VirtualClass.injective_chowPullbackBundle_transport
      ((VirtualClass.sumAcyclic φ F.degreeOne).comp
        (LinearTwoTermComplex.QuasiIsoSplitting.iso f hf))
      (VirtualClass.sumAcyclic φ F.degreeOne)
      (LinearTwoTermComplex.QuasiIsoSplitting.iso f hf) hΘ0 e₁ dimX dim₁ dim₂ i RX R₁ R₂ hinj₁)
  exact step4.symm.trans (step3.symm.trans (step2.trans step1))

/-- **Quasi-isomorphism invariance for a chain-homotopy equivalence.**  If `e : E ≃ F` is a
chain-homotopy equivalence with `ψ⁻¹ ∘ e.hom⁻¹ = φ⁻¹`, then `φ` and `ψ` have the same virtual
class. -/
theorem virtualClassAt_eq_of_homotopyEquivalence
    (he : LinearTwoTermComplex.HomotopyEquivalence E F)
    (hcomp : ψ.degreeZero.comp he.hom.degreeZero = φ.degreeZero)
    {κE κF κ₁ : Type u} [Finite κE] [Finite κF] [Finite κ₁]
    (eE : ResolvedCone.bundleRing φ ≃ₐ[R ⧸ I] MvPolynomial κE (R ⧸ I))
    (eF : ResolvedCone.bundleRing ψ ≃ₐ[R ⧸ I] MvPolynomial κF (R ⧸ I))
    (e₁ : ResolvedCone.bundleRing (VirtualClass.sumAcyclic ψ E.degreeOne) ≃ₐ[R ⧸ I]
      MvPolynomial κ₁ (R ⧸ I))
    (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (dimF : DimensionFunction (ResolvedCone.bundleSpace ψ))
    (dim₁ : DimensionFunction
      (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic ψ E.degreeOne)))
    (dim₂ : DimensionFunction
      (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic φ F.degreeOne)))
    (i : ℤ)
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX i)
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (i + (Nat.card κE : ℤ)))
    (RF : RationalEquivalenceSystem (ResolvedCone.bundleSpace ψ) dimF (i + (Nat.card κF : ℤ)))
    (R₁ : RationalEquivalenceSystem
      (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic ψ E.degreeOne)) dim₁
      (i + (Nat.card κ₁ : ℤ)))
    (R₂ : RationalEquivalenceSystem
      (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic φ F.degreeOne)) dim₂
      (i + (Nat.card κ₁ : ℤ)))
    (hcard₁ : (Nat.card κ₁ : ℤ) = (Nat.card κF : ℤ) +
      (Nat.card (Module.Free.ChooseBasisIndex (R ⧸ I) E.degreeOne) : ℤ))
    (hcard₂ : (Nat.card κ₁ : ℤ) = (Nat.card κE : ℤ) +
      (Nat.card (Module.Free.ChooseBasisIndex (R ⧸ I) F.degreeOne) : ℤ))
    (hhom₁ : PrincipalDivisorsHomogeneous
      (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic ψ E.degreeOne)) dim₁)
    (hinj₁ : Function.Injective (VectorBundle.chowPullbackBundle e₁ dimX dim₁ i RX R₁))
    (hhomE : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinjE : Function.Injective (VectorBundle.chowPullbackBundle eE dimX dimE i RX RE))
    (hhomF : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace ψ) dimF)
    (hinjF : Function.Injective (VectorBundle.chowPullbackBundle eF dimX dimF i RX RF)) :
    VirtualClass.virtualClassAt φ eE dimX dimE i RX RE hhomE hinjE =
      VirtualClass.virtualClassAt ψ eF dimX dimF i RX RF hhomF hinjF :=
  virtualClassAt_eq_of_quasiIso φ ψ he.hom he.isQuasiIsomorphism hcomp eE eF e₁ dimX dimE dimF
    dim₁ dim₂ i RX RE RF R₁ R₂ hcard₁ hcard₂ hhom₁ hinj₁ hhomE hinjE hhomF hinjF

/-- **Quasi-isomorphism invariance when `φ` and `ψ` are compatible only up to a degree-zero
homotopy.**  If `ψ⁻¹ ∘ f⁻¹ = φ⁻¹ + h ∘ d_E` for some `h : E⁰ →ₗ I/I²`, then `φ` and `ψ` still
have the same virtual class: the theory `ψ ∘ f` is homotopic to `φ` in the sense of
`HomotopyInvariance.virtualClassAt_congr` and is strictly compatible with `ψ`. -/
theorem virtualClassAt_eq_of_quasiIso_homotopy
    (f : LinearTwoTermComplex.Hom E F) (hf : f.IsQuasiIsomorphism)
    (h : E.degreeOne →ₗ[R ⧸ I] (conormalComplex k R I).degreeZero)
    (hcomp : ψ.degreeZero.comp f.degreeZero = φ.degreeZero + h.comp E.differential)
    {κE κF κ₁ : Type u} [Finite κE] [Finite κF] [Finite κ₁]
    (eE : ResolvedCone.bundleRing φ ≃ₐ[R ⧸ I] MvPolynomial κE (R ⧸ I))
    (eF : ResolvedCone.bundleRing ψ ≃ₐ[R ⧸ I] MvPolynomial κF (R ⧸ I))
    (e₁ : ResolvedCone.bundleRing (VirtualClass.sumAcyclic ψ E.degreeOne) ≃ₐ[R ⧸ I]
      MvPolynomial κ₁ (R ⧸ I))
    (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (dimF : DimensionFunction (ResolvedCone.bundleSpace ψ))
    (dim₁ : DimensionFunction
      (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic ψ E.degreeOne)))
    (dim₂ : DimensionFunction
      (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic φ F.degreeOne)))
    (i : ℤ)
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX i)
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (i + (Nat.card κE : ℤ)))
    (RF : RationalEquivalenceSystem (ResolvedCone.bundleSpace ψ) dimF (i + (Nat.card κF : ℤ)))
    (R₁ : RationalEquivalenceSystem
      (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic ψ E.degreeOne)) dim₁
      (i + (Nat.card κ₁ : ℤ)))
    (R₂ : RationalEquivalenceSystem
      (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic φ F.degreeOne)) dim₂
      (i + (Nat.card κ₁ : ℤ)))
    (hcard₁ : (Nat.card κ₁ : ℤ) = (Nat.card κF : ℤ) +
      (Nat.card (Module.Free.ChooseBasisIndex (R ⧸ I) E.degreeOne) : ℤ))
    (hcard₂ : (Nat.card κ₁ : ℤ) = (Nat.card κE : ℤ) +
      (Nat.card (Module.Free.ChooseBasisIndex (R ⧸ I) F.degreeOne) : ℤ))
    (hhom₁ : PrincipalDivisorsHomogeneous
      (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic ψ E.degreeOne)) dim₁)
    (hinj₁ : Function.Injective (VectorBundle.chowPullbackBundle e₁ dimX dim₁ i RX R₁))
    (hhomE : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinjE : Function.Injective (VectorBundle.chowPullbackBundle eE dimX dimE i RX RE))
    (hhomF : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace ψ) dimF)
    (hinjF : Function.Injective (VectorBundle.chowPullbackBundle eF dimX dimF i RX RF)) :
    VirtualClass.virtualClassAt φ eE dimX dimE i RX RE hhomE hinjE =
      VirtualClass.virtualClassAt ψ eF dimX dimF i RX RF hhomF hinjF := by
  have hstep := HomotopyInvariance.virtualClassAt_congr φ (ψ.comp f) h hcomp eE dimX dimE i
    RX RE hhomE hinjE
  have hmain := virtualClassAt_eq_of_quasiIso (ψ.comp f) ψ f hf rfl eE eF e₁ dimX dimE dimF
    dim₁ dim₂ i RX RE RF R₁ R₂ hcard₁ hcard₂ hhom₁ hinj₁ hhomE hinjE hhomF hinjF
  exact hstep.symm.trans hmain

end Main

/-! ## The canonical trivialisations -/

section Canonical

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R] {I : Ideal R}
variable [Nontrivial (R ⧸ I)]
variable {E F : LinearTwoTermComplex (R ⧸ I)}
variable [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
variable [Module.Free (R ⧸ I) E.degreeOne] [Module.Finite (R ⧸ I) E.degreeOne]
variable [Module.Free (R ⧸ I) F.degreeZero] [Module.Finite (R ⧸ I) F.degreeZero]
variable [Module.Free (R ⧸ I) F.degreeOne] [Module.Finite (R ⧸ I) F.degreeOne]
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
variable (ψ : LinearTwoTermComplex.Hom F (conormalComplex k R I))

omit [IsNoetherianRing R] in
/-- **A quasi-isomorphism preserves the virtual dimension.**  This is the rank identity
`finrank_add_finrank_of_quasiIso` rewritten as `vd ψ = vd φ`. -/
theorem virtualDimension_eq_of_quasiIso
    (f : LinearTwoTermComplex.Hom E F) (hf : f.IsQuasiIsomorphism) :
    VirtualClass.virtualDimension ψ = VirtualClass.virtualDimension φ := by
  have hrank := finrank_add_finrank_of_quasiIso f hf
  change ((Module.finrank (R ⧸ I) F.degreeOne : ℤ)) - (Module.finrank (R ⧸ I) F.degreeZero : ℤ) =
    ((Module.finrank (R ⧸ I) E.degreeOne : ℤ)) - (Module.finrank (R ⧸ I) E.degreeZero : ℤ)
  omega

/-- **Behrend–Fantechi, Proposition 5.3 (quasi-isomorphism invariance), for the canonical
trivialisations.**

The left-hand side is the virtual fundamental class
`VirtualClass.virtualClass φ dimX dimE RX RE hhomE hinjE` of
`VirtualFundamentalClass/Construction.lean`.  The right-hand side is the virtual class of `ψ`,
computed in the canonical trivialisation of `F₁` and in the degree `virtualDimension φ`; by
`virtualDimension_eq_of_quasiIso` this degree is `virtualDimension ψ`, so by
`VirtualClass.virtualClassAt_trivialization` the right-hand side is the virtual class of `ψ`
in the sense of `Construction.lean` as well.  (It cannot be *written* as
`VirtualClass.virtualClass ψ …` here, because the degree of `RX` would then be the
syntactically different integer `virtualDimension ψ`.)

The remaining hypotheses are those of the intermediate complex `F ⊕ [E⁰ = E⁰]`. -/
theorem virtualClass_eq_of_quasiIso
    (f : LinearTwoTermComplex.Hom E F) (hf : f.IsQuasiIsomorphism)
    (hcomp : ψ.degreeZero.comp f.degreeZero = φ.degreeZero)
    (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (dimF : DimensionFunction (ResolvedCone.bundleSpace ψ))
    (dim₁ : DimensionFunction
      (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic ψ E.degreeOne)))
    (dim₂ : DimensionFunction
      (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic φ F.degreeOne)))
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX
      (VirtualClass.virtualDimension φ))
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE
      (VirtualClass.coneDegree φ))
    (RF : RationalEquivalenceSystem (ResolvedCone.bundleSpace ψ) dimF
      (VirtualClass.virtualDimension φ + (VirtualClass.bundleRank ψ : ℤ)))
    (R₁ : RationalEquivalenceSystem
      (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic ψ E.degreeOne)) dim₁
      (VirtualClass.virtualDimension φ +
        (VirtualClass.bundleRank (VirtualClass.sumAcyclic ψ E.degreeOne) : ℤ)))
    (R₂ : RationalEquivalenceSystem
      (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic φ F.degreeOne)) dim₂
      (VirtualClass.virtualDimension φ +
        (VirtualClass.bundleRank (VirtualClass.sumAcyclic ψ E.degreeOne) : ℤ)))
    (hhom₁ : PrincipalDivisorsHomogeneous
      (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic ψ E.degreeOne)) dim₁)
    (hinj₁ : Function.Injective (VectorBundle.chowPullbackBundle
      (VirtualClass.trivialization (VirtualClass.sumAcyclic ψ E.degreeOne)) dimX dim₁
      (VirtualClass.virtualDimension φ) RX R₁))
    (hhomE : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinjE : Function.Injective (VirtualClass.bundlePullback φ dimX dimE RX RE))
    (hhomF : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace ψ) dimF)
    (hinjF : Function.Injective (VectorBundle.chowPullbackBundle
      (VirtualClass.trivialization ψ) dimX dimF (VirtualClass.virtualDimension φ) RX RF)) :
    VirtualClass.virtualClass φ dimX dimE RX RE hhomE hinjE =
      VirtualClass.virtualClassAt ψ (VirtualClass.trivialization ψ) dimX dimF
        (VirtualClass.virtualDimension φ) RX RF hhomF hinjF := by
  rw [← VirtualClass.virtualClassAt_trivialization φ dimX dimE RX RE hhomE hinjE]
  exact virtualClassAt_eq_of_quasiIso φ ψ f hf hcomp (VirtualClass.trivialization φ)
    (VirtualClass.trivialization ψ)
    (VirtualClass.trivialization (VirtualClass.sumAcyclic ψ E.degreeOne))
    dimX dimE dimF dim₁ dim₂ (VirtualClass.virtualDimension φ) RX RE RF R₁ R₂
    (VirtualClass.card_chooseBasisIndex_sumAcyclic (E := F) E.degreeOne)
    (card_chooseBasisIndex_sum_of_quasiIso f hf) hhom₁ hinj₁ hhomE hinjE hhomF hinjF

end Canonical

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.QuasiIsoInvariance
