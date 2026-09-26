/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.ProjectiveBaseChange

/-!
# Tor amplitude of projective-perfect derived modules

`HasTorAmplitudeIn` is a statement about tensoring a concrete complex with every module.  This
file lifts it to the derived category only through bounded finite-projective representatives.  The
representative-independence theorem is proved by replacing a derived isomorphism with an actual
homotopy equivalence and then applying the additive tensor functor to that equivalence.

No tensor product of an arbitrary non-flat complex is used: all termwise tensor products below are
formed from projective representatives.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TensorProduct

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

namespace PerfectComplex

universe u

variable {R : Type u} [CommRing R]

section DerivedAmplitude

attribute [local instance] HasDerivedCategory.standard

/-! ## Derived amplitude and representative independence -/

/-- A derived module has Tor amplitude in `[a,b]` when one bounded finite-projective representative
has that amplitude.  The theorem `hasTorAmplitudeIn_of_projectiveDerivedIso` below proves that
this condition is independent of the chosen projective representative. -/
def HasProjectiveTorAmplitudeIn (E : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) : Prop :=
  ∃ K : CochainComplex (ModuleCat.{u} R) ℤ,
    IsStrictlyProjective K ∧ Nonempty (DerivedCategory.Q.obj K ≅ E) ∧
      HasTorAmplitudeIn K a b

namespace HasProjectiveTorAmplitudeIn

variable {E F : DerivedCategory (ModuleCat.{u} R)} {a b : ℤ}

/-- Tor amplitude is monotone under enlarging its interval. -/
theorem mono (h : HasProjectiveTorAmplitudeIn E a b) {a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b') :
    HasProjectiveTorAmplitudeIn E a' b' := by
  obtain ⟨K, hK, e, hAmp⟩ := h
  exact ⟨K, hK, e, hAmp.mono ha hb⟩

/-- Transport of the concrete Tor-amplitude statement across a derived isomorphism of projective
representatives. -/
theorem hasTorAmplitudeIn_of_projectiveDerivedIso
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyProjective K)
    (hL : IsStrictlyProjective L) (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L)
    (hAmp : HasTorAmplitudeIn K a b) : HasTorAmplitudeIn L a b := by
  obtain ⟨hEq, hEq_spec⟩ := exists_homotopyEquiv_of_projectiveDerivedIso hK hL e
  intro M i hi
  let hTensor : HomotopyEquiv (tensorRight K M) (tensorRight L M) :=
    Functor.mapHomotopyEquiv (MonoidalCategory.tensorRight M) hEq
  have hIso : (tensorRight K M).homology i ≅ (tensorRight L M).homology i :=
    hTensor.toHomologyIso i
  exact IsZero.of_iso (hAmp M i hi) hIso.symm

/-- The amplitude predicate is independent of the representative: every bounded finite-projective
representative of the same derived object has the same interval. -/
theorem of_rep
    (h : HasProjectiveTorAmplitudeIn E a b)
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyProjective K)
    (e : DerivedCategory.Q.obj K ≅ E) : HasTorAmplitudeIn K a b := by
  obtain ⟨L, hL, ⟨eL⟩, hAmp⟩ := h
  exact hasTorAmplitudeIn_of_projectiveDerivedIso hL hK (eL ≪≫ e.symm) hAmp

/-- Transport of projective Tor amplitude across a derived isomorphism. -/
theorem of_iso (h : HasProjectiveTorAmplitudeIn E a b) (e : E ≅ F) :
    HasProjectiveTorAmplitudeIn F a b := by
  obtain ⟨K, hK, eK, hAmp⟩ := h
  exact ⟨K, hK, ⟨eK.some ≪≫ e⟩, hAmp⟩

end HasProjectiveTorAmplitudeIn

/-- A supported bounded finite-projective representative gives the corresponding derived Tor
amplitude. -/
theorem hasProjectiveTorAmplitudeIn_of_isSupportedIn
    {E : DerivedCategory (ModuleCat.{u} R)} {a b : ℤ}
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyProjective K)
    (e : DerivedCategory.Q.obj K ≅ E) (hSupport : IsSupportedIn K a b) :
    HasProjectiveTorAmplitudeIn E a b :=
  ⟨K, hK, ⟨e⟩, hasTorAmplitudeIn_of_isSupportedIn hSupport⟩

/-- Every projective-perfect derived object has some finite Tor-amplitude interval. -/
theorem IsProjectivePerfect.hasProjectiveTorAmplitude
    {E : DerivedCategory (ModuleCat.{u} R)} (hE : IsProjectivePerfect E) :
    ∃ a b : ℤ, HasProjectiveTorAmplitudeIn E a b := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  obtain ⟨a, b, hSupport⟩ := hK.bounded
  exact ⟨a, b, hasProjectiveTorAmplitudeIn_of_isSupportedIn hK e hSupport⟩

end DerivedAmplitude

section SupportedOperations

attribute [local instance] HasDerivedCategory.standard

variable {S : Type u} [CommRing S] (f : R →+* S)

/-! ## Operations obtained directly from supported representatives -/

/-- Shifting a supported projective representative shifts its derived Tor-amplitude interval with
the cohomological sign convention `[a-n,b-n]`. -/
theorem hasProjectiveTorAmplitudeIn_shift_of_isSupportedIn
    {E : DerivedCategory (ModuleCat.{u} R)} {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyProjective K) (e : DerivedCategory.Q.obj K ≅ E)
    {a b n : ℤ} (hSupport : IsSupportedIn K a b) :
    HasProjectiveTorAmplitudeIn (E⟦n⟧) (a - n) (b - n) := by
  let K' := (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n).obj K
  have hK' : IsStrictlyProjective K' := hK.shift n
  have hSupport' : IsSupportedIn K' (a - n) (b - n) := hSupport.shift n
  refine hasProjectiveTorAmplitudeIn_of_isSupportedIn hK' ?_ hSupport'
  exact (DerivedCategory.Q.commShiftIso n).app K ≪≫
    (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} R)) n).mapIso e

/-- Base change of a supported projective representative has the same derived Tor-amplitude
interval over the target ring.  The proof uses support after scalar extension, so it makes no
flatness assumption on the ring map. -/
theorem hasProjectiveTorAmplitudeIn_baseChange_of_isSupportedIn
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyProjective K)
    {a b : ℤ} (hSupport : IsSupportedIn K a b) :
    HasProjectiveTorAmplitudeIn (R := S)
      (DerivedCategory.Q.obj ((Modules.Derived.baseChangeFunctor f).obj K)) a b := by
  have hK' : IsStrictlyProjective ((Modules.Derived.baseChangeFunctor f).obj K) :=
    hK.baseChange f
  have hSupport' : IsSupportedIn ((Modules.Derived.baseChangeFunctor f).obj K) a b := by
    intro i hi
    rw [Modules.Derived.baseChangeFunctor_obj]
    exact (ModuleCat.extendScalars f).map_isZero (hSupport i hi)
  exact hasProjectiveTorAmplitudeIn_of_isSupportedIn hK' (Iso.refl _) hSupport'

/-- Base change of the representative selected by a projective-perfect proof has the expected
derived Tor amplitude whenever that selected representative is supported in the interval. -/
theorem IsProjectivePerfect.derivedBaseChange_hasProjectiveTorAmplitudeIn_of_isSupportedIn
    {E : DerivedCategory (ModuleCat.{u} R)} (hE : IsProjectivePerfect E)
    {a b : ℤ} (hSupport : IsSupportedIn hE.rep a b) :
    HasProjectiveTorAmplitudeIn (R := S)
      (IsProjectivePerfect.derivedBaseChange f hE) a b := by
  exact hasProjectiveTorAmplitudeIn_baseChange_of_isSupportedIn f
    hE.rep_isStrictlyProjective hSupport

end SupportedOperations

end PerfectComplex

end GromovWitten.AlgebraicGeometry.CotangentComplex
