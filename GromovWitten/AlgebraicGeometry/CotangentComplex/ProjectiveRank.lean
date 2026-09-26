/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.ProjectivePerfect
import GromovWitten.AlgebraicGeometry.CotangentComplex.ProjectiveBaseChange
import GromovWitten.AlgebraicGeometry.CotangentComplex.PerfectRank
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Stalkwise virtual rank of bounded finite-projective complexes

For a bounded complex of finite-projective modules, the rank at a point of `Spec R` is the
alternating sum of the ranks of the terms after localization at that point.  In particular this
definition does not assign a single rank to an arbitrary projective module: the rank is a
function on the spectrum.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TensorProduct

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

namespace PerfectComplex

universe u

variable {R : Type u} [CommRing R]

/-! ## The pointwise rank -/

/-- The stalkwise rank of a module term at a prime of `R`. -/
noncomputable def termRankAt (M : ModuleCat.{u} R) (p : PrimeSpectrum R) : ℤ :=
  Module.rankAtStalk (R := R) (M : Type u) p

/-- The pointwise virtual rank of a complex, as an alternating `finsum` over its terms. -/
noncomputable def projectiveRankAt (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (p : PrimeSpectrum R) : ℤ :=
  ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * termRankAt (K.X i) p

set_option linter.style.haveILetI false in
private theorem termRankAt_eq_zero_of_isZero [Nontrivial R] {M : ModuleCat.{u} R}
    (hM : IsZero M) (p : PrimeSpectrum R) : termRankAt M p = 0 := by
  letI : Subsingleton (M : Type u) := ModuleCat.isZero_iff_subsingleton.mp hM
  change (Module.rankAtStalk (R := R) (M : Type u) p : ℤ) = 0
  have hzero : Module.rankAtStalk (R := R) (M : Type u) = 0 :=
    Module.rankAtStalk_eq_zero_of_subsingleton
  rw [hzero]
  simp

private theorem projectiveRankAt_eq_sum_Icc [Nontrivial R]
    {K : CochainComplex (ModuleCat.{u} R) ℤ} {a b : ℤ}
    (hK : IsSupportedIn K a b) (p : PrimeSpectrum R) :
    projectiveRankAt K p =
      ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) * termRankAt (K.X i) p := by
  refine finsum_eq_finsetSum_of_support_subset _ ?_
  intro i hi
  simp only [Finset.coe_Icc, Set.mem_Icc]
  by_contra hcon
  apply hi
  change (i.negOnePow : ℤ) * termRankAt (K.X i) p = 0
  rw [termRankAt_eq_zero_of_isZero (hK i (by omega))]
  simp

/-! The finite sum presentation is independent of the chosen support interval. -/

/-- Two support intervals compute the same stalkwise virtual rank. -/
theorem projectiveRankAt_eq_sum_Icc_of_supported [Nontrivial R]
    {K : CochainComplex (ModuleCat.{u} R) ℤ} {a b a' b' : ℤ}
    (hK : IsSupportedIn K a b) (hK' : IsSupportedIn K a' b') (p : PrimeSpectrum R) :
    (∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) * termRankAt (K.X i) p) =
      ∑ i ∈ Finset.Icc a' b', (i.negOnePow : ℤ) * termRankAt (K.X i) p := by
  rw [← projectiveRankAt_eq_sum_Icc hK p, ← projectiveRankAt_eq_sum_Icc hK' p]

/-- A termwise isomorphism of complexes preserves the stalkwise virtual rank. -/
theorem projectiveRankAt_congr
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (e : K ≅ L) (p : PrimeSpectrum R) :
    projectiveRankAt K p = projectiveRankAt L p := by
  unfold projectiveRankAt
  apply finsum_congr
  intro i
  have hterm : termRankAt (K.X i) p = termRankAt (L.X i) p := by
    change (Module.rankAtStalk (R := R) (K.X i : Type u) p : ℤ) =
      (Module.rankAtStalk (R := R) (L.X i : Type u) p : ℤ)
    have h := congrFun (Module.rankAtStalk_eq_of_equiv
    (((HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i).mapIso e).toLinearEquiv)) p
    exact congrArg (fun n : ℕ => (n : ℤ)) h
  rw [hterm]

/-! ## Scalar extension -/

section BaseChange

variable {S : Type u} [CommRing S] (f : R →+* S)

/- Stalk rank commutes with extension of scalars. -/
set_option linter.style.haveILetI false in
theorem termRankAt_baseChange (M : ModuleCat.{u} R) (hM : IsFiniteProjective M)
    (p : PrimeSpectrum S) :
    termRankAt ((ModuleCat.extendScalars f).obj M) p = termRankAt M (p.comap f) := by
  letI : Algebra R S := f.toAlgebra
  haveI : Module.Finite R (M : Type u) := hM.finite
  haveI : Module.Projective R (M : Type u) := hM.projective
  haveI : Module.Flat R (M : Type u) := Module.Flat.of_projective
  change (Module.rankAtStalk (R := S) (S ⊗[R] (M : Type u)) p : ℤ) =
    (Module.rankAtStalk (R := R) (M : Type u) (p.comap f) : ℤ)
  rw [Module.rankAtStalk_baseChange]
  simp only [RingHom.algebraMap_toAlgebra]

/-- The stalkwise virtual rank pulls back along the map of spectra induced by scalar extension. -/
theorem projectiveRankAt_baseChange
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : IsStrictlyProjective K)
    (p : PrimeSpectrum S) :
    projectiveRankAt (baseChange f K) p = projectiveRankAt K (p.comap f) := by
  unfold projectiveRankAt
  apply finsum_congr
  intro i
  rw [baseChange_X, termRankAt_baseChange f _ (hK.finiteProjective i)]

end BaseChange

/-! ## Homotopy invariance -/

set_option linter.style.haveILetI false in
private theorem isStrictlyPerfect_localization [Nontrivial R]
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyProjective K)
    (p : PrimeSpectrum R) :
    IsStrictlyPerfect
      (baseChange (algebraMap R (Localization.AtPrime p.asIdeal)) K) := by
  let S := Localization.AtPrime p.asIdeal
  let f : R →+* S := algebraMap R S
  let L := baseChange f K
  refine ⟨?_, ?_⟩
  · obtain ⟨a, b, hab⟩ := hK.bounded
    exact ⟨a, b, fun i hi => by
      change IsZero ((baseChange f K).X i)
      rw [baseChange_X]
      exact (ModuleCat.extendScalars f).map_isZero (hab i hi)⟩
  · intro i
    change IsFiniteFree ((baseChange f K).X i)
    rw [baseChange_X]
    have hM := (hK.finiteProjective i).extendScalars f
    haveI : Module.Finite S ((ModuleCat.extendScalars f).obj (K.X i) : Type u) := hM.finite
    haveI : Module.Projective S ((ModuleCat.extendScalars f).obj (K.X i) : Type u) := hM.projective
    haveI : Module.Flat S ((ModuleCat.extendScalars f).obj (K.X i) : Type u) :=
      Module.Flat.of_projective
    exact ⟨Module.free_of_flat_of_isLocalRing, hM.finite⟩

set_option linter.style.haveILetI false in
private theorem termRankAt_eq_localized_rank [Nontrivial R]
    (M : ModuleCat.{u} R) (hM : IsFiniteProjective M) (p : PrimeSpectrum R) :
    termRankAt M p =
      (rankOf ((ModuleCat.extendScalars (algebraMap R
        (Localization.AtPrime p.asIdeal))).obj M) : ℤ) := by
  let S := Localization.AtPrime p.asIdeal
  let f : R →+* S := algebraMap R S
  let q : PrimeSpectrum S := ⟨IsLocalRing.maximalIdeal S, inferInstance⟩
  have hq : q.comap f = p := by
    apply PrimeSpectrum.ext
    change (IsLocalRing.maximalIdeal S).comap f = p.asIdeal
    exact Localization.AtPrime.under_maximalIdeal
  have hbase := termRankAt_baseChange f M hM q
  rw [hq] at hbase
  have hM' := hM.extendScalars f
  haveI : Module.Finite S ((ModuleCat.extendScalars f).obj M : Type u) := hM'.finite
  haveI : Module.Projective S ((ModuleCat.extendScalars f).obj M : Type u) := hM'.projective
  haveI : Module.Flat S ((ModuleCat.extendScalars f).obj M : Type u) :=
    Module.Flat.of_projective
  haveI : Module.Free S ((ModuleCat.extendScalars f).obj M : Type u) :=
    Module.free_of_flat_of_isLocalRing
  have hfree := Module.rankAtStalk_eq_finrank_of_free
    (R := S) (M := ((ModuleCat.extendScalars f).obj M : Type u))
  have hfin : termRankAt ((ModuleCat.extendScalars f).obj M) q =
      (rankOf ((ModuleCat.extendScalars f).obj M) : ℤ) := by
    change (Module.rankAtStalk (R := S)
      ((ModuleCat.extendScalars f).obj M : Type u) q : ℤ) = _
    exact congrArg (fun n : ℕ => (n : ℤ)) (congrFun hfree q)
  exact hbase.symm.trans hfin

/-- Homotopy equivalent bounded finite-projective complexes have equal stalkwise virtual rank. -/
theorem projectiveRankAt_eq_of_homotopyEquiv [Nontrivial R]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyProjective K) (hL : IsStrictlyProjective L)
    (e : HomotopyEquiv K L) (p : PrimeSpectrum R) :
    projectiveRankAt K p = projectiveRankAt L p := by
  let S := Localization.AtPrime p.asIdeal
  let f : R →+* S := algebraMap R S
  let K' := baseChange f K
  let L' := baseChange f L
  have hK' : IsStrictlyPerfect K' := isStrictlyPerfect_localization hK p
  have hL' : IsStrictlyPerfect L' := isStrictlyPerfect_localization hL p
  have he' : HomotopyEquiv K' L' :=
    Functor.mapHomotopyEquiv (ModuleCat.extendScalars f) e
  have hrank : PerfectComplex.rank K' = PerfectComplex.rank L' :=
    rank_eq_of_homotopyEquiv hK' hL' he'
  unfold projectiveRankAt
  rw [show (∑ᶠ i : ℤ, (i.negOnePow : ℤ) * termRankAt (K.X i) p) =
      PerfectComplex.rank K' by
        unfold PerfectComplex.rank K'
        apply finsum_congr
        intro i
        rw [termRankAt_eq_localized_rank _ (hK.finiteProjective i)]
        rfl,
    show (∑ᶠ i : ℤ, (i.negOnePow : ℤ) * termRankAt (L.X i) p) =
      PerfectComplex.rank L' by
        unfold PerfectComplex.rank L'
        apply finsum_congr
        intro i
        rw [termRankAt_eq_localized_rank _ (hL.finiteProjective i)]
        rfl]
  exact hrank

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- A derived isomorphism between projective representatives preserves stalkwise virtual rank.
The comparison is obtained from the K-projective homotopy-equivalence lifting theorem. -/
theorem projectiveRankAt_eq_of_projectiveDerivedIso [Nontrivial R]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyProjective K) (hL : IsStrictlyProjective L)
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) (p : PrimeSpectrum R) :
    projectiveRankAt K p = projectiveRankAt L p := by
  obtain ⟨h, _⟩ := exists_homotopyEquiv_of_projectiveDerivedIso hK hL e
  exact projectiveRankAt_eq_of_homotopyEquiv hK hL h p

/-- The stalkwise virtual rank attached to a projective-perfect derived representative. -/
noncomputable def IsProjectivePerfect.rankAt
    {E : DerivedCategory (ModuleCat.{u} R)} (hE : IsProjectivePerfect E)
    (p : PrimeSpectrum R) : ℤ :=
  projectiveRankAt hE.rep p

@[simp]
theorem IsProjectivePerfect.rankAt_eq_of_rep [Nontrivial R]
    {E : DerivedCategory (ModuleCat.{u} R)} (hE : IsProjectivePerfect E)
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyProjective K)
    (e : DerivedCategory.Q.obj K ≅ E) (p : PrimeSpectrum R) :
    hE.rankAt p = projectiveRankAt K p := by
  obtain ⟨h, _⟩ := exists_homotopyEquiv_of_projectiveDerivedIso
    hE.rep_isStrictlyProjective hK (hE.repIso ≪≫ e.symm)
  exact projectiveRankAt_eq_of_homotopyEquiv hE.rep_isStrictlyProjective hK h p

/-- Derived isomorphisms preserve the virtual rank function. -/
theorem IsProjectivePerfect.rankAt_congr [Nontrivial R]
    {E F : DerivedCategory (ModuleCat.{u} R)}
    (hE : IsProjectivePerfect E) (hF : IsProjectivePerfect F)
    (e : E ≅ F) (p : PrimeSpectrum R) : hE.rankAt p = hF.rankAt p :=
  hE.rankAt_eq_of_rep hF.rep_isStrictlyProjective (hF.repIso ≪≫ e.symm) p

/-- Derived scalar extension pulls the virtual rank function back along the map of spectra. -/
theorem IsProjectivePerfect.rankAt_derivedBaseChange
    {S : Type u} [CommRing S] [Nontrivial S] (f : R →+* S)
    {E : DerivedCategory (ModuleCat.{u} R)} (hE : IsProjectivePerfect E)
    (p : PrimeSpectrum S) :
    (hE.derivedBaseChange_isProjectivePerfect f).rankAt p = hE.rankAt (p.comap f) := by
  rw [(hE.derivedBaseChange_isProjectivePerfect f).rankAt_eq_of_rep
    (hE.rep_isStrictlyProjective.baseChange f) (Iso.refl _) p]
  exact projectiveRankAt_baseChange f hE.rep hE.rep_isStrictlyProjective p

end Derived

/-! ## Local constancy -/

set_option linter.style.haveILetI false in
private theorem isLocallyConstant_termRankAt [Nontrivial R]
    {M : ModuleCat.{u} R} (hM : IsFiniteProjective M) :
    IsLocallyConstant (termRankAt (R := R) M) := by
  haveI : Module.Finite R (M : Type u) := hM.finite
  haveI : Module.Projective R (M : Type u) := hM.projective
  haveI : Module.FinitePresentation R (M : Type u) :=
    Module.finitePresentation_of_projective R (M : Type u)
  haveI : Module.Flat R (M : Type u) := Module.Flat.of_projective
  change IsLocallyConstant (fun p => (Module.rankAtStalk (R := R) (M : Type u) p : ℤ))
  exact (Module.isLocallyConstant_rankAtStalk (R := R) (M := (M : Type u))).comp
    (fun n => (n : ℤ))

/-- The stalkwise virtual rank of a bounded finite-projective complex is locally constant. -/
theorem isLocallyConstant_projectiveRankAt [Nontrivial R]
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyProjective K) :
    IsLocallyConstant (projectiveRankAt (R := R) K) := by
  obtain ⟨a, b, hab⟩ := hK.bounded
  rw [show projectiveRankAt (R := R) K =
      fun p => ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) * termRankAt (K.X i) p by
    funext p; exact projectiveRankAt_eq_sum_Icc hab p]
  have hsum : ∀ s : Finset ℤ,
      IsLocallyConstant (fun p =>
        ∑ i ∈ s, (i.negOnePow : ℤ) * termRankAt (K.X i) p) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        convert IsLocallyConstant.const (X := PrimeSpectrum R) (0 : ℤ) using 1
        · ext p
          simp
    | @insert i s hi ih =>
        have hsum_insert :
            (fun p => ∑ j ∈ insert i s, (j.negOnePow : ℤ) * termRankAt (K.X j) p) =
              (fun p => (i.negOnePow : ℤ) * termRankAt (K.X i) p +
                ∑ j ∈ s, (j.negOnePow : ℤ) * termRankAt (K.X j) p) := by
          funext p
          rw [Finset.sum_insert hi]
        rw [hsum_insert]
        have hi' := (IsLocallyConstant.const (X := PrimeSpectrum R)
          (i.negOnePow : ℤ)).comp₂ (isLocallyConstant_termRankAt (hK.finiteProjective i))
          (fun n z => n * z)
        exact hi'.comp₂ ih (fun z w => z + w)
  exact hsum (Finset.Icc a b)

section DerivedRank

attribute [local instance] HasDerivedCategory.standard

theorem IsProjectivePerfect.isLocallyConstant_rankAt [Nontrivial R]
    {E : DerivedCategory (ModuleCat.{u} R)} (hE : IsProjectivePerfect E) :
    IsLocallyConstant hE.rankAt := by
  exact isLocallyConstant_projectiveRankAt hE.rep_isStrictlyProjective

end DerivedRank

end PerfectComplex

end GromovWitten.AlgebraicGeometry.CotangentComplex
