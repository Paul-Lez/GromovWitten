/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/

import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.RegularLocalRing.Defs
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.ComponentIntersection

/-!
# Dimension of the local rings of an arithmetic surface along the special fibre

Let `M` be a model of a curve over a discrete valuation ring `R` whose total space is regular and
whose structure morphism is proper (an `ArithmeticSurface`).  This file computes the Krull
dimension of the local rings of the total space at the points of the special fibre and derives the
consequences for the intersection theory of `ComponentIntersection.lean`.

## Commutative algebra

* `IsRegularLocalRing.isDomain`: **a regular local ring is an integral domain**.  This is a gap in
  Mathlib (`Mathlib/RingTheory/RegularLocalRing/Defs.lean` has no such result); it is proved here
  by the standard induction on the number of generators of the maximal ideal (Stacks 00NP), using
  prime avoidance (`exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes`), the
  generator-exchange lemma `exists_finset_maximalIdeal_eq_span_insert` and Nakayama's lemma.
* `IsRegularLocalRing.isDiscreteValuationRing_of_ringKrullDim_eq_one`: a regular local ring of
  Krull dimension one is a discrete valuation ring.
* `krullDimLE_zero_quotient_of_radical_eq_maximalIdeal`,
  `ringKrullDim_quotient_eq_zero_of_radical_eq_maximalIdeal`,
  `length_quotient_ne_top_of_krullDimLE_zero`: an ideal of a local ring whose radical is the
  maximal ideal has zero-dimensional quotient, and a zero-dimensional quotient of a Noetherian
  ring has finite length.

## Geometry of the special fibre

* `baseStalkHom_flat`, `isSMulRegular_baseElementGerm`: the stalk of the total space of a model at
  any point is flat over the base ring, so the germ of a nonzero element of the base ring is a
  nonzerodivisor there.  (Flatness of `M.toBase` is part of the data of a `Model`.)
* `ringKrullDim_quotient_baseElementGerm_succ`: Krull's principal ideal theorem in the present
  setting — cutting the stalk at a point of the special fibre by the germ of a uniformiser drops
  the Krull dimension by exactly one.
* `range_specialFiberι`: a point of the total space lies on the special fibre exactly when it lies
  over the closed point of the base (the converse of `toBase_specialFiberι`).
* `eq_genericPoint_of_mem_closure`: a point of the special fibre whose closure contains the generic
  point of a component *is* that generic point.
* `mem_basicOpen_fromSpecStalk`: the dictionary between primes of a stalk and points of the scheme,
  in the form needed to test vanishing of a global section.
* `radical_span_baseElementGerm_genericPoint`: **unconditionally**, the germ of a uniformiser at the
  generic point of a component of the special fibre generates an ideal with radical the maximal
  ideal.
* `ringKrullDim_stalk_genericPoint`, `isDiscreteValuationRing_stalk_genericPoint`:
  **unconditionally**, the local ring of the total space at the generic point of a component of the
  special fibre has Krull dimension one, hence is a discrete valuation ring.
* `ringKrullDim_stalk_eq_two`: at a point of the special fibre at which the fibre is
  one-dimensional (a closed point of a component of a curve) the stalk has Krull dimension two.
  Here the one-dimensionality of the fibre is an explicit hypothesis, see below.
* `componentMultiplicity_ne_top_of_span_eq`, `componentMultiplicityNat`,
  `componentMultiplicityNat_pos_of_span_eq`: **unconditionally**, the multiplicity with which a
  component occurs in the special fibre is a genuine (positive) natural number.
* `componentIntersection_ne_top_of_krullDimLE_zero`,
  `componentIntersection_ne_top_of_radical_eq`, `componentIntersectionNat`: finiteness of the
  intersection number of two components, with the Noetherian hypothesis of
  `componentIntersection_ne_top` discharged by regularity and its radical hypothesis weakened to
  zero-dimensionality of the local intersection algebra.

## The remaining fibre-dimension hypotheses

Two things are *not* derived here.

1. The dimension of the special fibre at a *closed* point.  It enters `ringKrullDim_stalk_eq` (and
   hence `ringKrullDim_stalk_eq_two`) as the explicit hypothesis
   `ringKrullDim (𝒪_{M,x} ⧸ (π)) = 1`, the dimension of the local ring of the scheme-theoretic
   special fibre at `x`; equivalently, via
   `ringKrullDim_quotient_eq_zero_of_radical_eq_maximalIdeal`, zero-dimensionality is the
   set-theoretic statement that the special fibre is near `x` just the point `x`.  Deriving the
   value `1` needs the identification of the stalk of the scheme-theoretic special fibre at `x`
   with `𝒪_{M,x} ⧸ (π)` (base change along the closed immersion `Spec (R/m) → Spec R`, whose ideal
   is generated by a uniformiser) together with the fact that a curve over a field is
   one-dimensional at its closed points; neither is available in the repository or in Mathlib.
2. Finiteness of the intersection locus of two distinct components, and zero-dimensionality of the
   local intersection algebra there.  `genericPoint_notMem_componentCloseds` shows unconditionally
   that the locus is a proper closed subset of each component; that it is finite again needs the
   components to be curves.
-/

universe u

open IsLocalRing
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace IsRegularLocalRing

section Noetherian

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- **Nakayama's lemma** for the maximal ideal of a Noetherian local ring: a nonzero maximal
ideal is not contained in its own square. -/
theorem maximalIdeal_not_le_sq (h : maximalIdeal A ≠ ⊥) :
    ¬ maximalIdeal A ≤ maximalIdeal A ^ 2 := by
  intro hle
  refine h (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal A) (maximalIdeal A)
    (IsNoetherian.noetherian _) ?_ ?_)
  · rwa [Ideal.smul_eq_mul, ← pow_two]
  · exact le_of_eq (jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm

/-- **Prime avoidance** in a Noetherian local ring: if the maximal ideal is contained neither in
its square nor in any minimal prime, then some element of the maximal ideal avoids the square and
every minimal prime. -/
theorem exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes
    (h2 : ¬ maximalIdeal A ≤ maximalIdeal A ^ 2)
    (hmin : ∀ p ∈ minimalPrimes A, ¬ maximalIdeal A ≤ p) :
    ∃ x ∈ maximalIdeal A, x ∉ maximalIdeal A ^ 2 ∧ ∀ p ∈ minimalPrimes A, x ∉ p := by
  classical
  have hfin : (insert (maximalIdeal A ^ 2) (minimalPrimes A)).Finite :=
    (minimalPrimes.finite_of_isNoetherianRing (R := A)).insert _
  have hprime : ∀ I ∈ insert (maximalIdeal A ^ 2) (minimalPrimes A),
      I ≠ maximalIdeal A ^ 2 → I ≠ maximalIdeal A ^ 2 → I.IsPrime := by
    intro I hI hne _
    exact (Set.mem_insert_iff.mp hI).resolve_left hne |>.isPrime
  have hsub : ¬ ((maximalIdeal A : Set A) ⊆
      ⋃ I ∈ insert (maximalIdeal A ^ 2) (minimalPrimes A), (I : Set A)) := by
    rw [Ideal.subset_union_prime_finite hfin (maximalIdeal A ^ 2) (maximalIdeal A ^ 2) hprime]
    rintro ⟨I, hI, hle⟩
    rcases Set.mem_insert_iff.mp hI with rfl | hI
    · exact h2 hle
    · exact hmin I hI hle
  obtain ⟨x, hxm, hx⟩ := Set.not_subset.mp hsub
  refine ⟨x, hxm, fun hx2 => hx ?_, fun p hp hxp => hx ?_⟩
  · exact Set.mem_biUnion (Set.mem_insert _ _) hx2
  · exact Set.mem_biUnion (Set.mem_insert_of_mem _ hp) hxp

/-- If `x` belongs to the maximal ideal of a Noetherian local ring but not to its square, then a
minimal system of generators of the maximal ideal can be chosen to contain `x`: there is a set of
`(maximalIdeal A).spanFinrank - 1` further elements which, together with `x`, generate. -/
theorem exists_finset_maximalIdeal_eq_span_insert {x : A} (hx : x ∈ maximalIdeal A)
    (hx2 : x ∉ maximalIdeal A ^ 2) {n : ℕ} (hn : (maximalIdeal A).spanFinrank = n + 1) :
    ∃ t : Finset A, t.card ≤ n ∧ (t : Set A) ⊆ (maximalIdeal A : Set A) ∧
      maximalIdeal A = Ideal.span (insert x (t : Set A)) := by
  classical
  obtain ⟨s, hcard, hspan⟩ :=
    (IsNoetherian.noetherian (maximalIdeal A)).exists_span_finset_card_eq_spanFinrank
  rw [hn] at hcard
  have hsm : (s : Set A) ⊆ (maximalIdeal A : Set A) := fun a ha => hspan ▸ Ideal.subset_span ha
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp (hspan ▸ hx)
  have hex : ∃ i ∈ s, f i ∉ maximalIdeal A := by
    by_contra hcon
    push Not at hcon
    refine hx2 (hf ▸ Ideal.sum_mem _ fun i hi => ?_)
    rw [smul_eq_mul, pow_two]
    exact Ideal.mul_mem_mul (hcon i hi) (hsm hi)
  obtain ⟨i, his, hfi⟩ := hex
  have hunit : IsUnit (f i) := by
    by_contra hcon
    exact hfi ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hcon))
  refine ⟨s.erase i, ?_, fun a ha => hsm (Finset.mem_of_mem_erase ha), le_antisymm ?_ ?_⟩
  · have := Finset.card_erase_of_mem his
    omega
  · rw [← hspan, Ideal.span_le]
    intro a ha
    by_cases hai : a = i
    · subst hai
      have hmem : f a * a ∈ Ideal.span (insert x ((s.erase a : Finset A) : Set A)) := by
        have hsum : f a * a = x - ∑ j ∈ s.erase a, f j • j := by
          rw [← hf, ← Finset.add_sum_erase s _ his, smul_eq_mul]
          ring
        rw [hsum]
        refine Ideal.sub_mem _ (Ideal.subset_span (Set.mem_insert _ _))
          (Ideal.sum_mem _ fun j hj => ?_)
        exact Ideal.mul_mem_left _ _
          (Ideal.subset_span (Set.mem_insert_of_mem _ (by exact_mod_cast hj)))
      exact (Ideal.unit_mul_mem_iff_mem _ hunit).mp hmem
    · exact Ideal.subset_span
        (Set.mem_insert_of_mem _ (by exact_mod_cast Finset.mem_erase.mpr ⟨hai, ha⟩))
  · rw [Ideal.span_le]
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact hx
    · exact hsm (Finset.mem_of_mem_erase (by exact_mod_cast ha))

end Noetherian

section Domain

/-- Auxiliary statement for `IsRegularLocalRing.isDomain`, set up for induction on the number of
generators of the maximal ideal. -/
private theorem isDomain_aux : ∀ (n : ℕ) (A : Type u) [CommRing A] [IsRegularLocalRing A],
    (maximalIdeal A).spanFinrank = n → IsDomain A := by
  intro n
  induction n with
  | zero =>
    intro A _ _ hn
    have hbot : maximalIdeal A = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp hn
    let _ := (isField_iff_maximalIdeal_eq.mpr hbot).toField
    infer_instance
  | succ n ih =>
    intro A _ _ hn
    have hdim : ringKrullDim A = ((n + 1 : ℕ) : WithBot ℕ∞) := by
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := A), hn]
    have hmne : maximalIdeal A ≠ ⊥ := by
      intro h
      rw [h, Submodule.spanFinrank_bot] at hn
      omega
    have hmin : ∀ p ∈ minimalPrimes A, ¬ maximalIdeal A ≤ p := by
      intro p hp hle
      have hpr : p.IsPrime := hp.isPrime
      have hpe : p = maximalIdeal A := le_antisymm (le_maximalIdeal hpr.ne_top) hle
      have h0 : (maximalIdeal A).height = 0 := Ideal.height_eq_zero_iff.mpr (hpe ▸ hp)
      rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h0] at hdim
      have hcontra : (0 : ℕ) = n + 1 := by exact_mod_cast hdim
      omega
    obtain ⟨x, hx, hx2, hxmin⟩ := exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes A
      (maximalIdeal_not_le_sq A hmne) hmin
    obtain ⟨t, htcard, -, htspan⟩ := exists_finset_maximalIdeal_eq_span_insert A hx hx2 hn
    have hIle : Ideal.span {x} ≤ maximalIdeal A := (Ideal.span_singleton_le_iff_mem _).mpr hx
    have hIne : Ideal.span {x} ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top hIle
    let _ : Nontrivial (A ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hIne
    let _ : IsLocalRing (A ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    have hspanB : maximalIdeal (A ⧸ Ideal.span {x}) =
        Ideal.span (Ideal.Quotient.mk (Ideal.span {x}) '' (t : Set A)) := by
      rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (Ideal.span {x}))
        Ideal.Quotient.mk_surjective, htspan, Ideal.map_span, Set.image_insert_eq,
        show (Ideal.Quotient.mk (Ideal.span {x})) x = 0 from
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)]
      exact Ideal.span_insert_zero
    have hBrank : (maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank ≤ n := by
      rw [hspanB]
      refine le_trans (Submodule.spanFinrank_span_le_ncard_of_finite
        ((t : Set A).toFinite.image _)) ?_
      calc (Ideal.Quotient.mk (Ideal.span {x}) '' (t : Set A)).ncard
          ≤ (t : Set A).ncard := Set.ncard_image_le (t : Set A).toFinite
        _ = t.card := by simp
        _ ≤ n := htcard
    have hle1 : ringKrullDim A ≤ ringKrullDim (A ⧸ Ideal.span {x}) + 1 := by
      refine le_trans (ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (Ideal.span {x})
        (by rw [ringJacobson_eq_maximalIdeal]; exact hIle)) (add_le_add le_rfl ?_)
      have h1 : (Ideal.span {x} : Ideal A).spanFinrank ≤ 1 := by
        refine le_trans (Submodule.spanFinrank_span_le_ncard_of_finite
          (Set.finite_singleton x)) ?_
        simp
      exact_mod_cast h1
    have hlow : ((n : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ Ideal.span {x}) := by
      rw [← ENat.WithBot.add_le_add_one_right_iff]
      calc ((n : ℕ) : WithBot ℕ∞) + 1 = ((n + 1 : ℕ) : WithBot ℕ∞) := by push_cast; ring
        _ = ringKrullDim A := hdim.symm
        _ ≤ ringKrullDim (A ⧸ Ideal.span {x}) + 1 := hle1
    have hBrank' : (maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank = n := by
      have h1 : ((n : ℕ) : WithBot ℕ∞) ≤
          (((maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank : ℕ) : WithBot ℕ∞) :=
        hlow.trans (ringKrullDim_le_spanFinrank_maximalIdeal (A ⧸ Ideal.span {x}))
      have h2 : n ≤ (maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank := by exact_mod_cast h1
      omega
    let _ : IsRegularLocalRing (A ⧸ Ideal.span {x}) :=
      of_spanFinrank_maximalIdeal_le _ (by rw [hBrank']; exact hlow)
    have hBdom : IsDomain (A ⧸ Ideal.span {x}) := ih (A ⧸ Ideal.span {x}) hBrank'
    let _ : (Ideal.span {x} : Ideal A).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime (Ideal.span {x})).mp hBdom
    obtain ⟨q, hq, hqle⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := Ideal.span {x}) bot_le
    have hqsmul : q ≤ maximalIdeal A • q := by
      intro y hy
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp (hqle hy)
      have hyq : x * z ∈ q := by rw [← hz]; exact hy
      have hzq : z ∈ q :=
        (hq.isPrime.mem_or_mem hyq).resolve_left (hxmin q hq)
      rw [hz, Ideal.smul_eq_mul]
      exact Ideal.mul_mem_mul hx hzq
    have hq0 : q = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _
      (IsNoetherian.noetherian _) hqsmul (le_of_eq (jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm)
    let _ : (⊥ : Ideal A).IsPrime := hq0 ▸ hq.isPrime
    exact IsDomain.of_bot_isPrime A

/-- **A regular local ring is an integral domain.**  This is not in Mathlib; the proof is the
standard induction on the Krull dimension (Stacks 00NP): a generator of the maximal ideal outside
its square and outside every minimal prime cuts out a regular local quotient of one dimension
less, which is a domain by induction, so the principal ideal it generates is prime and Nakayama's
lemma forces the minimal prime inside it to vanish. -/
theorem isDomain (A : Type u) [CommRing A] [IsRegularLocalRing A] : IsDomain A :=
  isDomain_aux (maximalIdeal A).spanFinrank A rfl

/-- A regular local ring of Krull dimension one is a discrete valuation ring. -/
theorem isDiscreteValuationRing_of_ringKrullDim_eq_one (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (h : ringKrullDim A = 1) :
    letI := isDomain A; IsDiscreteValuationRing A := by
  let _ := isDomain A
  rw [← IsLocalRing.finrank_CotangentSpace_eq_one_iff]
  have h1 := (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp inferInstance
  rw [h] at h1
  exact_mod_cast h1

end Domain

end IsRegularLocalRing

/-! ### Finite length of zero-dimensional quotients -/

/-- In a local ring, an ideal whose radical is the maximal ideal has zero-dimensional quotient:
the only prime of the quotient is the maximal ideal. -/
theorem krullDimLE_zero_quotient_of_radical_eq_maximalIdeal {A : Type u} [CommRing A]
    [IsLocalRing A] {J : Ideal A} (hJ : J.radical = maximalIdeal A) :
    Ring.KrullDimLE 0 (A ⧸ J) := by
  have key : ∀ P : PrimeSpectrum (A ⧸ J),
      P.asIdeal.comap (Ideal.Quotient.mk J) = maximalIdeal A := by
    intro P
    have hle : J ≤ P.asIdeal.comap (Ideal.Quotient.mk J) := by
      intro y hy
      have hy0 : (Ideal.Quotient.mk J) y = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hy
      have : (Ideal.Quotient.mk J) y ∈ P.asIdeal := by rw [hy0]; exact P.asIdeal.zero_mem
      exact this
    have hprime : (P.asIdeal.comap (Ideal.Quotient.mk J)).IsPrime := inferInstance
    refine le_antisymm (le_maximalIdeal hprime.ne_top) ?_
    rw [← hJ]
    exact (Ideal.IsPrime.radical_le_iff hprime).mpr hle
  have hsub : Subsingleton (PrimeSpectrum (A ⧸ J)) := by
    refine ⟨fun P Q => PrimeSpectrum.ext ?_⟩
    have hinj := Ideal.comap_injective_of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective
    exact hinj ((key P).trans (key Q).symm)
  exact ⟨Order.krullDim_nonpos_of_subsingleton⟩


/-- In a local ring, the quotient by an ideal whose radical is the maximal ideal is
zero-dimensional. -/
theorem ringKrullDim_quotient_eq_zero_of_radical_eq_maximalIdeal {A : Type u} [CommRing A]
    [IsLocalRing A] {J : Ideal A} (hJ : J.radical = maximalIdeal A) :
    ringKrullDim (A ⧸ J) = 0 := by
  have hJne : J ≠ ⊤ := by
    intro h
    rw [h, Ideal.radical_top] at hJ
    exact (maximalIdeal.isMaximal A).ne_top hJ.symm
  let _ : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJne
  let _ := krullDimLE_zero_quotient_of_radical_eq_maximalIdeal hJ
  exact le_antisymm (Ring.krullDimLE_iff.mp ‹_›) ringKrullDim_nonneg_of_nontrivial

/-- A quotient of a Noetherian ring by an ideal with zero-dimensional quotient has finite
length. -/
theorem length_quotient_ne_top_of_krullDimLE_zero (A : Type u) [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) [Ring.KrullDimLE 0 (A ⧸ J)] : Module.length A (A ⧸ J) ≠ ⊤ := by
  rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
  have hart : IsArtinianRing (A ⧸ J) := isArtinianRing_iff_krullDimLE_zero.mpr ‹_›
  exact ⟨isNoetherian_quotient J, isArtinian_of_surjective_algebraMap
    (Ideal.Quotient.mk_surjective (I := J))⟩


namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

noncomputable section

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)} {M : Model R K C toK}

/-! ### Flatness of the stalks of a model over the base ring -/

/-- The structure map from the base ring to the stalk of the total space of a model at a point:
pull back a global section along the structure morphism and take its germ. -/
def baseStalkHom (x : M.total) : R →+* M.total.presheaf.stalk x :=
  ((M.total.presheaf.germ ⊤ x trivial).hom.comp M.toBase.appTop.hom).comp
    (Scheme.ΓSpecIso (.of R)).inv.hom

@[simp]
theorem baseStalkHom_apply (x : M.total) (r : R) :
    baseStalkHom x r = baseElementGerm x r := rfl

/-- The structure map from the base ring to a stalk of the total space of a model is flat: it is
the composition of the (flat) localisation `R = Γ(Spec R, ⊤) → 𝒪_{Spec R, f x}` with the stalk map
of the flat morphism `M.toBase`. -/
theorem baseStalkHom_flat (x : M.total) : (baseStalkHom x).Flat := by
  let xtop : (⊤ : (Spec (.of R)).Opens) := ⟨M.toBase x, trivial⟩
  let _ := (Spec (.of R)).presheaf.algebra_section_stalk xtop
  have hlocB : IsLocalization.AtPrime ((Spec (.of R)).presheaf.stalk xtop)
      ((isAffineOpen_top (Spec (.of R))).primeIdealOf xtop).asIdeal :=
    (isAffineOpen_top (Spec (.of R))).isLocalization_stalk xtop
  let _ : Module.Flat Γ(Spec (.of R), ⊤) ((Spec (.of R)).presheaf.stalk xtop) :=
    IsLocalization.flat _ ((isAffineOpen_top (Spec (.of R))).primeIdealOf
      xtop).asIdeal.primeCompl
  have hflatB : ((algebraMap Γ(Spec (.of R), ⊤)
      ((Spec (.of R)).presheaf.stalk xtop))).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  have hflatB' : (((Spec (.of R)).presheaf.germ ⊤ (M.toBase x) trivial).hom).Flat := hflatB
  have hflatS : ((M.toBase.stalkMap x).hom).Flat := AlgebraicGeometry.Flat.stalkMap M.toBase x
  have hflatI : (((Scheme.ΓSpecIso (.of R)).inv).hom).Flat :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  have key : baseStalkHom x = ((M.toBase.stalkMap x).hom.comp
      ((Spec (.of R)).presheaf.germ ⊤ (M.toBase x) trivial).hom).comp
      ((Scheme.ΓSpecIso (.of R)).inv).hom := by
    ext r
    exact (M.toBase.germ_stalkMap_apply ⊤ x trivial ((Scheme.ΓSpecIso (.of R)).inv r)).symm
  rw [key]
  exact (hflatI.comp hflatB').comp hflatS

/-- The germ at `x` of a nonzero element of the base ring is a nonzerodivisor on the stalk of the
total space at `x`: the total space is flat over the base. -/
theorem isSMulRegular_baseElementGerm (x : M.total) {r : R} (hr : r ≠ 0) :
    IsSMulRegular (M.total.presheaf.stalk x) (baseElementGerm x r) := by
  let _ : Algebra R (M.total.presheaf.stalk x) := (baseStalkHom x).toAlgebra
  have hflat : Module.Flat R (M.total.presheaf.stalk x) := baseStalkHom_flat x
  have hreg : IsSMulRegular (M.total.presheaf.stalk x) r :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hr)
  intro a b hab
  refine hreg ?_
  have halg : algebraMap R (M.total.presheaf.stalk x) r = baseElementGerm x r := rfl
  change r • a = r • b
  rw [Algebra.smul_def, Algebra.smul_def, halg]
  have hab' : baseElementGerm x r * a = baseElementGerm x r * b := hab
  exact hab'

/-! ### Krull dimension of the local rings along the special fibre -/

/-- The stalk of the total space of a regular model at any point is an integral domain: it is a
regular local ring. -/
theorem isDomain_stalk (hM : ArithmeticSurface M) (x : M.total) :
    IsDomain (M.total.presheaf.stalk x) :=
  @IsRegularLocalRing.isDomain _ _ (hM.regular x)

/-- The germ, at a point over the closed point of the base, of an element of the maximal ideal of
the base lies in the maximal ideal of the stalk. -/
theorem baseElementGerm_mem_maximalIdeal {x : M.total} (hx : M.toBase x = dvrSpecialPoint R)
    {π : R} (hπ : π ∈ maximalIdeal R) :
    baseElementGerm x π ∈ maximalIdeal (M.total.presheaf.stalk x) :=
  (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (baseElementGerm_not_isUnit hx hπ))

/-- The germ of a nonzero element of the base ring is a nonzerodivisor of the stalk. -/
theorem baseElementGerm_mem_nonZeroDivisors (x : M.total) {π : R} (hπ0 : π ≠ 0) :
    baseElementGerm x π ∈ nonZeroDivisors (M.total.presheaf.stalk x) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro z hz
  refine isSMulRegular_baseElementGerm x hπ0 ?_
  change baseElementGerm x π * z = baseElementGerm x π * 0
  rw [mul_zero, mul_comm]
  exact hz

/-- **Krull's principal ideal theorem along the special fibre.**  Cutting the stalk of a regular
proper flat model at a point of the special fibre by the germ of a uniformiser of the base drops
the Krull dimension by exactly one. -/
theorem ringKrullDim_quotient_baseElementGerm_succ (hM : ArithmeticSurface M) {x : M.total}
    (hx : M.toBase x = dvrSpecialPoint R) {π : R} (hπ : π ∈ maximalIdeal R) (hπ0 : π ≠ 0) :
    ringKrullDim (M.total.presheaf.stalk x ⧸ Ideal.span {baseElementGerm x π}) + 1 =
      ringKrullDim (M.total.presheaf.stalk x) := by
  let _ := hM.regular x
  exact ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
    (isSMulRegular_baseElementGerm x hπ0) (baseElementGerm_mem_maximalIdeal hx hπ)

/-- The Krull dimension of the stalk of the total space is one more than the Krull dimension of
the local ring of the special fibre, at every point of the special fibre. -/
theorem ringKrullDim_stalk_eq (hM : ArithmeticSurface M) {x : M.total}
    (hx : M.toBase x = dvrSpecialPoint R) {π : R} (hπ : π ∈ maximalIdeal R) (hπ0 : π ≠ 0)
    {n : ℕ} (hfib : ringKrullDim (M.total.presheaf.stalk x ⧸
      Ideal.span {baseElementGerm x π}) = (n : WithBot ℕ∞)) :
    ringKrullDim (M.total.presheaf.stalk x) = ((n + 1 : ℕ) : WithBot ℕ∞) := by
  rw [← ringKrullDim_quotient_baseElementGerm_succ hM hx hπ hπ0, hfib]
  push_cast
  ring

/-- At a point of the special fibre where the fibre is zero-dimensional — for instance the generic
point of a component — the stalk of the total space has Krull dimension one. -/
theorem ringKrullDim_stalk_eq_one (hM : ArithmeticSurface M) {x : M.total}
    (hx : M.toBase x = dvrSpecialPoint R) {π : R} (hπ : π ∈ maximalIdeal R) (hπ0 : π ≠ 0)
    (hfib : ringKrullDim (M.total.presheaf.stalk x ⧸ Ideal.span {baseElementGerm x π}) = 0) :
    ringKrullDim (M.total.presheaf.stalk x) = 1 := by
  have h := ringKrullDim_stalk_eq hM hx hπ hπ0 (n := 0) (by exact_mod_cast hfib)
  rw [h]
  norm_num

/-- At a point of the special fibre where the fibre is one-dimensional — for instance a closed
point of a component of a curve — the stalk of the total space has Krull dimension two. -/
theorem ringKrullDim_stalk_eq_two (hM : ArithmeticSurface M) {x : M.total}
    (hx : M.toBase x = dvrSpecialPoint R) {π : R} (hπ : π ∈ maximalIdeal R) (hπ0 : π ≠ 0)
    (hfib : ringKrullDim (M.total.presheaf.stalk x ⧸ Ideal.span {baseElementGerm x π}) = 1) :
    ringKrullDim (M.total.presheaf.stalk x) = 2 := by
  have h := ringKrullDim_stalk_eq hM hx hπ hπ0 (n := 1) (by exact_mod_cast hfib)
  rw [h]
  norm_num

/-- **The local ring of the total space at the generic point of a component of the special fibre
is a discrete valuation ring**, as soon as the special fibre is zero-dimensional there. -/
theorem isDiscreteValuationRing_stalk (hM : ArithmeticSurface M) {x : M.total}
    (hx : M.toBase x = dvrSpecialPoint R) {π : R} (hπ : π ∈ maximalIdeal R) (hπ0 : π ≠ 0)
    (hfib : ringKrullDim (M.total.presheaf.stalk x ⧸ Ideal.span {baseElementGerm x π}) = 0) :
    @IsDiscreteValuationRing (M.total.presheaf.stalk x) _
      (@IsRegularLocalRing.isDomain _ _ (hM.regular x)) := by
  let _ := hM.regular x
  exact IsRegularLocalRing.isDiscreteValuationRing_of_ringKrullDim_eq_one _
    (ringKrullDim_stalk_eq_one hM hx hπ hπ0 hfib)

/-- The stalk of the total space at the generic point of a component of the special fibre has
Krull dimension at most one, so the theory of orders of vanishing applies to it. -/
theorem krullDimLE_one_stalk (hM : ArithmeticSurface M) {x : M.total}
    (hx : M.toBase x = dvrSpecialPoint R) {π : R} (hπ : π ∈ maximalIdeal R) (hπ0 : π ≠ 0)
    (hfib : ringKrullDim (M.total.presheaf.stalk x ⧸ Ideal.span {baseElementGerm x π}) = 0) :
    Ring.KrullDimLE 1 (M.total.presheaf.stalk x) :=
  Ring.krullDimLE_iff.mpr (le_of_eq (ringKrullDim_stalk_eq_one hM hx hπ hπ0 hfib))


/-! ### The special fibre is exactly the fibre over the closed point -/

/-- The closed point of the base is in the image of the residue-field point. -/
theorem mem_range_specialPointMap : dvrSpecialPoint R ∈ Set.range (specialPointMap R) := by
  let z : Spec (.of (specialResidueField R)) := (⊥ : PrimeSpectrum (specialResidueField R))
  refine ⟨z, ?_⟩
  have h := congrArg (fun g : Spec (.of (specialResidueField R)) ⟶ Spec (.of R) => g z)
    (specialResidueSpecIso_hom_fromSpecResidueField R)
  have hmem : (Spec (.of R)).fromSpecResidueField (dvrSpecialPoint R)
      ((specialResidueSpecIso R).hom z) ∈
      Set.range ((Spec (.of R)).fromSpecResidueField (dvrSpecialPoint R)) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecResidueField, Set.mem_singleton_iff] at hmem
  rw [← h]
  exact hmem

/-- **A point of the total space lies on the special fibre exactly when it lies over the closed
point of the base.**  One inclusion is `toBase_specialFiberι`; the other is surjectivity of the
underlying map of a pullback of schemes onto the set-theoretic fibre product. -/
theorem range_specialFiberι :
    Set.range (specialFiberι R M.toBase) = {x : M.total | M.toBase x = dvrSpecialPoint R} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨y, rfl⟩
    exact toBase_specialFiberι y
  · intro x hx
    have hr : M.toBase x ∈ Set.range (specialPointMap R) := by
      rw [show M.toBase x = dvrSpecialPoint R from hx]
      exact mem_range_specialPointMap
    have hx' : x ∈ M.toBase ⁻¹' Set.range (specialPointMap R) := hr
    rw [← Scheme.Pullback.range_fst] at hx'
    exact hx'

/-- A point of the special fibre whose closure contains the generic point of a component *is* that
generic point: a component is a maximal irreducible closed subset of the special fibre, and generic
points of irreducible closed subsets are unique. -/
theorem eq_genericPoint_of_mem_closure (i : ArithmeticSurface.Component M) {y : M.total}
    (hy : M.toBase y = dvrSpecialPoint R) (hspec : genericPoint i ∈ closure {y}) :
    y = genericPoint i := by
  obtain ⟨y', rfl⟩ : y ∈ Set.range (specialFiberι R M.toBase) := by
    rw [range_specialFiberι]; exact hy
  have hclosed := Scheme.Hom.isClosedEmbedding (specialFiberι R M.toBase)
  have himg : closure {specialFiberι R M.toBase y'} =
      specialFiberι R M.toBase '' closure {y'} := by
    rw [← Set.image_singleton, hclosed.closure_image_eq]
  rw [himg] at hspec
  have hmem : specialFiberGenericPoint i ∈ closure {y'} := by
    obtain ⟨z, hz, hzeq⟩ := hspec
    have hzz : z = specialFiberGenericPoint i := hclosed.injective hzeq
    exact hzz ▸ hz
  have hsub : (i : Set M.specialFiberScheme) ⊆ closure {y'} := by
    rw [← isGenericPoint_specialFiberGenericPoint i]
    exact (isClosed_closure).closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hmem)
  have hy'gen : IsGenericPoint y' (i : Set M.specialFiberScheme) :=
    le_antisymm (i.2.le_of_ge isIrreducible_singleton.closure hsub) hsub
  exact congrArg (specialFiberι R M.toBase)
    (hy'gen.eq (isGenericPoint_specialFiberGenericPoint i))


/-- A point of `Spec 𝒪_{X,x}` lands in the basic open set of a global section exactly when the germ
of that section at `x` avoids the corresponding prime. -/
theorem mem_basicOpen_fromSpecStalk {X : Scheme.{u}} (x : X) (s : Γ(X, ⊤))
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    X.fromSpecStalk x p ∈ X.basicOpen s ↔ X.presheaf.germ ⊤ x trivial s ∉ p.asIdeal := by
  have h1 : X.fromSpecStalk x ⁻¹ᵁ X.basicOpen s =
      (Spec (X.presheaf.stalk x)).basicOpen ((X.fromSpecStalk x).appTop s) :=
    Scheme.preimage_basicOpen_top _ s
  have h3 : (Spec (X.presheaf.stalk x)).basicOpen ((X.fromSpecStalk x).appTop s) =
      PrimeSpectrum.basicOpen (X.presheaf.germ ⊤ x trivial s) := by
    rw [Scheme.fromSpecStalk_appTop, CommRingCat.comp_apply, CommRingCat.comp_apply,
      Scheme.basicOpen_res, basicOpen_eq_of_affine', Iso.inv_hom_id_apply]
    exact top_inf_eq _
  constructor
  · intro hmem
    have hmem' : p ∈ X.fromSpecStalk x ⁻¹ᵁ X.basicOpen s := hmem
    rw [h1, h3] at hmem'
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hmem'
  · intro hnot
    have hmem' : p ∈ PrimeSpectrum.basicOpen (X.presheaf.germ ⊤ x trivial s) :=
      (PrimeSpectrum.mem_basicOpen _ _).mpr hnot
    rw [← h3, ← h1] at hmem'
    exact hmem'

/-- **The germ of a uniformiser cuts out only the generic point of a component**: in the local ring
of the total space at the generic point of a component of the special fibre, the ideal generated by
the germ of a uniformiser of the base has radical the maximal ideal.  This is unconditional: a
prime of the stalk containing the germ corresponds to a point specialising to the generic point at
which the uniformiser vanishes, hence to a point of the special fibre whose closure contains the
component; maximality of the component then forces that point to be the generic point itself. -/
theorem radical_span_baseElementGerm_genericPoint (i : ArithmeticSurface.Component M) {π : R}
    (hπ : maximalIdeal R = Ideal.span {π}) :
    (Ideal.span {baseElementGerm (genericPoint i) π}).radical =
      maximalIdeal (M.total.presheaf.stalk (genericPoint i)) := by
  have hπmem : π ∈ maximalIdeal R := by
    rw [hπ]
    exact Ideal.mem_span_singleton_self π
  have hzl : PrimeSpectrum.zeroLocus
      ((Ideal.span {baseElementGerm (genericPoint i) π} :
        Ideal (M.total.presheaf.stalk (genericPoint i))) : Set _) =
      {IsLocalRing.closedPoint (M.total.presheaf.stalk (genericPoint i))} := by
    refine Set.Subset.antisymm (fun p hp => ?_) (fun q hq => ?_)
    · have hmem : baseElementGerm (genericPoint i) π ∈ p.asIdeal :=
        (PrimeSpectrum.mem_zeroLocus _ _).mp hp (Ideal.mem_span_singleton_self _)
      have hspec : M.total.fromSpecStalk (genericPoint i) p ⤳ genericPoint i := by
        have hr : M.total.fromSpecStalk (genericPoint i) p ∈
            Set.range (M.total.fromSpecStalk (genericPoint i)) := ⟨p, rfl⟩
        rwa [Scheme.range_fromSpecStalk] at hr
      have hnb : M.total.fromSpecStalk (genericPoint i) p ∉
          M.total.basicOpen (M.toBase.appTop ((Scheme.ΓSpecIso (.of R)).inv π)) := by
        rw [mem_basicOpen_fromSpecStalk]
        exact fun hc => hc hmem
      have hbase : M.toBase (M.total.fromSpecStalk (genericPoint i) p) = dvrSpecialPoint R := by
        have hnot : M.toBase (M.total.fromSpecStalk (genericPoint i) p) ∉
            PrimeSpectrum.basicOpen π := by
          intro hc
          refine hnb ?_
          rw [← Scheme.preimage_basicOpen_top]
          have hbasic : (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv π) =
              PrimeSpectrum.basicOpen π := by
            rw [basicOpen_eq_of_affine', Iso.inv_hom_id_apply]
          have hmem2 : M.toBase (M.total.fromSpecStalk (genericPoint i) p) ∈
              (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv π) := by
            rw [hbasic]; exact hc
          exact hmem2
        have hin : π ∈ (M.toBase (M.total.fromSpecStalk (genericPoint i) p)).asIdeal := by
          by_contra hc
          exact hnot ((PrimeSpectrum.mem_basicOpen _ _).mpr hc)
        have hle : maximalIdeal R ≤
            (M.toBase (M.total.fromSpecStalk (genericPoint i) p)).asIdeal := by
          rw [hπ, Ideal.span_le, Set.singleton_subset_iff]
          exact hin
        exact PrimeSpectrum.ext ((maximalIdeal.isMaximal R).eq_of_le
          (M.toBase (M.total.fromSpecStalk (genericPoint i) p)).isPrime.ne_top hle).symm
      have hy : M.total.fromSpecStalk (genericPoint i) p = genericPoint i :=
        eq_genericPoint_of_mem_closure i hbase (specializes_iff_mem_closure.mp hspec)
      refine Set.mem_singleton_iff.mpr ((Scheme.Hom.isEmbedding
        (M.total.fromSpecStalk (genericPoint i))).injective ?_)
      rw [Scheme.fromSpecStalk_closedPoint]
      exact hy
    · rw [Set.mem_singleton_iff] at hq
      subst hq
      refine (PrimeSpectrum.mem_zeroLocus _ _).mpr (SetLike.coe_subset_coe.mpr
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ?_)))
      exact baseElementGerm_mem_maximalIdeal (toBase_genericPoint i) hπmem
  rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hzl,
    PrimeSpectrum.vanishingIdeal_singleton]
  rfl


/-! ### Discharging the hypotheses of `ComponentIntersection.lean` -/

/-- Two distinct components of the special fibre are incomparable, so the generic point of one
never lies on the other.  In particular the intersection locus of two distinct components is a
proper closed subset of each of them.  This is unconditional. -/
theorem genericPoint_notMem_componentCloseds {i j : ArithmeticSurface.Component M} (hij : i ≠ j) :
    genericPoint i ∉ (componentCloseds j : Set M.total) := by
  intro hmem
  have hclosure : (componentCloseds i : Set M.total) ⊆ (componentCloseds j : Set M.total) := by
    rw [← isGenericPoint_genericPoint i]
    exact (componentCloseds j).isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hmem)
  have himg : specialFiberι R M.toBase '' (i : Set M.specialFiberScheme) ⊆
      specialFiberι R M.toBase '' (j : Set M.specialFiberScheme) := hclosure
  have hsub : (i : Set M.specialFiberScheme) ⊆ (j : Set M.specialFiberScheme) :=
    (Set.image_subset_image_iff
      (Scheme.Hom.isClosedEmbedding (specialFiberι R M.toBase)).injective).mp himg
  exact hij (Subtype.ext (le_antisymm hsub (i.2.le_of_ge j.2.prop hsub)))


/-- **The multiplicity of a component of the special fibre is a genuine natural number.**  The
local ring of the total space at the generic point of the component is a discrete valuation ring
(as soon as the special fibre is zero-dimensional there), so the order of vanishing of a nonzero
element of the base ring is finite. -/
theorem componentMultiplicity_ne_top (hM : ArithmeticSurface M)
    (i : ArithmeticSurface.Component M) {π : R} (hπ : π ∈ maximalIdeal R) (hπ0 : π ≠ 0)
    (hfib : ringKrullDim (M.total.presheaf.stalk (genericPoint i) ⧸
      Ideal.span {baseElementGerm (genericPoint i) π}) = 0) :
    componentMultiplicity i π ≠ ⊤ := by
  let _ := hM.regular (genericPoint i)
  let _ := krullDimLE_one_stalk hM (toBase_genericPoint i) hπ hπ0 hfib
  exact Ring.ord_ne_top (baseElementGerm_mem_nonZeroDivisors _ hπ0)

/-- **The local ring of the total space at a point of the special fibre where the fibre is
set-theoretically just that point is a discrete valuation ring.**  This is the form of
`isDiscreteValuationRing_stalk` in which the hypothesis is the (set-theoretic) statement that the
germ of the uniformiser cuts out only the point itself, which is exactly the situation at the
generic point of a component of the special fibre. -/
theorem isDiscreteValuationRing_stalk_of_radical_eq (hM : ArithmeticSurface M) {x : M.total}
    (hx : M.toBase x = dvrSpecialPoint R) {π : R} (hπ : π ∈ maximalIdeal R) (hπ0 : π ≠ 0)
    (hrad : (Ideal.span {baseElementGerm x π}).radical =
      maximalIdeal (M.total.presheaf.stalk x)) :
    @IsDiscreteValuationRing (M.total.presheaf.stalk x) _
      (@IsRegularLocalRing.isDomain _ _ (hM.regular x)) :=
  isDiscreteValuationRing_stalk hM hx hπ hπ0
    (ringKrullDim_quotient_eq_zero_of_radical_eq_maximalIdeal hrad)

/-- The multiplicity of a component is a natural number, in the set-theoretic form of the
hypothesis: the germ of the uniformiser cuts out only the generic point of the component in the
local ring there. -/
theorem componentMultiplicity_ne_top_of_radical_eq (hM : ArithmeticSurface M)
    (i : ArithmeticSurface.Component M) {π : R} (hπ : π ∈ maximalIdeal R) (hπ0 : π ≠ 0)
    (hrad : (Ideal.span {baseElementGerm (genericPoint i) π}).radical =
      maximalIdeal (M.total.presheaf.stalk (genericPoint i))) :
    componentMultiplicity i π ≠ ⊤ :=
  componentMultiplicity_ne_top hM i hπ hπ0
    (ringKrullDim_quotient_eq_zero_of_radical_eq_maximalIdeal hrad)


/-- The multiplicity with which a component occurs in the special fibre, as a natural number. -/
def componentMultiplicityNat (i : ArithmeticSurface.Component M) (π : R) : ℕ :=
  (componentMultiplicity i π).toNat

/-- Under the zero-dimensionality hypothesis on the special fibre at the generic point of the
component, the natural-number multiplicity really is the `ℕ∞`-valued one. -/
theorem coe_componentMultiplicityNat (hM : ArithmeticSurface M)
    (i : ArithmeticSurface.Component M) {π : R} (hπ : π ∈ maximalIdeal R) (hπ0 : π ≠ 0)
    (hfib : ringKrullDim (M.total.presheaf.stalk (genericPoint i) ⧸
      Ideal.span {baseElementGerm (genericPoint i) π}) = 0) :
    (componentMultiplicityNat i π : ℕ∞) = componentMultiplicity i π :=
  ENat.natCast_toNat (componentMultiplicity_ne_top hM i hπ hπ0 hfib)

/-- The natural-number multiplicity of a component is positive. -/
theorem componentMultiplicityNat_pos (hM : ArithmeticSurface M)
    (i : ArithmeticSurface.Component M) {π : R} (hπ : π ∈ maximalIdeal R) (hπ0 : π ≠ 0)
    (hfib : ringKrullDim (M.total.presheaf.stalk (genericPoint i) ⧸
      Ideal.span {baseElementGerm (genericPoint i) π}) = 0) :
    0 < componentMultiplicityNat i π := by
  have h1 := componentMultiplicity_pos i hπ
  rw [← coe_componentMultiplicityNat hM i hπ hπ0 hfib] at h1
  exact_mod_cast h1

/-- **Finiteness of the intersection number of two components**, from finiteness of the
intersection locus together with zero-dimensionality of the local intersection algebras.  This
replaces the radical hypothesis of `componentIntersection_ne_top` by the geometric statement that
the scheme-theoretic intersection is zero-dimensional at each of its points. -/
theorem componentIntersection_ne_top_of_krullDimLE_zero (hM : ArithmeticSurface M)
    (i j : ArithmeticSurface.Component M)
    (hfin : ((componentCloseds i : Set M.total) ∩ componentCloseds j).Finite)
    (hdim : ∀ x ∈ (componentCloseds i : Set M.total) ∩ componentCloseds j,
      Ring.KrullDimLE 0 (M.total.presheaf.stalk x ⧸
        (stalkIdeal (vanishingIdeal i) x ⊔ stalkIdeal (vanishingIdeal j) x))) :
    componentIntersection i j ≠ ⊤ := by
  have hsupp : Function.support
      (fun x ↦ idealSheafIntersectionMultiplicity (vanishingIdeal i) (vanishingIdeal j) x) ⊆
      (componentCloseds i : Set M.total) ∩ componentCloseds j := by
    intro x hx
    by_contra hxmem
    rw [Set.mem_inter_iff, not_and_or] at hxmem
    apply hx
    apply idealSheafIntersectionMultiplicity_eq_zero_of_not_mem_support
    rcases hxmem with hxi | hxj
    · exact Or.inl (mt (mem_support_vanishingIdeal_iff i x).mp hxi)
    · exact Or.inr (mt (mem_support_vanishingIdeal_iff j x).mp hxj)
  rw [componentIntersection, finsum_eq_sum_of_support_subset_of_finite _ hsupp hfin,
    Ne, ENat.sum_eq_top]
  rintro ⟨x, hx, htop⟩
  have hxmem : x ∈ (componentCloseds i : Set M.total) ∩ componentCloseds j := by
    rwa [Set.Finite.mem_toFinset] at hx
  let _ := hM.regular x
  let _ := hdim x hxmem
  exact length_quotient_ne_top_of_krullDimLE_zero (M.total.presheaf.stalk x)
    (stalkIdeal (vanishingIdeal i) x ⊔ stalkIdeal (vanishingIdeal j) x) htop

/-- Finiteness of the intersection number of two components, in the form closest to
`componentIntersection_ne_top`: the intersection locus is finite and at each of its points the sum
of the two stalk ideals has maximal radical.  The Noetherian hypothesis of
`componentIntersection_ne_top` is now supplied by regularity of the total space. -/
theorem componentIntersection_ne_top_of_radical_eq (hM : ArithmeticSurface M)
    (i j : ArithmeticSurface.Component M)
    (hfin : ((componentCloseds i : Set M.total) ∩ componentCloseds j).Finite)
    (hrad : ∀ x ∈ (componentCloseds i : Set M.total) ∩ componentCloseds j,
      (stalkIdeal (vanishingIdeal i) x ⊔ stalkIdeal (vanishingIdeal j) x).radical =
        maximalIdeal (M.total.presheaf.stalk x)) :
    componentIntersection i j ≠ ⊤ :=
  componentIntersection_ne_top_of_krullDimLE_zero hM i j hfin fun x hx =>
    krullDimLE_zero_quotient_of_radical_eq_maximalIdeal (hrad x hx)


/-- A generator of the maximal ideal of a discrete valuation ring is nonzero. -/
theorem uniformiser_ne_zero {π : R} (hπ : maximalIdeal R = Ideal.span {π}) : π ≠ 0 := fun h =>
  IsDiscreteValuationRing.not_a_field R (hπ.trans (Ideal.span_singleton_eq_bot.mpr h))

/-- **The local ring of the total space of a regular proper model at the generic point of a
component of the special fibre has Krull dimension one.**  Unconditional. -/
theorem ringKrullDim_stalk_genericPoint (hM : ArithmeticSurface M)
    (i : ArithmeticSurface.Component M) {π : R} (hπ : maximalIdeal R = Ideal.span {π}) :
    ringKrullDim (M.total.presheaf.stalk (genericPoint i)) = 1 :=
  ringKrullDim_stalk_eq_one hM (toBase_genericPoint i)
    (hπ ▸ Ideal.mem_span_singleton_self π) (uniformiser_ne_zero hπ)
    (ringKrullDim_quotient_eq_zero_of_radical_eq_maximalIdeal
      (radical_span_baseElementGerm_genericPoint i hπ))

/-- **The local ring of the total space of a regular proper model at the generic point of a
component of the special fibre is a discrete valuation ring.**  Unconditional. -/
theorem isDiscreteValuationRing_stalk_genericPoint (hM : ArithmeticSurface M)
    (i : ArithmeticSurface.Component M) {π : R} (hπ : maximalIdeal R = Ideal.span {π}) :
    @IsDiscreteValuationRing (M.total.presheaf.stalk (genericPoint i)) _
      (@IsRegularLocalRing.isDomain _ _ (hM.regular (genericPoint i))) :=
  isDiscreteValuationRing_stalk hM (toBase_genericPoint i)
    (hπ ▸ Ideal.mem_span_singleton_self π) (uniformiser_ne_zero hπ)
    (ringKrullDim_quotient_eq_zero_of_radical_eq_maximalIdeal
      (radical_span_baseElementGerm_genericPoint i hπ))

/-- **The multiplicity of a component of the special fibre is a genuine natural number.**
Unconditional, for `π` a uniformiser of the base. -/
theorem componentMultiplicity_ne_top_of_span_eq (hM : ArithmeticSurface M)
    (i : ArithmeticSurface.Component M) {π : R} (hπ : maximalIdeal R = Ideal.span {π}) :
    componentMultiplicity i π ≠ ⊤ :=
  componentMultiplicity_ne_top hM i (hπ ▸ Ideal.mem_span_singleton_self π)
    (uniformiser_ne_zero hπ) (ringKrullDim_quotient_eq_zero_of_radical_eq_maximalIdeal
      (radical_span_baseElementGerm_genericPoint i hπ))

/-- The natural-number multiplicity of a component agrees with the `ℕ∞`-valued one, for `π` a
uniformiser of the base.  Unconditional. -/
theorem coe_componentMultiplicityNat_of_span_eq (hM : ArithmeticSurface M)
    (i : ArithmeticSurface.Component M) {π : R} (hπ : maximalIdeal R = Ideal.span {π}) :
    (componentMultiplicityNat i π : ℕ∞) = componentMultiplicity i π :=
  ENat.natCast_toNat (componentMultiplicity_ne_top_of_span_eq hM i hπ)

/-- The natural-number multiplicity of a component is positive, for `π` a uniformiser of the base.
Unconditional. -/
theorem componentMultiplicityNat_pos_of_span_eq (hM : ArithmeticSurface M)
    (i : ArithmeticSurface.Component M) {π : R} (hπ : maximalIdeal R = Ideal.span {π}) :
    0 < componentMultiplicityNat i π := by
  have h1 := componentMultiplicity_pos i (hπ ▸ Ideal.mem_span_singleton_self π)
  rw [← coe_componentMultiplicityNat_of_span_eq hM i hπ] at h1
  exact_mod_cast h1


/-- The intersection number of two components of the special fibre, as a natural number. -/
def componentIntersectionNat (i j : ArithmeticSurface.Component M) : ℕ :=
  (componentIntersection i j).toNat

/-- The natural-number intersection number of two components is symmetric. -/
theorem componentIntersectionNat_comm (i j : ArithmeticSurface.Component M) :
    componentIntersectionNat i j = componentIntersectionNat j i :=
  congrArg ENat.toNat (componentIntersection_comm i j)

/-- Under the finiteness and zero-dimensionality hypotheses on the intersection locus, the
natural-number intersection number really is the `ℕ∞`-valued one. -/
theorem coe_componentIntersectionNat (hM : ArithmeticSurface M)
    (i j : ArithmeticSurface.Component M)
    (hfin : ((componentCloseds i : Set M.total) ∩ componentCloseds j).Finite)
    (hdim : ∀ x ∈ (componentCloseds i : Set M.total) ∩ componentCloseds j,
      Ring.KrullDimLE 0 (M.total.presheaf.stalk x ⧸
        (stalkIdeal (vanishingIdeal i) x ⊔ stalkIdeal (vanishingIdeal j) x))) :
    (componentIntersectionNat i j : ℕ∞) = componentIntersection i j :=
  ENat.natCast_toNat (componentIntersection_ne_top_of_krullDimLE_zero hM i j hfin hdim)

/-- Two components with disjoint carriers have zero natural-number intersection number. -/
theorem componentIntersectionNat_eq_zero_of_disjoint (i j : ArithmeticSurface.Component M)
    (h : (componentCloseds i : Set M.total) ∩ componentCloseds j = ∅) :
    componentIntersectionNat i j = 0 := by
  rw [componentIntersectionNat, componentIntersection_eq_zero_of_disjoint i j h]
  rfl


end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction
