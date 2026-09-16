/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode

/-!
# Dimension and embedding dimension of the local node

This file proves the quantitative form of the local-node regularity calculation.  At the
total-space origin over a DVR, the ambient polynomial local ring has dimension three and the
hypersurface local ring has dimension two.  At thickness at least two, its maximal ideal has
embedding dimension three, so three generators are necessary.
-/

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode

universe u

noncomputable section

/-- The ambient total-origin maximal ideal `(x,y,π)` has height three.  The lower bound is
witnessed by the explicit chain obtained by successively killing `π`, `x`, and `y`; the upper
bound is the dimension of the two-variable polynomial ring over a DVR. -/
theorem totalOriginIdeal_height_eq_three
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) :
    (totalOriginIdeal R π).height = 3 := by
  let mR : Ideal R := Ideal.span {π}
  let : mR.IsMaximal := by
    change (Ideal.span {π}).IsMaximal
    rw [← hπ.maximalIdeal_eq]
    exact IsLocalRing.maximalIdeal.isMaximal R
  let k := R ⧸ mR
  let : Field k := Ideal.Quotient.field mR
  let red : R →+* k := Ideal.Quotient.mk mR
  let f1 : MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 2) k :=
    MvPolynomial.map red
  let g : MvPolynomial (Fin 2) k →+* Polynomial k :=
    MvPolynomial.eval₂Hom Polynomial.C ![0, Polynomial.X]
  let f2 : MvPolynomial (Fin 2) R →+* Polynomial k := g.comp f1
  let p1 := RingHom.ker f1
  let p2 := RingHom.ker f2
  let : p1.IsPrime := RingHom.ker_isPrime f1
  let : p2.IsPrime := RingHom.ker_isPrime f2
  let : (totalOriginIdeal R π).IsPrime :=
    (totalOriginIdeal_isMaximal_of_irreducible R π hπ).isPrime
  have hp1p2 : p1 ≤ p2 := by
    intro z hz
    change f2 z = 0
    change f1 z = 0 at hz
    change (g.comp f1) z = 0
    rw [RingHom.comp_apply, hz, map_zero]
  have hcomp : (Polynomial.evalRingHom (0 : k)).comp f2 =
      red.comp (totalOriginEvaluation R).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [f2, g, f1, red, totalOriginEvaluation]
    · intro i
      fin_cases i <;> simp [f2, g, f1, red, totalOriginEvaluation]
  have hp2m : p2 ≤ totalOriginIdeal R π := by
    intro z hz
    rw [totalOriginIdeal_eq_comap_originEvaluation]
    change totalOriginEvaluation R z ∈ mR
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change red (totalOriginEvaluation R z) = 0
    change f2 z = 0 at hz
    have h : ((Polynomial.evalRingHom (0 : k)).comp f2) z = 0 := by simp [hz]
    rw [hcomp] at h
    exact h
  have hp1_ne_bot : p1 ≠ ⊥ := by
    intro hp1
    have hc : MvPolynomial.C π ∈ p1 := by
      change f1 (MvPolynomial.C π) = 0
      change MvPolynomial.map red (MvPolynomial.C π) = 0
      have hred : red π = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span (Set.mem_singleton _)
      rw [MvPolynomial.map_C, hred, map_zero]
    rw [hp1, Submodule.mem_bot] at hc
    exact hπ.ne_zero (MvPolynomial.C_injective (Fin 2) R (by simpa using hc))
  have hp1_lt_p2 : p1 < p2 := by
    refine lt_of_le_of_ne hp1p2 ?_
    intro heq
    have hx : MvPolynomial.X 0 ∈ p2 := by
      change f2 (MvPolynomial.X 0) = 0
      simp [f2, g, f1]
    have hx' : MvPolynomial.X 0 ∈ p1 := heq ▸ hx
    change f1 (MvPolynomial.X 0) = 0 at hx'
    simp [f1] at hx'
  have hp2_lt_m : p2 < totalOriginIdeal R π := by
    refine lt_of_le_of_ne hp2m ?_
    intro heq
    have hy : MvPolynomial.X 1 ∈ totalOriginIdeal R π := by
      rw [totalOriginIdeal]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    have hy' : MvPolynomial.X 1 ∈ p2 := heq ▸ hy
    change f2 (MvPolynomial.X 1) = 0 at hy'
    simp [f2, g, f1] at hy'
  have h01 : (⊥ : Ideal (MvPolynomial (Fin 2) R)).height + 1 ≤ p1.height :=
    Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hp1_ne_bot)
  have h12 : p1.height + 1 ≤ p2.height :=
    Ideal.height_add_one_le_of_lt_of_isPrime hp1_lt_p2
  have h23 : p2.height + 1 ≤ (totalOriginIdeal R π).height :=
    Ideal.height_add_one_le_of_lt_of_isPrime hp2_lt_m
  have hlower : (3 : ℕ∞) ≤ (totalOriginIdeal R π).height := by
    rw [Ideal.height_bot] at h01
    have h01' : (1 : ℕ∞) ≤ p1.height := by simpa using h01
    calc
      (3 : ℕ∞) = 1 + 1 + 1 := by norm_num
      _ ≤ p1.height + 1 + 1 := by gcongr
      _ ≤ p2.height + 1 := by gcongr
      _ ≤ (totalOriginIdeal R π).height := h23
  have hupperW : ((totalOriginIdeal R π).height : WithBot ℕ∞) ≤
      (3 : WithBot ℕ∞) := by
    calc
      ((totalOriginIdeal R π).height : WithBot ℕ∞) ≤
          ringKrullDim (MvPolynomial (Fin 2) R) :=
        Ideal.height_le_ringKrullDim_of_ne_top
          (totalOriginIdeal_isMaximal_of_irreducible R π hπ).ne_top
      _ = 3 := by
        rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
          IsDiscreteValuationRing.ringKrullDim_eq_one]
        norm_num
  have hupper : (totalOriginIdeal R π).height ≤ (3 : ℕ∞) :=
    WithBot.coe_le_coe.mp hupperW
  exact le_antisymm hupper hlower

/-- The regular ambient local ring at `(x,y,π)` has Krull dimension three. -/
theorem originAmbientRing_ringKrullDim_eq_three
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) :
    ringKrullDim (OriginAmbientRing R π hπ) = 3 := by
  let : (totalOriginIdeal R π).IsPrime :=
    (totalOriginIdeal_isMaximal_of_irreducible R π hπ).isPrime
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (totalOriginIdeal R π),
    totalOriginIdeal_height_eq_three R π hπ]
  norm_num

/-- Every positive-thickness node local ring at the total-space origin has Krull dimension two. -/
theorem originRing_ringKrullDim_eq_two
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n) :
    ringKrullDim (OriginRing R π hπ n) = 2 := by
  have hdrop := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
    (originEquation_isRegular R π hπ n) (originEquation_mem_maximalIdeal R π hπ n hn)
  change ringKrullDim (OriginRing R π hπ n) + 1 =
    ringKrullDim (OriginAmbientRing R π hπ) at hdrop
  rw [originAmbientRing_ringKrullDim_eq_three R π hπ] at hdrop
  have hBne : ringKrullDim (OriginRing R π hπ n) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hdrop
    simp at hdrop
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hBne
  have hdropENat : d + 1 = (3 : ℕ∞) := by
    apply WithBot.coe_injective
    calc
      (↑(d + 1) : WithBot ℕ∞) = (↑d : WithBot ℕ∞) + 1 := by simp
      _ = ringKrullDim (OriginRing R π hπ n) + 1 :=
        congrArg (fun e : WithBot ℕ∞ => e + 1) hd
      _ = 3 := hdrop
  have hdtop : d ≠ ⊤ := by
    intro hdtop
    rw [hdtop] at hdropENat
    simp at hdropENat
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp hdtop
  have hdropNat : e + 1 = 3 := by
    exact_mod_cast he.symm ▸ hdropENat
  have he2 : e = 2 := by omega
  calc
    ringKrullDim (OriginRing R π hπ n) = (d : WithBot ℕ∞) := hd.symm
    _ = (e : WithBot ℕ∞) := congrArg (fun z : ℕ∞ => (z : WithBot ℕ∞)) he.symm
    _ = 2 := by simp [he2]

/-- At thickness at least two, the two-dimensional origin local ring has embedding dimension
three.  Thus all three displayed generators `x,y,π` are necessary. -/
theorem originMaximalIdeal_spanFinrank_eq_three
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (n : ℕ) (hn : 2 ≤ n) :
    (originMaximalIdeal R π hπ n).spanFinrank = 3 := by
  have hnpos : 0 < n := by omega
  let q : OriginAmbientRing R π hπ →+* OriginRing R π hπ n :=
    Ideal.Quotient.mk (Ideal.span {originEquation R π hπ n})
  have hEqLe : Ideal.span {originEquation R π hπ n} ≤
      IsLocalRing.maximalIdeal (OriginAmbientRing R π hπ) :=
    Ideal.span_le.mpr fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact originEquation_mem_maximalIdeal R π hπ n hnpos
  let : Nontrivial (OriginRing R π hπ n) :=
    Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hEqLe
  let : IsLocalRing (OriginRing R π hπ n) :=
    IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  have hmax : originMaximalIdeal R π hπ n =
      IsLocalRing.maximalIdeal (OriginRing R π hπ n) :=
    IsLocalRing.eq_maximalIdeal (R := OriginRing R π hπ n)
      (I := originMaximalIdeal R π hπ n)
      (originMaximalIdeal_isMaximal R π hπ n hnpos)
  have hupper : (originMaximalIdeal R π hπ n).spanFinrank ≤ 3 :=
    originMaximalIdeal_spanFinrank_le_three R π hπ n
  have hdim : ringKrullDim (OriginRing R π hπ n) = 2 :=
    originRing_ringKrullDim_eq_two R π hπ n hnpos
  have hlowerW := ringKrullDim_le_spanFinrank_maximalIdeal (OriginRing R π hπ n)
  rw [hdim] at hlowerW
  have hlower : 2 ≤ (originMaximalIdeal R π hπ n).spanFinrank := by
    rw [hmax]
    exact_mod_cast hlowerW
  have hne : (originMaximalIdeal R π hπ n).spanFinrank ≠ 2 := by
    intro heq
    have hreg : IsRegularLocalRing (OriginRing R π hπ n) := by
      apply (isRegularLocalRing_iff (OriginRing R π hπ n)).mpr
      rw [← hmax, heq, hdim]
      norm_num
    have hn1 := (originRing_isRegularLocalRing_iff R π hπ n hnpos).mp hreg
    omega
  omega

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode
