/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# The affine length formula for the degree of a principal divisor

For `k` a field and `A` a finitely generated `k`-algebra that is an integral domain of Krull
dimension `1`, and `a : A` nonzero, this file proves the affine length formula
(Fulton, *Intersection Theory*, Example 1.2.3 / Appendix A.3):

`∑ᶠ m : MaximalSpectrum A, [κ(m):k] * ord_{A_m}(a) = finrank k (A ⧸ (a))`.

## Main declarations

* `GromovWitten.AlgebraicGeometry.IntersectionTheory.AffineDegreeFormula.affineLengthFormula`:
  the main theorem above.
-/

open CategoryTheory

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory.AffineDegreeFormula

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

/-- The localization of a ring of Krull dimension `≤ 1` at a prime ideal again has Krull
dimension `≤ 1`: the height of a prime ideal never exceeds the Krull dimension of the ambient
ring, and the Krull dimension of a localization at a prime equals the height of that prime. -/
theorem krullDimLE_one_localization [Ring.KrullDimLE 1 A] (m : Ideal A) [m.IsPrime]
    (Am : Type u) [CommRing Am] [Algebra A Am] [IsLocalization.AtPrime Am m] :
    Ring.KrullDimLE 1 Am := by
  rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height m Am]
  exact (Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top ‹m.IsPrime›)).trans
    (Ring.krullDimLE_iff.mp ‹Ring.KrullDimLE 1 A›)

/-- `k`'s own residue field surjects onto `k` (in fact it is `k` itself), so `Module.length`
computed over `k` agrees with `Module.length` computed over `IsLocalRing.ResidueField k`, for
any module that is compatibly a module over both. -/
theorem length_eq_length_residueField_self {N : Type u} [AddCommGroup N]
    [Module k N] [Module (IsLocalRing.ResidueField k) N]
    [IsScalarTower k (IsLocalRing.ResidueField k) N] :
    Module.length k N = Module.length (IsLocalRing.ResidueField k) N :=
  Module.length_eq_of_surjective (R := IsLocalRing.ResidueField k) Ideal.Quotient.mk_surjective

/-- For `m` a maximal ideal of `A` and `Am` a localization of `A` at `m`, the residue field of
`Am` is `k`-linearly isomorphic to `A ⧸ m`. -/
theorem length_residueField_localization_eq (m : Ideal A) [m.IsMaximal]
    {Am : Type u} [CommRing Am] [Algebra A Am] [IsLocalization.AtPrime Am m] [IsLocalRing Am]
    [Algebra k Am] [IsScalarTower k A Am] :
    Module.length k (IsLocalRing.ResidueField Am) = Module.length k (A ⧸ m) := by
  set e := IsLocalization.AtPrime.equivQuotMaximalIdeal m Am
  have hcomm : ∀ x : A,
      e (algebraMap A (A ⧸ m) x) = algebraMap A (IsLocalRing.ResidueField Am) x := by
    intro x
    exact IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk m Am x
  have hcommk : ∀ c : k,
      e (algebraMap k (A ⧸ m) c) = algebraMap k (IsLocalRing.ResidueField Am) c := by
    intro c
    rw [IsScalarTower.algebraMap_apply k A (A ⧸ m), hcomm,
      ← IsScalarTower.algebraMap_apply k A (IsLocalRing.ResidueField Am)]
  let f : (A ⧸ m) ≃ₐ[k] IsLocalRing.ResidueField Am := AlgEquiv.ofRingEquiv (f := e) hcommk
  exact (f.toLinearEquiv.length_eq).symm

/-- The algebra map out of a field is always a local ring homomorphism, as long as the target
is nontrivial: every nonzero element of a field is already a unit, and `0` cannot map to a
unit unless the target is trivial. -/
theorem isLocalHom_algebraMap_of_field {R : Type u} [Semiring R] [Nontrivial R] [Algebra k R] :
    IsLocalHom (algebraMap k R) where
  map_nonunit a ha := by
    rcases eq_or_ne a 0 with rfl | ha0
    · exact absurd ha (by simp)
    · exact isUnit_iff_ne_zero.mpr ha0

/-- `Module.finrank` is the truncation to `ℕ` of `Module.length` for a vector space over a
division ring, with no finiteness hypothesis needed: both sides are `0` when the space is
infinite-dimensional. -/
theorem length_toNat_eq_finrank (K M : Type u) [DivisionRing K] [AddCommGroup M] [Module K M] :
    (Module.length K M).toNat = Module.finrank K M := by
  rw [Module.length_eq_rank, Cardinal.toNat_toENat]; rfl

/-- The affine length formula, local at one maximal ideal `m` of `A`: for `Am` a localization of
`A` at `m`, the `k`-dimension of `Am ⧸ (a)` is the residue degree `[κ(m):k]` times the order of
vanishing of `a` at `m`. -/
theorem local_finrank_formula (m : Ideal A) [m.IsMaximal]
    {Am : Type u} [CommRing Am] [Algebra A Am] [IsLocalization.AtPrime Am m] [IsLocalRing Am]
    [Algebra k Am] [IsScalarTower k A Am] [Module.Finite k (A ⧸ m)] (a : A) :
    Module.finrank k (Am ⧸ Ideal.span {algebraMap A Am a}) =
      Module.finrank k (A ⧸ m) * (Ring.ord Am (algebraMap A Am a)).toNat := by
  have hlh : IsLocalHom (algebraMap k Am) := isLocalHom_algebraMap_of_field
  have hlen := IsLocalRing.length_restrictScalars k Am
    (Am ⧸ Ideal.span {algebraMap A Am a})
  rw [← length_eq_length_residueField_self (k := k), length_residueField_localization_eq m] at hlen
  have hord : Module.length Am (Am ⧸ Ideal.span {algebraMap A Am a}) =
      Ring.ord Am (algebraMap A Am a) := rfl
  rw [hord] at hlen
  have := congrArg ENat.toNat hlen
  rwa [length_toNat_eq_finrank, ENat.toNat_mul, Module.length_eq_finrank k (A ⧸ m),
    mul_comm] at this

/-- For `m` an ideal of `A` containing `a`, the image `m ⧸ (a)` is maximal in `A ⧸ (a)` iff `m`
is maximal in `A`: the third isomorphism theorem identifies the two quotients, and being maximal
is the same as the quotient being a field. -/
theorem isMaximal_map_quotient_iff {a : A} {m : Ideal A} (hle : Ideal.span {a} ≤ m) :
    (m.map (Ideal.Quotient.mk (Ideal.span {a}))).IsMaximal ↔ m.IsMaximal := by
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient,
    Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact (DoubleQuot.quotQuotEquivQuotOfLE hle).toMulEquiv.isField_congr

/-- Maximal ideals of `A ⧸ (a)` correspond exactly to maximal ideals of `A` containing `a`. -/
noncomputable def maxSpecQuotientEquiv (a : A) :
    MaximalSpectrum (A ⧸ Ideal.span {a}) ≃ {m : MaximalSpectrum A // a ∈ m.asIdeal} where
  toFun p :=
    have hle : Ideal.span {a} ≤ p.asIdeal.comap (Ideal.Quotient.mk (Ideal.span {a})) := by
      intro x hx
      change Ideal.Quotient.mk (Ideal.span {a}) x ∈ p.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact p.asIdeal.zero_mem
    ⟨⟨p.asIdeal.comap (Ideal.Quotient.mk (Ideal.span {a})),
        (isMaximal_map_quotient_iff hle).mp (by
          rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]; exact p.isMaximal)⟩,
      hle (Ideal.subset_span rfl)⟩
  invFun m :=
    ⟨m.1.asIdeal.map (Ideal.Quotient.mk (Ideal.span {a})),
      (isMaximal_map_quotient_iff
        (Ideal.span_singleton_le_iff_mem m.1.asIdeal |>.mpr m.2)).mpr m.1.isMaximal⟩
  left_inv p := by
    apply MaximalSpectrum.ext
    exact Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective p.asIdeal
  right_inv m := by
    apply Subtype.ext
    apply MaximalSpectrum.ext
    change (m.1.asIdeal.map (Ideal.Quotient.mk (Ideal.span {a}))).comap
        (Ideal.Quotient.mk (Ideal.span {a})) = m.1.asIdeal
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr (Ideal.span_singleton_le_iff_mem m.1.asIdeal |>.mpr m.2)]

/-- The localisation of `A ⧸ (a)` at the maximal ideal `m ⧸ (a)` agrees, as a `k`-algebra, with
`Am ⧸ (a)` for `Am` a localisation of `A` at `m`: both are localisations of `A ⧸ (a)` at the same
submonoid (the image of `A ∖ m`), so they are canonically isomorphic. -/
theorem localization_quotient_finrank_eq (a : A) (p : Ideal (A ⧸ Ideal.span {a})) [p.IsMaximal]
    (m : Ideal A) [m.IsMaximal] (hle : Ideal.span {a} ≤ m)
    (hpm : p = m.map (Ideal.Quotient.mk (Ideal.span {a})))
    {Am : Type u} [CommRing Am] [Algebra A Am] [IsLocalization.AtPrime Am m]
    [Algebra k Am] [IsScalarTower k A Am] :
    Module.finrank k (Localization.AtPrime p) =
      Module.finrank k (Am ⧸ (Ideal.span {a}).map (algebraMap A Am)) := by
  set π := Ideal.Quotient.mk (Ideal.span {a})
  have hcomap : p.comap π = m := by
    rw [hpm, Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hle]
  have hsub : Algebra.algebraMapSubmonoid (A ⧸ Ideal.span {a}) m.primeCompl = p.primeCompl := by
    have h1 : (p.primeCompl.comap π).map π = p.primeCompl :=
      Submonoid.map_comap_eq_of_surjective Ideal.Quotient.mk_surjective p.primeCompl
    have h2 : p.primeCompl.comap π = m.primeCompl := by
      ext x
      simp only [Submonoid.mem_comap, Ideal.mem_primeCompl_iff, ← Ideal.mem_comap, hcomap]
    change Submonoid.map π m.primeCompl = p.primeCompl
    rw [← h2, h1]
  have hinst : IsLocalization p.primeCompl (Am ⧸ (Ideal.span {a}).map (algebraMap A Am)) :=
    hsub ▸ (inferInstance :
      IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ Ideal.span {a}) m.primeCompl)
        (Am ⧸ (Ideal.span {a}).map (algebraMap A Am)))
  have e := IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
    (Am ⧸ (Ideal.span {a}).map (algebraMap A Am))
  have hcommk : ∀ c : k, e (algebraMap k (Localization.AtPrime p) c) =
      algebraMap k (Am ⧸ (Ideal.span {a}).map (algebraMap A Am)) c := by
    intro c
    rw [IsScalarTower.algebraMap_apply k (A ⧸ Ideal.span {a}) (Localization.AtPrime p),
      e.commutes, IsScalarTower.algebraMap_apply k A (A ⧸ Ideal.span {a})]
    have hstep : algebraMap A Am (algebraMap k A c) = algebraMap k Am c :=
      (IsScalarTower.algebraMap_apply k A Am c).symm
    calc algebraMap (A ⧸ Ideal.span {a}) (Am ⧸ (Ideal.span {a}).map (algebraMap A Am))
            (algebraMap A (A ⧸ Ideal.span {a}) (algebraMap k A c))
        = Ideal.Quotient.mk ((Ideal.span {a}).map (algebraMap A Am))
            (algebraMap A Am (algebraMap k A c)) := rfl
      _ = Ideal.Quotient.mk ((Ideal.span {a}).map (algebraMap A Am)) (algebraMap k Am c) := by
            rw [hstep]
      _ = algebraMap k (Am ⧸ (Ideal.span {a}).map (algebraMap A Am)) c := rfl
  let f : Localization.AtPrime p ≃ₐ[k] Am ⧸ (Ideal.span {a}).map (algebraMap A Am) :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) hcommk
  exact f.toLinearEquiv.finrank_eq

/-- The quotient of a Noetherian ring of Krull dimension `≤ 1` by the ideal generated by a
non-zero-divisor is Artinian: it is Noetherian, and has Krull dimension `0`. -/
theorem isArtinianRing_quotient_span_singleton [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    {x : A} (hx : x ∈ nonZeroDivisors A) : IsArtinianRing (A ⧸ Ideal.span {x}) := by
  rw [isArtinianRing_iff_krullDimLE_zero, Ring.KrullDimLE, Order.krullDimLE_iff,
    ← ENat.WithBot.add_le_add_one_right_iff, Nat.cast_zero, zero_add]
  exact (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hx).trans (Order.KrullDimLE.krullDim_le)

/-- **The affine length formula** (Fulton, *Intersection Theory*, Example 1.2.3 / Appendix A.3):
for `k` a field, `A` a finitely generated `k`-algebra that is an integral domain of Krull
dimension `1`, and `a : A` nonzero, the sum over the maximal ideals `m` of `A` of the residue
degree `[κ(m):k]` times the order of vanishing of `a` at `m` equals the `k`-dimension of
`A ⧸ (a)`. -/
theorem affineLengthFormula [IsDomain A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType k A]
    (a : A) (ha : a ≠ 0) :
    ∑ᶠ m : MaximalSpectrum A, Module.finrank k (A ⧸ m.asIdeal) *
        (Ring.ord (Localization.AtPrime m.asIdeal)
          (algebraMap A (Localization.AtPrime m.asIdeal) a)).toNat =
      Module.finrank k (A ⧸ Ideal.span {a}) := by
  have hIN : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hnzd : a ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_ne_zero ha
  have hArt : IsArtinianRing (A ⧸ Ideal.span {a}) := isArtinianRing_quotient_span_singleton hnzd
  have hFT : Algebra.FiniteType k (A ⧸ Ideal.span {a}) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k (Ideal.span {a}))
      Ideal.Quotient.mk_surjective
  have hFin : Module.Finite k (A ⧸ Ideal.span {a}) :=
    Module.finite_of_isArtinianRing k (A ⧸ Ideal.span {a})
  have hFintype : Fintype (PrimeSpectrum (A ⧸ Ideal.span {a})) := Fintype.ofFinite _
  have hFintypeMax : Fintype (MaximalSpectrum (A ⧸ Ideal.span {a})) := Fintype.ofFinite _
  set F : MaximalSpectrum A → ℕ := fun m => Module.finrank k (A ⧸ m.asIdeal) *
      (Ring.ord (Localization.AtPrime m.asIdeal)
        (algebraMap A (Localization.AtPrime m.asIdeal) a)).toNat with hF
  have hsupp : Function.support F ⊆ {m : MaximalSpectrum A | a ∈ m.asIdeal} := by
    intro m hm
    by_contra hcon
    refine hm ?_
    have hunit : IsUnit (algebraMap A (Localization.AtPrime m.asIdeal) a) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime m.asIdeal) m.asIdeal
        a).mpr hcon
    simp [hF, Ring.ord_of_isUnit hunit]
  have hsub : Fintype {m : MaximalSpectrum A // a ∈ m.asIdeal} :=
    Fintype.ofEquiv _ (maxSpecQuotientEquiv a)
  have hfin : {m : MaximalSpectrum A | a ∈ m.asIdeal}.Finite := by
    have heq : {m : MaximalSpectrum A | a ∈ m.asIdeal} =
        Set.range (Subtype.val : {m : MaximalSpectrum A // a ∈ m.asIdeal} → MaximalSpectrum A) := by
      ext m; simp
    rw [heq]
    exact Set.finite_range _
  rw [finsum_eq_sum_of_support_subset_of_finite F hsupp hfin]
  have hterm : ∀ q : MaximalSpectrum (A ⧸ Ideal.span {a}),
      F ((maxSpecQuotientEquiv a) q).1 = Module.finrank k (Localization.AtPrime q.asIdeal) := by
    intro q
    set m := ((maxSpecQuotientEquiv a) q).1 with hm_def
    have hmem : a ∈ m.asIdeal := ((maxSpecQuotientEquiv a) q).2
    have hle : Ideal.span {a} ≤ m.asIdeal := Ideal.span_singleton_le_iff_mem m.asIdeal |>.mpr hmem
    have hpm : q.asIdeal = m.asIdeal.map (Ideal.Quotient.mk (Ideal.span {a})) :=
      (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q.asIdeal).symm
    have hmmax : m.asIdeal.IsMaximal := m.isMaximal
    let _ : Field (A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
    have hAT : Algebra.FiniteType k (A ⧸ m.asIdeal) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m.asIdeal) Ideal.Quotient.mk_surjective
    have hFinm : Module.Finite k (A ⧸ m.asIdeal) :=
      Module.finite_of_isArtinianRing k (A ⧸ m.asIdeal)
    have hglue := localization_quotient_finrank_eq (k := k) a q.asIdeal m.asIdeal hle hpm
      (Am := Localization.AtPrime m.asIdeal)
    have hlocal := local_finrank_formula (k := k) m.asIdeal
      (Am := Localization.AtPrime m.asIdeal) a
    have hmapspan : (Ideal.span {a}).map (algebraMap A (Localization.AtPrime m.asIdeal)) =
        Ideal.span {algebraMap A (Localization.AtPrime m.asIdeal) a} := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [hF]
    change Module.finrank k (A ⧸ m.asIdeal) *
        (Ring.ord (Localization.AtPrime m.asIdeal)
          (algebraMap A (Localization.AtPrime m.asIdeal) a)).toNat = _
    rw [hglue, hmapspan, hlocal]
  have hbij : ∑ m ∈ hfin.toFinset, F m =
      ∑ q : MaximalSpectrum (A ⧸ Ideal.span {a}),
        Module.finrank k (Localization.AtPrime q.asIdeal) := by
    refine Finset.sum_bij' (fun (m : MaximalSpectrum A) (hm : m ∈ hfin.toFinset) =>
        (maxSpecQuotientEquiv a).symm ⟨m, hfin.mem_toFinset.mp hm⟩)
      (fun (q : MaximalSpectrum (A ⧸ Ideal.span {a})) (_ : q ∈ Finset.univ) =>
        ((maxSpecQuotientEquiv a) q).1)
      (fun _ _ => Finset.mem_univ _)
      (fun q _ => hfin.mem_toFinset.mpr ((maxSpecQuotientEquiv a) q).2)
      (fun m hm => ?_) (fun q _ => ?_) (fun m hm => ?_)
    · simp only [Equiv.apply_symm_apply]
    · simp only [Subtype.coe_eta, Equiv.symm_apply_apply]
    · have := hterm ((maxSpecQuotientEquiv a).symm ⟨m, hfin.mem_toFinset.mp hm⟩)
      simpa only [Equiv.apply_symm_apply] using this
  have hreindex : ∑ p : PrimeSpectrum (A ⧸ Ideal.span {a}),
      Module.finrank k (Localization.AtPrime p.asIdeal) =
      ∑ q : MaximalSpectrum (A ⧸ Ideal.span {a}),
        Module.finrank k (Localization.AtPrime q.asIdeal) :=
    Equiv.sum_comp (IsArtinianRing.primeSpectrumEquivMaximalSpectrum (R := A ⧸ Ideal.span {a}))
      (fun q => Module.finrank k (Localization.AtPrime q.asIdeal))
  rw [hbij, ← hreindex, ← IsArtinianRing.finrank_eq_sum_primeSpectrum (A ⧸ Ideal.span {a}) k]

end GromovWitten.AlgebraicGeometry.IntersectionTheory.AffineDegreeFormula
