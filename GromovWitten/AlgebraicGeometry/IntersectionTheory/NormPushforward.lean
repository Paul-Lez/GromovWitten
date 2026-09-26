/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/

import GromovWitten.Algebra.OrderDeterminant
import GromovWitten.Algebra.OrderBirational
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChernClasses
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ZeroCycleDegree
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleSectionGysinIdentity
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Pushforward of a principal divisor along a finite free morphism of affine curves

Let `A ⊆ B` be Noetherian integral domains of Krull dimension `≤ 1` with `B` finite and free as an
`A`-module and `algebraMap A B` injective, and let `p : Spec B ⟶ Spec A` be the induced morphism
(finite, hence proper). This file proves Fulton's *Intersection Theory*, Proposition 1.4, in this
affine finite free case: for `b : B` nonzero,

`p_* (div b) = div (Algebra.norm A b)`

as algebraic cycles on `Spec A`. This is the last missing geometric input for `deg (div r) = 0` on
a proper curve: it converts a divisor on a finite cover into a divisor on the base.

## Main declarations

* `NormPushforward.map_principalCycle_eq_principalCycle_norm`: the theorem above for
  `AlgebraicGeometry.AlgebraicCycle.map` with any pair of weight functions agreeing at the closed
  points of `Spec B` (the hypothesis `hw`).
* `NormPushforward.map_principalCycle_eq_principalCycle_norm_dim`: the same for an arbitrary pair of
  certified dimension functions (`GromovWitten.AlgebraicGeometry.IntersectionTheory.
  DimensionFunction`), the form in which `ChowGroup.lean` takes pushforwards.
* `NormPushforward.properPushforward_principalCycleOf`: the same for
  `cyclesOfDimension.properPushforward` along the finite (hence proper) morphism
  `NormPushforward.specMap A B`, whose `IsFinite` instance is `instIsFinite_specMap`.
* `NormPushforward.map_principalCycle_apply_toSpecPoint_eq_finsum` and
  `NormPushforward.map_principalCycle_apply_toSpecPoint`: the coefficient of the pushforward at a
  closed point `m`, first as the fibre sum `∑_{q ↦ m} [κ(q):κ(m)] · ord_q(b)` and then as
  `ord_m (Algebra.norm A b)`.
* `NormPushforward.degreeCycle_principalCycleOf_norm`: the corollary for `ZeroCycleDegree`, namely
  `deg (div b) = deg (div (Algebra.norm A b))` for `A`, `B` algebras over a field `k` with
  `IsScalarTower k A B`. It rests on two general facts proved here:
  `NormPushforward.residueDegree_comp_eq_mul` (multiplicativity of the absolute residue degree,
  `[κ(x):k] = [κ(x):κ(p x)]·[κ(p x):k]`) and `NormPushforward.degreeCycle_map_eq` (the degree of a
  zero-cycle is unchanged by pushforward along a quasi-compact morphism of quasi-compact schemes
  over `Spec k`, via the fibrewise regrouping `NormPushforward.finsum_fibre_mul`).

## Proof outline

Comparing coefficients at a point `y` of `Spec A`:

* at the generic point (`y.asIdeal = ⊥`) both sides vanish: every point of the fibre is the generic
  point of `Spec B`, because a nonzero prime of `B` contracts to a nonzero prime of `A`
  (`Ideal.eq_bot_of_comap_eq_bot`, integrality), and `Scheme.ord` vanishes at points of coheight
  `≠ 1` (`map_principalCycle_apply_of_eq_bot`);
* at a closed point `m` (necessarily maximal, `isMaximal_of_ne_bot`) the fibre is reindexed by the
  maximal spectrum of the semilocal ring `locB B m = (A ∖ m)⁻¹B` (`fibrePoint`,
  `fibrePoint_injective`, `comap_fibrePoint`, `exists_fibrePoint`, packaged as
  `fibreEquivMaximalSpectrumLocB`), turning the coefficient into
  `∑ᶠ Q : MaximalSpectrum (locB B m), [κ(Q) : κ(locA m)] · ord_Q(b)`.

  Each term is the `Q`-summand of the semilocal length formula (`fibreTerm_eq_summand`,
  `summand_quotient_span_eq`): the residue degrees agree by `finrank_residueField_fibrePoint`
  (`residueDegree_specMap` computes `Scheme.Hom.residueDegree` in terms of `Ideal.ResidueField.map`,
  and the residue field of `(locB B m)_Q` is that of `B_q` by
  `IsLocalization.localizationLocalizationAtPrimeIsoLocalization`), and the two orders of vanishing
  agree because `(locB B m)_Q` is a localization of `B` at `q` (`SectionGysinIdentity.
  ring_ord_atPrime`). The sum of the summands is `Ring.ord (locA m) (Algebra.norm A b)` by
  `finsum_summand_locB_eq_ord_norm`, which is `OrderDeterminant.finsum_summand_eq_ord_norm`
  (Fulton A.2.3/A.2.6) applied to the finite free extension `locA m ⊆ locB B m`, together with
  `Algebra.norm_localization`. Finally `VectorBundle.scheme_ord_eq_localization` identifies
  `Ring.ord (locA m) (Algebra.norm A b)` with the coefficient of `div (Algebra.norm A b)` at `m`.
-/

-- Concrete `Spec R` / residue-field carriers only unify with the generic scheme instances at
-- default transparency; this option is what Mathlib's own `Scheme.Spec.residueFieldIso` uses.
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory.NormPushforward

/-! ## Transport of `Module.finrank` along a commuting square of ring isomorphisms -/

/-- **`Module.finrank` transports along a commuting square of ring isomorphisms.** If
`eK : K ≃+* K'` and `eL : L ≃+* L'` are ring isomorphisms of fields intertwining the structure maps
`algebraMap K L` and `algebraMap K' L'`, then `[L : K] = [L' : K']`. Proved by factoring
`algebraMap K L'` through `K'`: the `K`-dimension of `K'` is `1` (the structure map is `eK`, hence
bijective), so `Module.finrank_mul_finrank` gives `[L' : K] = [L' : K']`, while `eL` is a
`K`-linear equivalence `L ≃ₗ[K] L'`. -/
theorem finrank_congr_ringEquiv {K L K' L' : Type u} [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K' L'] (eK : K ≃+* K') (eL : L ≃+* L')
    (h : ∀ c, eL (algebraMap K L c) = algebraMap K' L' (eK c)) :
    Module.finrank K L = Module.finrank K' L' := by
  let _ : Algebra K K' := eK.toRingHom.toAlgebra
  let _ : Algebra K L' := ((algebraMap K' L').comp eK.toRingHom).toAlgebra
  have _ : IsScalarTower K K' L' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : Module.finrank K K' = 1 := by
    have e : K ≃ₗ[K] K' := LinearEquiv.ofBijective (Algebra.linearMap K K') eK.bijective
    rw [← e.finrank_eq, Module.finrank_self]
  have h2 : Module.finrank K L = Module.finrank K L' := by
    have hsmul : ∀ (c : K) (x : L), eL (c • x) = c • eL x := by
      intro c x
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, h c]
      rfl
    exact LinearEquiv.finrank_eq
      ({ eL.toAddEquiv with map_smul' := hsmul } : L ≃ₗ[K] L')
  rw [h2, ← Module.finrank_mul_finrank K K' L', h1, one_mul]

/-- Version of `finrank_congr_ringEquiv` for algebra structures supplied by ring homomorphisms on
both sides (the shape in which `Scheme.Hom.residueDegree` and `Ideal.ResidueField.map` present
themselves). -/
theorem finrank_congr_ringHom {K L K' L' : Type u} [Field K] [Field L] [Field K'] [Field L']
    (ψ : K →+* L) (ψ' : K' →+* L') (eK : K ≃+* K') (eL : L ≃+* L')
    (h : ∀ c, eL (ψ c) = ψ' (eK c)) :
    (letI := ψ.toAlgebra; Module.finrank K L) =
      (letI := ψ'.toAlgebra; Module.finrank K' L') := by
  let _ : Algebra K L := ψ.toAlgebra
  let _ : Algebra K' L' := ψ'.toAlgebra
  exact finrank_congr_ringEquiv eK eL h

/-- Version of `finrank_congr_ringEquiv` where only the source algebra structure is supplied by a
ring homomorphism, the target one being the ambient instance. -/
theorem finrank_congr_ringHom_left {K L K' L' : Type u} [Field K] [Field L] [Field K'] [Field L']
    [Algebra K' L'] (ψ : K →+* L) (eK : K ≃+* K') (eL : L ≃+* L')
    (h : ∀ c, eL (ψ c) = algebraMap K' L' (eK c)) :
    (letI := ψ.toAlgebra; Module.finrank K L) = Module.finrank K' L' := by
  let _ : Algebra K L := ψ.toAlgebra
  exact finrank_congr_ringEquiv eK eL h

/-! ## The residue field of an affine scheme at a point -/

/-- The residue field of `Spec R` at a point `x`, identified with Mathlib's `Ideal.ResidueField`
of the corresponding prime: the induced map on residue fields of the isomorphism `Spec.stalkIso`
between the stalk at `x` and `Localization.AtPrime x.asIdeal`. -/
noncomputable def specResidueFieldEquiv (R : CommRingCat.{u}) (x : ↥(Spec R)) :
    ↥((Spec R).residueField x) ≃+* x.asIdeal.ResidueField :=
  IsLocalRing.ResidueField.mapEquiv (Spec.stalkIso R x).commRingCatIsoToRingEquiv

/-- **The residue degree of `Spec.map φ` in terms of `Ideal.ResidueField`.** For `φ : R ⟶ S` a
morphism of commutative rings and `x` a point of `Spec S` with prime `q`, the residue degree of
`Spec.map φ` at `x` is the degree of the residue field extension `κ(q) / κ(q ∩ R)` in the sense of
`Ideal.ResidueField.map`. Both sides are transported into one another by `specResidueFieldEquiv`,
whose compatibility with the stalk maps is `Scheme.localRingHom_comp_stalkIso`. -/
theorem residueDegree_specMap (R S : CommRingCat.{u}) (φ : R ⟶ S) (x : PrimeSpectrum ↑S) :
    (Spec.map φ).residueDegree x =
      (letI := (Ideal.ResidueField.map ((Spec.map φ).base x).asIdeal x.asIdeal φ.hom rfl).toAlgebra;
        Module.finrank ((Spec.map φ).base x).asIdeal.ResidueField x.asIdeal.ResidueField) := by
  have hpt : ∀ z, (Spec.stalkIso S x).commRingCatIsoToRingEquiv
        (((Spec.map φ).stalkMap x).hom z) =
      Localization.localRingHom ((Spec.map φ).base x).asIdeal x.asIdeal φ.hom rfl
        ((Spec.stalkIso R ((Spec.map φ).base x)).commRingCatIsoToRingEquiv z) := by
    intro z
    refine (congrArg (fun w => (Spec.stalkIso S x).hom.hom w)
      (Scheme.localRingHom_comp_stalkIso_apply φ x z)).symm.trans ?_
    exact CategoryTheory.Iso.inv_hom_id_apply (Spec.stalkIso S x) _
  unfold Scheme.Hom.residueDegree
  refine finrank_congr_ringHom (K' := ((Spec.map φ).base x).asIdeal.ResidueField)
    (L' := x.asIdeal.ResidueField) _ _
    (specResidueFieldEquiv R ((Spec.map φ).base x)) (specResidueFieldEquiv S x) ?_
  intro c
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective c
  change IsLocalRing.ResidueField.map _
      (IsLocalRing.ResidueField.map ((Spec.map φ).stalkMap x).hom (IsLocalRing.residue _ z)) =
    IsLocalRing.ResidueField.map _
      (IsLocalRing.ResidueField.map _ (IsLocalRing.residue _ z))
  rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue,
    IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue]
  exact congrArg _ (hpt z)

/-- Variant of `residueDegree_specMap` in which the prime of `R` below `x` is given by a named
ideal `I` together with a proof that it is the contraction of `x.asIdeal`. -/
theorem residueDegree_specMap' (R S : CommRingCat.{u}) (φ : R ⟶ S) (x : PrimeSpectrum ↑S)
    (I : Ideal ↑R) [I.IsPrime] (hI : I = x.asIdeal.comap φ.hom) :
    (Spec.map φ).residueDegree x =
      (letI := (Ideal.ResidueField.map I x.asIdeal φ.hom hI).toAlgebra;
        Module.finrank I.ResidueField x.asIdeal.ResidueField) := by
  subst hI
  exact residueDegree_specMap R S φ x

/-! ## Localizing the finite free extension at a prime of the base -/

/-- `A` localized at a prime ideal `m`. -/
abbrev locA {A : Type u} [CommRing A] (m : Ideal A) [m.IsPrime] : Type u :=
  Localization.AtPrime m

/-- `B` localized at the image of `A ∖ m` in `B`. When `B` is module-finite over `A` this is a
semilocal ring whose maximal ideals are exactly the primes of `B` lying over `m`, and it is finite
and free over `locA m` when `B` is finite and free over `A`. -/
abbrev locB (B : Type u) [CommRing B] {A : Type u} [CommRing A] [Algebra A B] (m : Ideal A)
    [m.IsPrime] : Type u :=
  Localization (Algebra.algebraMapSubmonoid B m.primeCompl)

section LocalizationSetup

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (m : Ideal A) [m.IsPrime]

/-- `locA m` has Krull dimension `≤ 1` when `A` does: the Krull dimension of a localization at a
prime is the height of that prime, which is bounded by the Krull dimension of `A`. -/
theorem krullDimLE_one_locA [Ring.KrullDimLE 1 A] : Ring.KrullDimLE 1 (locA m) := by
  rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height m (locA m)]
  exact (Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top ‹m.IsPrime›)).trans
    (Ring.krullDimLE_iff.mp ‹Ring.KrullDimLE 1 A›)

/-- A basis of `B` over `A` localizes to a basis of `locB B m` over `locA m`. -/
noncomputable def basisLocB [Module.Free A B] [Module.Finite A B] :
    Module.Basis (Module.Free.ChooseBasisIndex A B) (locA m) (locB B m) :=
  (Module.Free.chooseBasis A B).localizationLocalization (locA m) m.primeCompl (locB B m)

instance instFreeLocB [Module.Free A B] [Module.Finite A B] :
    Module.Free (locA m) (locB B m) :=
  Module.Free.of_basis (basisLocB m)

instance instFiniteLocB [Module.Free A B] [Module.Finite A B] :
    Module.Finite (locA m) (locB B m) :=
  Module.Finite.of_basis (basisLocB m)

/-- The multiplicative set defining `locB B m` consists of non-zero-divisors of `B`, provided `B` is
a domain and `A → B` is injective: it is the image of `A ∖ m`, and `0 ∈ m`. -/
theorem algebraMapSubmonoid_le_nonZeroDivisors [IsDomain B]
    (hinj : Function.Injective (algebraMap A B)) :
    Algebra.algebraMapSubmonoid B m.primeCompl ≤ nonZeroDivisors B := by
  rintro _ ⟨s, hs, rfl⟩
  refine mem_nonZeroDivisors_iff_ne_zero.2 fun h => hs ?_
  have hs0 : s = 0 := hinj (by rw [h, map_zero])
  rw [hs0]
  exact m.zero_mem

end LocalizationSetup

/-! ## The norm formula at a prime of the base -/

section LocalNorm

attribute [local instance] LocalizedModule.moduleOfIsLocalization

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- **The `q`-summand of the semilocal length formula for a principal quotient.** For `q` a maximal
ideal of a module-finite algebra `B` over a local ring `A` and `c : B`, the `q`-summand of
`OrderSemilocal.summand` for `N = B ⧸ (c)` is `[κ(q) : κ_A] · Ring.ord (B_q) c`. This is the general
`c` version of `OrderBirational.summand_quotient_ideal_eq`, with the same proof. -/
theorem summand_quotient_span_eq [IsLocalRing A] [Module.Finite A B] (q : MaximalSpectrum B)
    (c : B) :
    OrderSemilocal.summand (A := A) (B ⧸ (Ideal.span {c} : Ideal B)) q =
      (Module.finrank (IsLocalRing.ResidueField A) q.asIdeal.ResidueField : ℕ∞) *
        Ring.ord (Localization.AtPrime q.asIdeal)
          (algebraMap B (Localization.AtPrime q.asIdeal) c) := by
  unfold OrderSemilocal.summand
  congr 1
  exact (OrderBirational.localizedModule_quotient_span_equiv q.asIdeal c).length_eq

variable [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsDomain B] [Module.Free A B]
  [Module.Finite A B]

/-- **The norm formula at a prime `m` of the base** (`OrderDeterminant.finsum_summand_eq_ord_norm`
applied to `locA m ⊆ locB B m`, together with `Algebra.norm_localization`): the sum over the
maximal ideals of `locB B m` of the semilocal summands of `locB B m ⧸ (b)` is the order of
vanishing of `Algebra.norm A b` in `locA m`. -/
theorem finsum_summand_locB_eq_ord_norm (hinj : Function.Injective (algebraMap A B))
    (m : Ideal A) [m.IsPrime] (b : B) (hb : b ≠ 0) :
    ∑ᶠ Q : MaximalSpectrum (locB B m),
        OrderSemilocal.summand (A := locA m)
          (locB B m ⧸ (Ideal.span {algebraMap B (locB B m) b} : Ideal (locB B m))) Q
      = Ring.ord (locA m) (algebraMap A (locA m) (Algebra.norm A b)) := by
  have hle := algebraMapSubmonoid_le_nonZeroDivisors m hinj
  have _ : Ring.KrullDimLE 1 (locA m) := krullDimLE_one_locA m
  have _ : IsDomain (locB B m) := IsLocalization.isDomain_localization hle
  have hb' : algebraMap B (locB B m) b ∈ nonZeroDivisors (locB B m) :=
    mem_nonZeroDivisors_iff_ne_zero.2 fun h =>
      hb (IsLocalization.injective (locB B m) hle (by rw [h, map_zero]))
  rw [← Algebra.norm_localization (Rₘ := locA m) (Sₘ := locB B m) A m.primeCompl b]
  exact OrderDeterminant.finsum_summand_eq_ord_norm hb'

end LocalNorm

/-! ## Points of the spectrum of a one-dimensional domain -/

section Points

variable {A : Type u} [CommRing A] [IsDomain A]

/-- **A nonzero prime of a domain of Krull dimension `≤ 1` is maximal.** If it weren't, a maximal
ideal strictly above it would force a chain of length `2`. -/
theorem isMaximal_of_ne_bot [Ring.KrullDimLE 1 A] (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) :
    p.IsMaximal := by
  obtain ⟨M, hM, hpM⟩ := p.exists_le_maximal (Ideal.IsPrime.ne_top ‹p.IsPrime›)
  rcases eq_or_lt_of_le hpM with heq | hlt
  · rw [heq]; exact hM
  · exfalso
    have h1 : p.height + 1 ≤ M.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have h2 : M.height ≤ (1 : ℕ∞) := by
      have hb := Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
      exact_mod_cast hb.trans (Ring.krullDimLE_iff.mp ‹Ring.KrullDimLE 1 A›)
    have h4 : (1 : ℕ∞) ≤ p.height :=
      Order.one_le_iff_ne_zero.mpr (by rw [ne_eq, Ideal.height_eq_zero_iff_eq_bot]; exact hp)
    have h5 : (2 : ℕ∞) ≤ p.height + 1 := by
      calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ p.height + 1 := by gcongr
    exact absurd (h5.trans (h1.trans h2)) (by norm_num)

/-- A point of `Spec A` whose prime is nonzero has specialisation-order coheight `1`. -/
theorem coheight_eq_one_of_ne_bot [Ring.KrullDimLE 1 A] (x : ↥(Spec (CommRingCat.of A)))
    (hx : x.asIdeal ≠ ⊥) : Order.coheight x = 1 := by
  have hco := VectorBundle.coheight_eq_ideal_height A x
  rw [hco]
  have h1 : x.asIdeal.height ≤ (1 : ℕ∞) := by
    have hb := Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top x.isPrime)
    exact_mod_cast hb.trans (Ring.krullDimLE_iff.mp ‹Ring.KrullDimLE 1 A›)
  exact le_antisymm h1 (Order.one_le_iff_ne_zero.mpr
    (by rw [ne_eq, Ideal.height_eq_zero_iff_eq_bot]; exact hx))

/-- The generic point of `Spec A` has specialisation-order coheight `≠ 1`. -/
theorem coheight_ne_one_of_eq_bot (x : ↥(Spec (CommRingCat.of A)))
    (hx : x.asIdeal = ⊥) : Order.coheight x ≠ 1 := by
  have hco := VectorBundle.coheight_eq_ideal_height A x
  rw [hco, hx, Ideal.height_bot]
  exact zero_ne_one

omit [IsDomain A] in
/-- **A certified dimension function of `Spec A` vanishes at every closed point.** The
inclusion-order coheight of a maximal ideal is `0`, and this coheight is the dimension function
(`VectorBundle.coheight_eq_dimension`). -/
theorem dimensionFunction_eq_zero_of_isMaximal (d : DimensionFunction (Spec (CommRingCat.of A)))
    (x : ↥(Spec (CommRingCat.of A))) (hmax : x.asIdeal.IsMaximal) : d x = 0 := by
  have h1 : @Order.coheight (PrimeSpectrum A) _ x = 0 := by
    rw [Order.coheight_eq_zero]
    intro y hxy
    exact le_of_eq (PrimeSpectrum.ext
      (hmax.eq_of_le y.isPrime.ne_top ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hxy)).symm)
  have h2 := VectorBundle.coheight_eq_dimension A d x
  rw [h1] at h2
  have h3 : Int.toNat (d x) = 0 := by exact_mod_cast h2.symm
  have h4 := d.nonnegative x
  change 0 ≤ d.toFun x at h4
  change d.toFun x = 0
  omega

end Points

/-! ## The maximal ideals of `locB B m` and the fibre over `m` -/

section Fibre

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (m : Ideal A) [m.IsPrime]

/-- A prime of `locA m` contracting to `m` is the maximal ideal: the contraction map on primes of a
localization is injective (`IsLocalization.map_under`). -/
theorem eq_maximalIdeal_of_comap_eq (P : Ideal (locA m)) [P.IsPrime]
    (hP : P.comap (algebraMap A (locA m)) = m) : P = IsLocalRing.maximalIdeal (locA m) := by
  have h1 := IsLocalization.map_under m.primeCompl (locA m) P
  have h2 := IsLocalization.map_under m.primeCompl (locA m)
    (IsLocalRing.maximalIdeal (locA m))
  have h3 : Ideal.under A P = Ideal.under A (IsLocalRing.maximalIdeal (locA m)) := by
    rw [IsLocalization.AtPrime.under_maximalIdeal (locA m) m]
    exact hP
  calc P = Ideal.map (algebraMap A (locA m)) (Ideal.under A P) := h1.symm
    _ = Ideal.map (algebraMap A (locA m))
        (Ideal.under A (IsLocalRing.maximalIdeal (locA m))) := by rw [h3]
    _ = IsLocalRing.maximalIdeal (locA m) := h2

/-- The point of `Spec B` below a maximal ideal of `locB B m`. -/
def fibrePoint (Q : MaximalSpectrum (locB B m)) : ↥(Spec (CommRingCat.of B)) :=
  PrimeSpectrum.comap (algebraMap B (locB B m)) ⟨Q.asIdeal, Q.isMaximal.isPrime⟩

@[simp]
theorem fibrePoint_asIdeal (Q : MaximalSpectrum (locB B m)) :
    (fibrePoint m Q).asIdeal = Q.asIdeal.comap (algebraMap B (locB B m)) := rfl

/-- `fibrePoint` is injective: an ideal of a localization is recovered from its contraction
(`IsLocalization.map_under`). -/
theorem fibrePoint_injective : Function.Injective (fibrePoint (B := B) m) := by
  intro Q Q' h
  have hQ : Q.asIdeal.IsPrime := Q.isMaximal.isPrime
  have hQ' : Q'.asIdeal.IsPrime := Q'.isMaximal.isPrime
  refine MaximalSpectrum.ext ?_
  have h1 := IsLocalization.map_under (Algebra.algebraMapSubmonoid B m.primeCompl)
    (locB B m) Q.asIdeal
  have h2 := IsLocalization.map_under (Algebra.algebraMapSubmonoid B m.primeCompl)
    (locB B m) Q'.asIdeal
  rw [← h1, ← h2]
  exact congrArg (Ideal.map (algebraMap B (locB B m)))
    (congrArg PrimeSpectrum.asIdeal h)

variable [Module.Free A B] [Module.Finite A B]

/-- A maximal ideal of `locB B m` lies over `m`: it contracts to a maximal ideal of the local ring
`locA m` (integrality), which must be the maximal ideal, whose contraction to `A` is `m`. -/
theorem comap_fibrePoint (Q : MaximalSpectrum (locB B m)) :
    (fibrePoint m Q).asIdeal.comap (algebraMap A B) = m := by
  have hQ : Q.asIdeal.IsPrime := Q.isMaximal.isPrime
  have hcomp : (fibrePoint m Q).asIdeal.comap (algebraMap A B) =
      (Q.asIdeal.comap (algebraMap (locA m) (locB B m))).comap (algebraMap A (locA m)) := by
    rw [fibrePoint_asIdeal, Ideal.comap_comap, Ideal.comap_comap,
      ← IsScalarTower.algebraMap_eq A B (locB B m),
      ← IsScalarTower.algebraMap_eq A (locA m) (locB B m)]
  have hmax : (Q.asIdeal.comap (algebraMap (locA m) (locB B m))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := locA m) Q.asIdeal
  rw [hcomp, IsLocalRing.eq_maximalIdeal hmax]
  exact IsLocalization.AtPrime.under_maximalIdeal (locA m) m

/-- Every prime of `B` lying over `m` is `fibrePoint m Q` for a (unique) maximal ideal `Q` of
`locB B m`: the extension of `q` to `locB B m` is prime (its complement misses the multiplicative
set), and contracts to the maximal ideal of `locA m`, hence is maximal by integrality. -/
theorem exists_fibrePoint (q : ↥(Spec (CommRingCat.of B)))
    (hq : q.asIdeal.comap (algebraMap A B) = m) : ∃ Q, fibrePoint m Q = q := by
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid B m.primeCompl : Set B)
      (q.asIdeal : Set B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hmem
    exact hs (hq ▸ hmem)
  have hJ : (q.asIdeal.map (algebraMap B (locB B m))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Algebra.algebraMapSubmonoid B m.primeCompl)
      (locB B m) q.asIdeal q.isPrime hdisj
  have hunder : (q.asIdeal.map (algebraMap B (locB B m))).comap (algebraMap B (locB B m))
      = q.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint (Algebra.algebraMapSubmonoid B m.primeCompl)
      (locB B m) q.isPrime hdisj
  have hPprime : ((q.asIdeal.map (algebraMap B (locB B m))).comap
      (algebraMap (locA m) (locB B m))).IsPrime := Ideal.comap_isPrime _ _
  have hPm : ((q.asIdeal.map (algebraMap B (locB B m))).comap
      (algebraMap (locA m) (locB B m))).comap (algebraMap A (locA m)) = m := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq A (locA m) (locB B m),
      IsScalarTower.algebraMap_eq A B (locB B m), ← Ideal.comap_comap, hunder, hq]
  have hJmax : (q.asIdeal.map (algebraMap B (locB B m))).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := locA m) _
      (by rw [eq_maximalIdeal_of_comap_eq m _ hPm]; exact IsLocalRing.maximalIdeal.isMaximal _)
  exact ⟨⟨q.asIdeal.map (algebraMap B (locB B m)), hJmax⟩, PrimeSpectrum.ext hunder⟩

/-- The canonical `B`-algebra isomorphism between the localization of `B` at `fibrePoint m Q` and
the localization of `locB B m` at `Q`, i.e.
`IsLocalization.localizationLocalizationAtPrimeIsoLocalization` for the multiplicative set
defining `locB B m`. -/
noncomputable def locQAlgEquiv (Q : MaximalSpectrum (locB B m)) :
    Localization.AtPrime (fibrePoint m Q).asIdeal ≃ₐ[B] Localization.AtPrime Q.asIdeal :=
  have _ : Q.asIdeal.IsPrime := Q.isMaximal.isPrime
  IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (Algebra.algebraMapSubmonoid B m.primeCompl) Q.asIdeal

omit [Module.Free A B] [Module.Finite A B] in
/-- The two routes `A → locA m → (locB B m)_Q` and `A → B → locB B m → (locB B m)_Q` from `A` into
the localization of `locB B m` at `Q` agree. -/
theorem algebraMap_locQ (Q : MaximalSpectrum (locB B m)) (a : A) :
    algebraMap A (Localization.AtPrime Q.asIdeal) a =
      algebraMap (locA m) (Localization.AtPrime Q.asIdeal) (algebraMap A (locA m) a) := by
  rw [IsScalarTower.algebraMap_apply A (locB B m) (Localization.AtPrime Q.asIdeal),
    IsScalarTower.algebraMap_apply (locA m) (locB B m) (Localization.AtPrime Q.asIdeal),
    IsScalarTower.algebraMap_apply A (locA m) (locB B m)]

/-- **Matching the residue degrees.** For `Q` a maximal ideal of `locB B m` with contraction
`q = fibrePoint m Q` in `B`, the residue degree `[κ(q) : κ(m)]` of `Ideal.ResidueField.map` agrees
with the residue degree `[κ(Q) : κ(locA m)]` occurring in `OrderSemilocal.summand`. The base fields
are literally the same type, and the top fields are identified by the residue field of
`locQAlgEquiv`. -/
theorem finrank_residueField_fibrePoint (Q : MaximalSpectrum (locB B m)) :
    (letI := (Ideal.ResidueField.map m (fibrePoint m Q).asIdeal (algebraMap A B)
        (comap_fibrePoint m Q).symm).toAlgebra;
      Module.finrank m.ResidueField (fibrePoint m Q).asIdeal.ResidueField) =
      Module.finrank (IsLocalRing.ResidueField (locA m)) Q.asIdeal.ResidueField := by
  have _ : Q.asIdeal.IsPrime := Q.isMaximal.isPrime
  have _ : IsScalarTower A (locA m) (Localization.AtPrime Q.asIdeal) :=
    IsScalarTower.of_algebraMap_eq (algebraMap_locQ m Q)
  refine finrank_congr_ringHom_left _ (RingEquiv.refl m.ResidueField)
    (IsLocalRing.ResidueField.mapAlgEquiv (locQAlgEquiv m Q)).toRingEquiv ?_
  have key : ((IsLocalRing.ResidueField.mapAlgEquiv
        (locQAlgEquiv m Q)).toRingEquiv : _ →+* _).comp
      (Ideal.ResidueField.map m (fibrePoint m Q).asIdeal (algebraMap A B)
        (comap_fibrePoint m Q).symm) =
      algebraMap (IsLocalRing.ResidueField (locA m)) Q.asIdeal.ResidueField := by
    refine Ideal.ResidueField.ringHom_ext (R := A) (RingHom.ext fun a => ?_)
    have h1 : algebraMap A Q.asIdeal.ResidueField a =
        algebraMap B Q.asIdeal.ResidueField (algebraMap A B a) :=
      IsScalarTower.algebraMap_apply A B _ a
    have h2 : algebraMap A Q.asIdeal.ResidueField a =
        algebraMap (IsLocalRing.ResidueField (locA m)) Q.asIdeal.ResidueField
          (algebraMap A m.ResidueField a) :=
      IsScalarTower.algebraMap_apply A (IsLocalRing.ResidueField (locA m)) _ a
    simp only [RingHom.comp_apply]
    rw [Ideal.ResidueField.map_algebraMap m (fibrePoint m Q).asIdeal (algebraMap A B)
      (comap_fibrePoint m Q).symm a]
    change (IsLocalRing.ResidueField.mapAlgEquiv (locQAlgEquiv m Q))
      (algebraMap B (fibrePoint m Q).asIdeal.ResidueField (algebraMap A B a)) = _
    rw [AlgEquiv.commutes, ← h1, h2]
  exact fun c => RingHom.congr_fun key c

/-- **The fibre of `Spec B → Spec A` over `m` is the maximal spectrum of `locB B m`.** Injectivity
is `fibrePoint_injective`, surjectivity is `exists_fibrePoint`, and `comap_fibrePoint` says the
image lies in the fibre. -/
noncomputable def fibreEquivMaximalSpectrumLocB :
    MaximalSpectrum (locB B m) ≃
      {x : ↥(Spec (CommRingCat.of B)) // x.asIdeal.comap (algebraMap A B) = m} :=
  Equiv.ofBijective (fun Q => ⟨fibrePoint m Q, comap_fibrePoint m Q⟩)
    ⟨fun _ _ h => fibrePoint_injective m (congrArg Subtype.val h),
      fun x => (exists_fibrePoint m x.1 x.2).imp fun _ h => Subtype.ext h⟩

end Fibre

/-! ## The main theorem -/

/-- The morphism of affine schemes `Spec B ⟶ Spec A` induced by `algebraMap A B`. -/
noncomputable abbrev specMap (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

/-- The principal cycle of a nonzero element of an integral Noetherian ring, on its spectrum. -/
noncomputable abbrev principalCycleOf (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (r : R) (hr : r ≠ 0) : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ :=
  (Spec (CommRingCat.of R)).principalCycle
    (VectorBundle.functionFieldUnit (CommRingCat.of R) r hr :
      (Spec (CommRingCat.of R)).functionField)

/-- The point of `Spec A` attached to a maximal ideal of `A`. -/
def toSpecPoint {A : Type u} [CommRing A] (m : MaximalSpectrum A) :
    ↥(Spec (CommRingCat.of A)) :=
  m.toPrimeSpectrum

section Main

variable {A B : Type u} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
  [IsNoetherianRing A] [IsNoetherianRing B] [Ring.KrullDimLE 1 A] [Ring.KrullDimLE 1 B]
  [Algebra A B] [Module.Free A B] [Module.Finite A B]

omit [IsDomain A] [IsDomain B] [IsNoetherianRing A] [IsNoetherianRing B] [Ring.KrullDimLE 1 A]
  [Ring.KrullDimLE 1 B] in
/-- A prime of `B` lying over a nonzero prime of `A` is itself nonzero. -/
theorem fibrePoint_asIdeal_ne_bot (hinj : Function.Injective (algebraMap A B))
    (m : MaximalSpectrum A) (hm : m.asIdeal ≠ ⊥) (Q : MaximalSpectrum (locB B m.asIdeal)) :
    (fibrePoint m.asIdeal Q).asIdeal ≠ ⊥ := by
  intro h
  apply hm
  have hbot : (⊥ : Ideal B).comap (algebraMap A B) = ⊥ := by
    ext a
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact ⟨fun ha => hinj (by rw [ha, map_zero]), fun ha => by rw [ha, map_zero]⟩
  rw [← comap_fibrePoint m.asIdeal Q, h, hbot]

/-- The term `[κ(q) : κ(m)] · ord_q(b)` of the fibre sum, for `q = fibrePoint m Q`. -/
noncomputable def fibreTerm (m : MaximalSpectrum A) (b : B)
    (Q : MaximalSpectrum (locB B m.asIdeal)) : ℕ :=
  (specMap A B).residueDegree (fibrePoint m.asIdeal Q) *
    (Ring.ord (Localization.AtPrime (fibrePoint m.asIdeal Q).asIdeal)
      (algebraMap B (Localization.AtPrime (fibrePoint m.asIdeal Q).asIdeal) b)).toNat

omit [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
/-- **The termwise comparison.** The fibre term `[κ(q) : κ(m)] · ord_q(b)` of the pushforward is
the `Q`-summand of the semilocal length formula for `locB B m ⧸ (b)` over `locA m`: the residue
degrees agree by `finrank_residueField_fibrePoint`, and the two orders of vanishing agree because
`(locB B m)_Q` is a localization of `B` at `q` (`SectionGysinIdentity.ring_ord_atPrime`). -/
theorem fibreTerm_eq_summand (hinj : Function.Injective (algebraMap A B)) (b : B) (hb : b ≠ 0)
    (m : MaximalSpectrum A) (hm : m.asIdeal ≠ ⊥) (Q : MaximalSpectrum (locB B m.asIdeal)) :
    ((fibreTerm m b Q : ℕ) : ℕ∞) =
      OrderSemilocal.summand (A := locA m.asIdeal)
        (locB B m.asIdeal ⧸ (Ideal.span {algebraMap B (locB B m.asIdeal) b} :
          Ideal (locB B m.asIdeal))) Q := by
  have hne := fibrePoint_asIdeal_ne_bot hinj m hm Q
  have hco := coheight_eq_one_of_ne_bot (A := B) (fibrePoint m.asIdeal Q) hne
  have hfin : Ring.ord (Localization.AtPrime (fibrePoint m.asIdeal Q).asIdeal)
      (algebraMap B (Localization.AtPrime (fibrePoint m.asIdeal Q).asIdeal) b) ≠ ⊤ :=
    VectorBundle.localization_ord_ne_top (CommRingCat.of B) (fibrePoint m.asIdeal Q) b hb hco
  have hrd : (specMap A B).residueDegree (fibrePoint m.asIdeal Q) =
      Module.finrank (IsLocalRing.ResidueField (locA m.asIdeal)) Q.asIdeal.ResidueField := by
    rw [residueDegree_specMap' (CommRingCat.of A) (CommRingCat.of B)
      (CommRingCat.ofHom (algebraMap A B)) (fibrePoint m.asIdeal Q) m.asIdeal
      (comap_fibrePoint m.asIdeal Q).symm]
    exact finrank_residueField_fibrePoint m.asIdeal Q
  have _ : IsLocalization.AtPrime (Localization.AtPrime Q.asIdeal)
      (fibrePoint m.asIdeal Q).asIdeal :=
    IsLocalization.isLocalization_atPrime_localization_atPrime
      (Algebra.algebraMapSubmonoid B m.asIdeal.primeCompl) Q.asIdeal
  have hord : Ring.ord (Localization.AtPrime Q.asIdeal)
        (algebraMap (locB B m.asIdeal) (Localization.AtPrime Q.asIdeal)
          (algebraMap B (locB B m.asIdeal) b)) =
      Ring.ord (Localization.AtPrime (fibrePoint m.asIdeal Q).asIdeal)
        (algebraMap B (Localization.AtPrime (fibrePoint m.asIdeal Q).asIdeal) b) := by
    rw [← IsScalarTower.algebraMap_apply B (locB B m.asIdeal)
      (Localization.AtPrime Q.asIdeal)]
    exact VectorBundle.SectionGysinIdentity.ring_ord_atPrime (fibrePoint m.asIdeal Q).asIdeal
      (Localization.AtPrime Q.asIdeal) b
  rw [summand_quotient_span_eq (A := locA m.asIdeal) Q (algebraMap B (locB B m.asIdeal) b), hord,
    fibreTerm, hrd, Nat.cast_mul, ENat.natCast_toNat hfin]

omit [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
/-- **The coefficient of the pushforward at a closed point of `Spec A` is the fibre sum**
`∑_{q ↦ m} [κ(q):κ(m)] · ord_q(b)`. The fibre of `Spec B → Spec A` over `m` is reindexed by
`MaximalSpectrum (locB B m)` (`fibrePoint`, `exists_fibrePoint`, `comap_fibrePoint`), and each
`AlgebraicCycle.mapCoeff` is the residue degree because the weight functions agree at the closed
points of the fibre (`hw`). -/
theorem map_principalCycle_apply_toSpecPoint_eq_finsum
    (hinj : Function.Injective (algebraMap A B))
    (wx : ↥(Spec (CommRingCat.of B)) → ℤ) (wy : ↥(Spec (CommRingCat.of A)) → ℤ)
    (hw : ∀ x : ↥(Spec (CommRingCat.of B)), x.asIdeal ≠ ⊥ →
      wx x = wy ((specMap A B).base x))
    (b : B) (hb : b ≠ 0) (m : MaximalSpectrum A) (hm : m.asIdeal ≠ ⊥) :
    AlgebraicCycle.map (specMap A B) wx wy (principalCycleOf B b hb) (toSpecPoint m) =
      ∑ᶠ Q : MaximalSpectrum (locB B m.asIdeal), ((fibreTerm m b Q : ℕ) : ℚ) := by
  classical
  have hset : (specMap A B).base ⁻¹' {toSpecPoint m} =
      Set.range (fibrePoint (B := B) m.asIdeal) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun hx => exists_fibrePoint m.asIdeal x (congrArg PrimeSpectrum.asIdeal hx), ?_⟩
    rintro ⟨Q, rfl⟩
    exact PrimeSpectrum.ext (comap_fibrePoint m.asIdeal Q)
  have hunfold : AlgebraicCycle.map (specMap A B) wx wy (principalCycleOf B b hb)
      (toSpecPoint m) = ∑ᶠ x ∈ (specMap A B).base ⁻¹' {toSpecPoint m},
        principalCycleOf B b hb x *
          (AlgebraicCycle.mapCoeff (specMap A B) wx wy x : ℚ) := rfl
  have hterm : ∀ Q : MaximalSpectrum (locB B m.asIdeal),
      principalCycleOf B b hb (fibrePoint m.asIdeal Q) *
          (AlgebraicCycle.mapCoeff (specMap A B) wx wy (fibrePoint m.asIdeal Q) : ℚ) =
        ((fibreTerm m b Q : ℕ) : ℚ) := by
    intro Q
    have hne := fibrePoint_asIdeal_ne_bot hinj m hm Q
    have hco := coheight_eq_one_of_ne_bot (A := B) (fibrePoint m.asIdeal Q) hne
    have hmc : AlgebraicCycle.mapCoeff (specMap A B) wx wy (fibrePoint m.asIdeal Q) =
        (specMap A B).residueDegree (fibrePoint m.asIdeal Q) := by
      unfold AlgebraicCycle.mapCoeff
      rw [if_pos (hw _ hne)]
    rw [hmc, Scheme.principalCycle_apply, VectorBundle.functionFieldUnit_val,
      VectorBundle.scheme_ord_eq_localization (CommRingCat.of B) (fibrePoint m.asIdeal Q) b hb hco,
      fibreTerm]
    push_cast
    ring
  rw [hunfold, hset, finsum_mem_range (fibrePoint_injective m.asIdeal), finsum_congr hterm]

/-- **The coefficient of the pushforward at a closed point of `Spec A`.** The fibre sum
`∑_{q ↦ m} [κ(q):κ(m)] · ord_q(b)` of `map_principalCycle_apply_toSpecPoint_eq_finsum` equals
`ord_m (Algebra.norm A b)`, by `finsum_summand_locB_eq_ord_norm` (that is, by D4's
`OrderDeterminant.finsum_summand_eq_ord_norm` applied to `locA m ⊆ locB B m`) together with the
termwise identification `fibreTerm_eq_summand`. -/
theorem map_principalCycle_apply_toSpecPoint (hinj : Function.Injective (algebraMap A B))
    (wx : ↥(Spec (CommRingCat.of B)) → ℤ) (wy : ↥(Spec (CommRingCat.of A)) → ℤ)
    (hw : ∀ x : ↥(Spec (CommRingCat.of B)), x.asIdeal ≠ ⊥ →
      wx x = wy ((specMap A B).base x))
    (b : B) (hb : b ≠ 0) (m : MaximalSpectrum A) (hm : m.asIdeal ≠ ⊥) :
    AlgebraicCycle.map (specMap A B) wx wy (principalCycleOf B b hb) (toSpecPoint m) =
      ((Ring.ord (locA m.asIdeal)
        (algebraMap A (locA m.asIdeal) (Algebra.norm A b))).toNat : ℚ) := by
  have hcast : (∑ᶠ Q : MaximalSpectrum (locB B m.asIdeal), ((fibreTerm m b Q : ℕ) : ℚ)) =
      ((∑ᶠ Q : MaximalSpectrum (locB B m.asIdeal), fibreTerm m b Q : ℕ) : ℚ) :=
    ((Nat.castRingHom ℚ).toAddMonoidHom.map_finsum_of_injective Nat.cast_injective _).symm
  have hcast2 : ((∑ᶠ Q : MaximalSpectrum (locB B m.asIdeal), fibreTerm m b Q : ℕ) : ℕ∞) =
      ∑ᶠ Q : MaximalSpectrum (locB B m.asIdeal), ((fibreTerm m b Q : ℕ) : ℕ∞) :=
    (Nat.castAddMonoidHom ℕ∞).map_finsum_of_injective Nat.cast_injective _
  rw [map_principalCycle_apply_toSpecPoint_eq_finsum hinj wx wy hw b hb m hm, hcast]
  have hnat : ((∑ᶠ Q : MaximalSpectrum (locB B m.asIdeal), fibreTerm m b Q : ℕ) : ℕ∞) =
      Ring.ord (locA m.asIdeal) (algebraMap A (locA m.asIdeal) (Algebra.norm A b)) := by
    rw [hcast2, finsum_congr (fun Q => fibreTerm_eq_summand hinj b hb m hm Q)]
    exact finsum_summand_locB_eq_ord_norm hinj m.asIdeal b hb
  have hnat' := congrArg ENat.toNat hnat
  rw [ENat.toNat_natCast] at hnat'
  rw [hnat']

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Ring.KrullDimLE 1 B] [Module.Free A B] in
/-- **The coefficient of the pushforward vanishes at the generic point of `Spec A`.** Every point
of the fibre over the generic point is the generic point of `Spec B` (a nonzero prime of `B`
contracts to a nonzero prime of `A`, by integrality), where the order of vanishing is `0`. -/
theorem map_principalCycle_apply_of_eq_bot
    (wx : ↥(Spec (CommRingCat.of B)) → ℤ) (wy : ↥(Spec (CommRingCat.of A)) → ℤ)
    (b : B) (hb : b ≠ 0) (y : ↥(Spec (CommRingCat.of A))) (hy : y.asIdeal = ⊥) :
    AlgebraicCycle.map (specMap A B) wx wy (principalCycleOf B b hb) y = 0 := by
  classical
  have hunfold : AlgebraicCycle.map (specMap A B) wx wy (principalCycleOf B b hb) y =
      ∑ᶠ x ∈ (specMap A B).base ⁻¹' {y}, principalCycleOf B b hb x *
        (AlgebraicCycle.mapCoeff (specMap A B) wx wy x : ℚ) := rfl
  rw [hunfold]
  refine finsum_mem_of_eqOn_zero fun x hx => ?_
  have hcomap : x.asIdeal.comap (algebraMap A B) = ⊥ := by
    have h := congrArg PrimeSpectrum.asIdeal (hx : (specMap A B).base x = y)
    rw [hy] at h
    exact h
  have hxb : x.asIdeal = ⊥ := Ideal.eq_bot_of_comap_eq_bot (R := A) hcomap
  rw [Scheme.principalCycle_apply,
    _root_.AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one
      (coheight_ne_one_of_eq_bot x hxb)]
  simp

/-- **Fulton, *Intersection Theory*, Proposition 1.4, affine finite free case.** Let `A ⊆ B` be
Noetherian domains of Krull dimension `≤ 1` with `B` finite and free as an `A`-module and
`algebraMap A B` injective, and let `p : Spec B ⟶ Spec A` be the induced (finite, hence proper)
morphism. For `b : B` nonzero, the pushforward of the principal cycle of `b` is the principal cycle
of `Algebra.norm A b`:

`p_* (div b) = div (Algebra.norm A b)`.

The weight functions `wx`, `wy` used by `AlgebraicCycle.map` are only required to agree at closed
points (`hw`), which holds for any pair of certified dimension functions
(`map_principalCycle_eq_principalCycle_norm_dim`). -/
theorem map_principalCycle_eq_principalCycle_norm (hinj : Function.Injective (algebraMap A B))
    (wx : ↥(Spec (CommRingCat.of B)) → ℤ) (wy : ↥(Spec (CommRingCat.of A)) → ℤ)
    (hw : ∀ x : ↥(Spec (CommRingCat.of B)), x.asIdeal ≠ ⊥ →
      wx x = wy ((specMap A B).base x))
    (b : B) (hb : b ≠ 0) :
    AlgebraicCycle.map (specMap A B) wx wy (principalCycleOf B b hb) =
      principalCycleOf A (Algebra.norm A b)
        (OrderDeterminant.norm_ne_zero (mem_nonZeroDivisors_iff_ne_zero.2 hb)) := by
  refine DFunLike.ext _ _ fun y => ?_
  by_cases hy : y.asIdeal = ⊥
  · rw [map_principalCycle_apply_of_eq_bot wx wy b hb y hy, Scheme.principalCycle_apply,
      _root_.AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one
        (coheight_ne_one_of_eq_bot y hy)]
    simp
  · have hmax : y.asIdeal.IsMaximal := isMaximal_of_ne_bot y.asIdeal hy
    have hco : Order.coheight y = 1 := coheight_eq_one_of_ne_bot y hy
    have hnorm : Algebra.norm A b ≠ 0 :=
      OrderDeterminant.norm_ne_zero (mem_nonZeroDivisors_iff_ne_zero.2 hb)
    have hval : AlgebraicCycle.map (specMap A B) wx wy (principalCycleOf B b hb) y =
        ((Ring.ord (locA (⟨y.asIdeal, hmax⟩ : MaximalSpectrum A).asIdeal)
          (algebraMap A (locA (⟨y.asIdeal, hmax⟩ : MaximalSpectrum A).asIdeal)
            (Algebra.norm A b))).toNat : ℚ) :=
      map_principalCycle_apply_toSpecPoint hinj wx wy hw b hb ⟨y.asIdeal, hmax⟩ hy
    rw [hval, Scheme.principalCycle_apply, VectorBundle.functionFieldUnit_val,
      VectorBundle.scheme_ord_eq_localization (CommRingCat.of A) y (Algebra.norm A b) hnorm hco]
    push_cast
    ring

/-- **Fulton, Prop. 1.4 in the dimension-graded form used by `ChowGroup.lean`.** For any two
certified dimension functions on `Spec B` and `Spec A`, the pushforward of the principal cycle of
`b` along `Spec B ⟶ Spec A` is the principal cycle of `Algebra.norm A b`: both dimension functions
vanish at closed points (`dimensionFunction_eq_zero_of_isMaximal`), so the weight condition of
`map_principalCycle_eq_principalCycle_norm` holds. -/
theorem map_principalCycle_eq_principalCycle_norm_dim
    (hinj : Function.Injective (algebraMap A B))
    (dB : DimensionFunction (Spec (CommRingCat.of B)))
    (dA : DimensionFunction (Spec (CommRingCat.of A))) (b : B) (hb : b ≠ 0) :
    AlgebraicCycle.map (specMap A B) dB dA (principalCycleOf B b hb) =
      principalCycleOf A (Algebra.norm A b)
        (OrderDeterminant.norm_ne_zero (mem_nonZeroDivisors_iff_ne_zero.2 hb)) := by
  refine map_principalCycle_eq_principalCycle_norm hinj _ _ (fun x hx => ?_) b hb
  have h1 : dB x = 0 :=
    dimensionFunction_eq_zero_of_isMaximal dB x (isMaximal_of_ne_bot x.asIdeal hx)
  have h2 : dA ((specMap A B).base x) = 0 := by
    refine dimensionFunction_eq_zero_of_isMaximal dA _ (isMaximal_of_ne_bot _ fun h => ?_)
    exact hx (Ideal.eq_bot_of_comap_eq_bot (R := A) h)
  rw [h1, h2]

/-! ## The dimension-graded proper pushforward -/

/-- `Spec B ⟶ Spec A` is a finite morphism, hence proper. -/
instance instIsFinite_specMap : IsFinite (specMap A B) := by
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

omit [Module.Free A B] [Module.Finite A B] [Ring.KrullDimLE 1 B] [IsDomain B]
  [IsNoetherianRing B] [Algebra A B] in
/-- The principal cycle of a nonzero element of a one-dimensional Noetherian domain is a cycle of
dimension `0`: its coefficients vanish off the closed points, where every certified dimension
function is `0`. -/
theorem principalCycleOf_mem_cyclesOfDimension
    (d : DimensionFunction (Spec (CommRingCat.of A))) (a : A) (ha : a ≠ 0) :
    principalCycleOf A a ha ∈ cyclesOfDimension (Spec (CommRingCat.of A)) d 0 := by
  intro x hx
  have hbot : x.asIdeal = ⊥ := by
    by_contra h
    exact hx (dimensionFunction_eq_zero_of_isMaximal d x (isMaximal_of_ne_bot x.asIdeal h))
  rw [Scheme.principalCycle_apply,
    _root_.AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one
      (coheight_ne_one_of_eq_bot x hbot)]
  simp

/-- **Fulton, Prop. 1.4, for the dimension-graded proper pushforward of `ChowGroup.lean`.** The
proper pushforward along the finite morphism `Spec B ⟶ Spec A` of the dimension-`0` cycle
`div b` is `div (Algebra.norm A b)`. -/
theorem properPushforward_principalCycleOf (hinj : Function.Injective (algebraMap A B))
    (dB : DimensionFunction (Spec (CommRingCat.of B)))
    (dA : DimensionFunction (Spec (CommRingCat.of A))) (b : B) (hb : b ≠ 0) :
    cyclesOfDimension.properPushforward (dimension := dB) (dimensionY := dA) (i := 0)
        (specMap A B)
        ⟨principalCycleOf B b hb, principalCycleOf_mem_cyclesOfDimension dB b hb⟩ =
      ⟨principalCycleOf A (Algebra.norm A b)
          (OrderDeterminant.norm_ne_zero (mem_nonZeroDivisors_iff_ne_zero.2 hb)),
        principalCycleOf_mem_cyclesOfDimension dA _ _⟩ :=
  Subtype.ext (map_principalCycle_eq_principalCycle_norm_dim hinj dB dA b hb)

end Main

/-! ## Compatibility of the degree with pushforward -/

section Degree

/-- **Summing a product over the fibres of a map.** For `F` with finite support and any weight
`c : β → ℚ`, `∑ᶠ y, (∑ᶠ x ∈ q ⁻¹' {y}, F x) * c y = ∑ᶠ x, F x * c (q x)`. Both sides are rewritten
as `Finset` sums over the (finite) support of `F` and its image, where the identity is
`Finset.sum_fiberwise_of_maps_to`. -/
theorem finsum_fibre_mul {α β : Type*} (q : α → β) (F : α → ℚ) (c : β → ℚ)
    (hF : (Function.support F).Finite) :
    ∑ᶠ y : β, (∑ᶠ x ∈ q ⁻¹' {y}, F x) * c y = ∑ᶠ x : α, F x * c (q x) := by
  classical
  have hsub : Function.support F ⊆ ↑hF.toFinset := by
    intro x hx
    simpa using hx
  have hinner : ∀ y : β, (∑ᶠ x ∈ q ⁻¹' {y}, F x) =
      ∑ x ∈ hF.toFinset with q x = y, F x := by
    intro y
    rw [← finsum_mem_coe_finset F (hF.toFinset.filter fun x => q x = y)]
    refine finsum_mem_inter_support_eq' F _ _ fun x hx => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_filter, Set.mem_ofPred_eq,
      Set.Finite.mem_toFinset]
    exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  have houter : Function.support (fun y : β => (∑ x ∈ hF.toFinset with q x = y, F x) * c y) ⊆
      ↑(hF.toFinset.image q) := by
    intro y hy
    by_contra hcon
    apply hy
    have hempty : (hF.toFinset.filter fun x => q x = y) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun {x} hx hqx => hcon ?_
      exact hqx ▸ Finset.mem_image_of_mem q hx
    simp [hempty]
  have hright : Function.support (fun x : α => F x * c (q x)) ⊆ ↑hF.toFinset :=
    (Function.support_mul_subset_left _ _).trans hsub
  simp_rw [hinner]
  rw [finsum_eq_finsetSum_of_support_subset _ houter,
    finsum_eq_finsetSum_of_support_subset _ hright]
  rw [← Finset.sum_fiberwise_of_maps_to (t := hF.toFinset.image q)
    (fun x hx => Finset.mem_image_of_mem q hx) fun x => F x * c (q x)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.1 hx).2]

/-- **Multiplicativity of the absolute residue degree.** For `p : X ⟶ Y` and a structure morphism
`g : Y ⟶ Spec k`, `[κ(x) : k] = [κ(x) : κ(p x)] · [κ(p x) : k]`: the residue field extension of `p`
at `x` fits into the scalar tower `k → κ(p x) → κ(x)` (naturality of
`FiniteTypeDimension.residueMap`, `FiniteTypeDimension.residueFieldMap_residueMap`), and
`Module.finrank_mul_finrank` applies. -/
theorem residueDegree_comp_eq_mul {k : Type u} [Field k] {X Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of k)) (p : X ⟶ Y) (x : X) :
    ZeroCycleDegree.residueDegree (p ≫ g) x =
      p.residueDegree x * ZeroCycleDegree.residueDegree g (p.base x) := by
  let _ : Algebra k ↥(Y.residueField (p.base x)) :=
    (FiniteTypeDimension.residueMap g (p.base x)).toAlgebra
  let _ : Algebra k ↥(X.residueField x) :=
    (FiniteTypeDimension.residueMap (p ≫ g) x).toAlgebra
  let _ : Algebra ↥(Y.residueField (p.base x)) ↥(X.residueField x) :=
    (p.residueFieldMap x).hom.toAlgebra
  have _ : IsScalarTower k ↥(Y.residueField (p.base x)) ↥(X.residueField x) :=
    IsScalarTower.of_algebraMap_eq fun c =>
      (FiniteTypeDimension.residueFieldMap_residueMap g p x c).symm
  have h := Module.finrank_mul_finrank k ↥(Y.residueField (p.base x)) ↥(X.residueField x)
  change ZeroCycleDegree.residueDegree (p ≫ g) x = _
  rw [mul_comm]
  exact h.symm

/-- **The degree of a zero-cycle is unchanged by pushforward.** For `p : X ⟶ Y` quasi-compact
between quasi-compact schemes over `Spec k` and `α` a cycle on `X` whose weight functions agree on
the support of `α` (`hw`), `deg (p_* α) = deg α`. This is `finsum_fibre_mul` (regrouping the sum
defining the degree over the fibres of `p`) together with the multiplicativity of the residue degree
(`residueDegree_comp_eq_mul`). -/
theorem degreeCycle_map_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of k)) (p : X ⟶ Y)
    [_root_.AlgebraicGeometry.QuasiCompact p] [CompactSpace X] [CompactSpace Y]
    (wx : X → ℤ) (wy : Y → ℤ) (α : AlgebraicCycle X ℚ)
    (hw : ∀ x ∈ Function.support (⇑α), wx x = wy (p.base x)) :
    ZeroCycleDegree.degreeCycle g (AlgebraicCycle.map p wx wy α) =
      ZeroCycleDegree.degreeCycle (p ≫ g) α := by
  classical
  have hF : (Function.support
      (fun x : X => α x * (AlgebraicCycle.mapCoeff p wx wy x : ℚ))).Finite :=
    (ZeroCycleDegree.finite_support α).subset (Function.support_mul_subset_left _ _)
  rw [ZeroCycleDegree.degreeCycle_apply, ZeroCycleDegree.degreeCycle_apply]
  have hLHS : (∑ᶠ y : Y, AlgebraicCycle.map p wx wy α y *
        (ZeroCycleDegree.residueDegree g y : ℚ)) =
      ∑ᶠ y : Y, (∑ᶠ x ∈ p.base ⁻¹' {y}, α x * (AlgebraicCycle.mapCoeff p wx wy x : ℚ)) *
        (ZeroCycleDegree.residueDegree g y : ℚ) := rfl
  rw [hLHS, finsum_fibre_mul p.base (fun x => α x * (AlgebraicCycle.mapCoeff p wx wy x : ℚ))
    (fun y => (ZeroCycleDegree.residueDegree g y : ℚ)) hF]
  refine finsum_congr fun x => ?_
  by_cases hα : α x = 0
  · simp [hα]
  · have hmc : AlgebraicCycle.mapCoeff p wx wy x = p.residueDegree x := by
      unfold AlgebraicCycle.mapCoeff
      rw [if_pos (hw x hα)]
    rw [mul_assoc, hmc, ← Nat.cast_mul, ← residueDegree_comp_eq_mul g p x]

variable {A B : Type u} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
  [IsNoetherianRing A] [IsNoetherianRing B] [Ring.KrullDimLE 1 A] [Ring.KrullDimLE 1 B]
  [Algebra A B] [Module.Free A B] [Module.Finite A B]

/-- The structure morphism `Spec A ⟶ Spec k` of a `k`-algebra `A`. -/
noncomputable abbrev structureMor (k A : Type u) [CommRing k] [CommRing A] [Algebra k A] :
    Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k A))

omit [IsDomain A] [IsDomain B] [IsNoetherianRing A] [IsNoetherianRing B] [Ring.KrullDimLE 1 A]
  [Ring.KrullDimLE 1 B] [Module.Free A B] [Module.Finite A B] in
/-- The structure morphism of `B` over `k` factors through `Spec A`. -/
theorem specMap_comp_structureMor (k : Type u) [CommRing k] [Algebra k A] [Algebra k B]
    [IsScalarTower k A B] :
    specMap A B ≫ structureMor k A = structureMor k B := by
  rw [specMap, structureMor, structureMor, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq k A B]

omit [Ring.KrullDimLE 1 B] in
/-- The support of a principal cycle consists of closed points. -/
theorem asIdeal_ne_bot_of_mem_support (b : B) (hb : b ≠ 0)
    {x : ↥(Spec (CommRingCat.of B))} (hx : x ∈ Function.support (⇑(principalCycleOf B b hb))) :
    x.asIdeal ≠ ⊥ := by
  intro h
  apply hx
  rw [Scheme.principalCycle_apply,
    _root_.AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one
      (coheight_ne_one_of_eq_bot x h)]
  simp

/-- **Corollary of Fulton's Proposition 1.4: the degree of `div b` on `Spec B` is the degree of
`div (Algebra.norm A b)` on `Spec A`.** Here `A` and `B` are `k`-algebras and the structure morphism
of `Spec B` factors as `Spec B ⟶ Spec A ⟶ Spec k` (`specMap_comp_structureMor`). Combines
`map_principalCycle_eq_principalCycle_norm` (for the constant weight functions, which trivially
agree) with `degreeCycle_map_eq`. -/
theorem degreeCycle_principalCycleOf_norm (k : Type u) [Field k] [Algebra k A] [Algebra k B]
    [IsScalarTower k A B] (hinj : Function.Injective (algebraMap A B)) (b : B) (hb : b ≠ 0) :
    ZeroCycleDegree.degreeCycle (structureMor k B) (principalCycleOf B b hb) =
      ZeroCycleDegree.degreeCycle (structureMor k A)
        (principalCycleOf A (Algebra.norm A b)
          (OrderDeterminant.norm_ne_zero (mem_nonZeroDivisors_iff_ne_zero.2 hb))) := by
  rw [← map_principalCycle_eq_principalCycle_norm hinj (fun _ => 0) (fun _ => 0)
      (fun _ _ => rfl) b hb,
    degreeCycle_map_eq (structureMor k A) (specMap A B) (fun _ => 0) (fun _ => 0)
      (principalCycleOf B b hb) (fun _ _ => rfl), specMap_comp_structureMor k]

end Degree

end GromovWitten.AlgebraicGeometry.IntersectionTheory.NormPushforward
