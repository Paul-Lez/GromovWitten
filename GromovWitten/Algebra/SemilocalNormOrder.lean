/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.Algebra.NormOrder
import GromovWitten.Algebra.OrderBirational
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Ideal.Over

/-!
# The semilocal norm formula without freeness

Let `A` be a Noetherian local domain of Krull dimension `≤ 1` with fraction field `K`, and let `B`
be a domain, module-finite and faithful over `A` (no freeness assumption), with fraction field `L`
(compatibly with `K`). This file proves Stacks Project, Algebra, Lemma 10.121.8 /
Fulton's *Intersection Theory*, Proposition 1.4, in the form needed for the semilocal (not
necessarily local) target ring `B`: for `b : B` nonzero,

`Ring.ordFrac A (Algebra.norm K (algebraMap B L b))`

equals the order of vanishing of `Module.length A (B ⧸ (b))`
(`semilocal_length_quotient_span_eq_ordFrac_norm`), which in turn decomposes as the fibre sum

`∑ᶠ q : MaximalSpectrum B, [κ(q) : κ_A] · Ring.ord (Localization.AtPrime q.asIdeal)
    (algebraMap B _ b)`

(`semilocal_finsum_ord_eq_ordFrac_norm`), a genuinely finite sum since `MaximalSpectrum B` is
finite (`finite_maximalSpectrum_of_finite_over_local`).

The proof (Stacks 10.121.8's local case, Fulton A.2.6/A.3.1) chooses, via
`NormOrder.normOrd_exists_basis`, a finite free `A`-submodule `F ⊆ B` spanned by elements of `B`
forming a `K`-basis of `L`, together with `c ∈ A` nonzero with `c • B ⊆ F`. For `x ∈ B` with
`x • B ⊆ F`, the determinant of multiplication by `x` on `F` maps to `Algebra.norm K x` and its
order equals `Module.length A (B ⧸ (x))`
(`OrderDeterminant.length_quotient_range_eq_ord_det_of_injective`,
`NormOrder.normOrd_length_quotient_restrict`); applying this to `x = c` and `x = c * b` and
cancelling the common `c`-term (using the additivity `length (B ⧸ (uv)) = length (B ⧸ (v)) +
length (B ⧸ (u))`, proved via Mathlib's `Ideal.mulQuot`/`Ideal.quotOfMul` exact sequence) gives the
formula for `b`. The fibre-sum form follows from `OrderSemilocal.length_eq_finsum`.

## Main results

* `GromovWitten.Algebra.finite_maximalSpectrum_of_finite_over_local`: `MaximalSpectrum B` is
  finite when `B` is module-finite over a local ring `A`.
* `GromovWitten.Algebra.semilocal_length_ne_top`: `Module.length A (B ⧸ (b))` is finite for
  `b ≠ 0`.
* `GromovWitten.Algebra.semilocal_length_quotient_span_eq_ordFrac_norm`: the norm formula,
  `Ring.ordFrac A (Algebra.norm K (algebraMap B L b)) = Multiplicative.ofAdd
  ((Module.length A (B ⧸ (b))).toNat : ℤ)`.
* `GromovWitten.Algebra.semilocal_finsum_ord_eq_ordFrac_norm`: the fibre-sum form of the norm
  formula over `MaximalSpectrum B`.
* `GromovWitten.Algebra.semilocal_sum_ord_eq_ordFrac_norm`: the same, as a genuine `Finset.sum`
  once `Fintype (MaximalSpectrum B)` is supplied.
-/

open scoped Pointwise

namespace GromovWitten.Algebra

open Module IsLocalRing

section MaximalSpectrumFinite

variable {B : Type*} [CommRing B]

/-- **`B` is semilocal when it is module-finite over a local ring `A`.** Every maximal ideal of
`B` lies over the maximal ideal of `A` (integral extensions send maximal ideals to maximal
ideals under `comap`, and the only maximal ideal of local `A` is `maximalIdeal A`), so
`MaximalSpectrum B` embeds into the (finite, by quasi-finiteness of the module-finite algebra
`B`) set of primes of `B` lying over `maximalIdeal A`. The witness ring `A` is an explicit
argument (rather than inferred from a section `variable`) so that it remains available to the
proof even though it does not appear in the conclusion. -/
theorem finite_maximalSpectrum_of_finite_over_local (A : Type*) [CommRing A] [IsLocalRing A]
    [Algebra A B] [Module.Finite A B] : Finite (MaximalSpectrum B) := by
  have hfin : ((IsLocalRing.maximalIdeal A).primesOver B).Finite :=
    Algebra.QuasiFinite.finite_primesOver (IsLocalRing.maximalIdeal A)
  have hsub : Finite ((IsLocalRing.maximalIdeal A).primesOver B) := hfin.to_subtype
  have hlies : ∀ Q : MaximalSpectrum B, Q.asIdeal.LiesOver (IsLocalRing.maximalIdeal A) := by
    intro Q
    have := Q.isMaximal
    exact ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) Q.asIdeal)).symm⟩
  exact Finite.of_injective (fun Q : MaximalSpectrum B =>
    (⟨Q.asIdeal, Q.isMaximal.isPrime, hlies Q⟩ :
      (IsLocalRing.maximalIdeal A).primesOver B)) fun Q Q' hQQ =>
    MaximalSpectrum.ext (congrArg Subtype.val hQQ)

end MaximalSpectrumFinite

section SemilocalNormFormula

variable {A B : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  [IsLocalRing A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
  [FaithfulSMul A B]
  {K L : Type*} [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]

omit [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsLocalRing A]
  [Module.Finite A B] [FaithfulSMul A B] in
/-- **Length additivity for a product.** For `u, v : B` with `u ≠ 0`,
`Module.length A (B ⧸ (uv)) = Module.length A (B ⧸ (v)) + Module.length A (B ⧸ (u))`. Proved via
Mathlib's exact sequence `B ⧸ (v) →ₗ[B] B ⧸ (u • (v)) →ₗ[B] B ⧸ (u)` (multiplication by `u`,
then reduction mod `u`), restricted to `A`-linear maps, together with `u • Ideal.span {v} =
Ideal.span {u * v}`. -/
private theorem length_quotient_span_mul {u v : B} (hu : u ≠ 0) :
    Module.length A (B ⧸ (Ideal.span {u * v} : Ideal B)) =
      Module.length A (B ⧸ (Ideal.span {v} : Ideal B)) +
        Module.length A (B ⧸ (Ideal.span {u} : Ideal B)) := by
  have hunzd : u ∈ nonZeroDivisors B := mem_nonZeroDivisors_of_ne_zero hu
  have hspan : u • (Ideal.span {v} : Ideal B) = Ideal.span {u * v} := by
    rw [← Submodule.singleton_set_smul (Ideal.span {v}) u]
    simp [← Ideal.submodule_span_eq, Submodule.set_smul_span]
  have hinj : Function.Injective ((Ideal.mulQuot u (Ideal.span {v})).restrictScalars A) :=
    Ideal.mulQuot_injective (Ideal.span {v}) hunzd
  have hsurj : Function.Surjective ((Ideal.quotOfMul u (Ideal.span {v})).restrictScalars A) :=
    Ideal.quotOfMul_surjective (Ideal.span {v})
  have hex : Function.Exact ((Ideal.mulQuot u (Ideal.span {v})).restrictScalars A)
      ((Ideal.quotOfMul u (Ideal.span {v})).restrictScalars A) :=
    Ideal.exact_mulQuot_quotOfMul (Ideal.span {v})
  have hlen := Module.length_eq_add_of_exact _ _ hinj hsurj hex
  rwa [hspan] at hlen

omit [Module.Finite A B] [FaithfulSMul A B] [IsFractionRing B L] in
/-- **The key per-element formula.** For `n`, `f : Fin n → B` spanning a free `A`-lattice `F`
whose cokernel in `B` has finite `A`-length, and `x ≠ 0` in `B` with `x • B ⊆ F`, the norm of `x`
has `ordFrac` equal to `Multiplicative.ofAdd` of the (finite) `A`-length of `B ⧸ (x)`. This is
Stacks 10.121.8's local computation (Fulton A.2.6), stripped of the extra `IsLocalRing B`
bookkeeping present in `NormOrder.normOrd_ord_det`. -/
private theorem ordFrac_norm_eq_of_mem {n : ℕ} {f : Fin n → B} {vK : Basis (Fin n) K L}
    (hv : ∀ i, vK i = algebraMap B L (f i)) (hli : LinearIndependent A f)
    (hBF : Module.length A (B ⧸ Submodule.span A (Set.range f)) ≠ ⊤) {x : B} (hx0 : x ≠ 0)
    (hx : ∀ y, x * y ∈ Submodule.span A (Set.range f)) :
    Ring.ordFrac A (Algebra.norm K (algebraMap B L x)) =
      Multiplicative.ofAdd
        ((Module.length A (B ⧸ (Ideal.span {x} : Ideal B))).toNat : ℤ) ∧
      Module.length A (B ⧸ (Ideal.span {x} : Ideal B)) ≠ ⊤ := by
  classical
  set F := Submodule.span A (Set.range f) with hFdef
  let bF : Basis (Fin n) A F := Basis.span hli
  have : Module.Free A F := Module.Free.of_basis bF
  have : Module.Finite A F := Module.Finite.of_basis bF
  have hμ : Function.Injective (LinearMap.mulLeft A x) := mul_right_injective₀ hx0
  have hφ : Function.Injective ((LinearMap.mulLeft A x).restrict (p := F) (q := F)
      fun y _ => hx y) := fun a b h => Subtype.ext (hμ (congrArg Subtype.val h))
  have hdet0 : LinearMap.det ((LinearMap.mulLeft A x).restrict (p := F) (q := F)
      fun y _ => hx y) ≠ 0 := OrderDeterminant.det_ne_zero_of_injective hφ
  have hlen : Module.length A (B ⧸ (Ideal.span {x} : Ideal B)) =
      Ring.ord A (LinearMap.det ((LinearMap.mulLeft A x).restrict (p := F) (q := F)
        fun y _ => hx y)) := by
    rw [← OrderDeterminant.length_quotient_range_eq_ord_det_of_injective hφ,
      normOrd_length_quotient_restrict hμ hx hBF]
    have hrange : LinearMap.range (LinearMap.mulLeft A x) =
        (Ideal.span {x} : Ideal B).restrictScalars A := by
      ext z
      simp [Ideal.mem_span_singleton', mul_comm, eq_comm]
    rw [hrange, (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {x})).length_eq]
  have hnorm : algebraMap A K (LinearMap.det ((LinearMap.mulLeft A x).restrict (p := F) (q := F)
      fun y _ => hx y)) = Algebra.norm K (algebraMap B L x) := normOrd_algebraMap_det hv hli hx
  have hordtop : Ring.ord A (LinearMap.det ((LinearMap.mulLeft A x).restrict (p := F) (q := F)
      fun y _ => hx y)) ≠ ⊤ := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hdet0)
  refine ⟨?_, hlen ▸ hordtop⟩
  rw [← hnorm, Ring.ordFrac_eq_ord A hdet0,
    Ring.ordMonoidWithZeroHom_eq_coe A (mem_nonZeroDivisors_of_ne_zero hdet0)
      (ENat.natCast_toNat hordtop).symm, hlen]

/-- Auxiliary existence statement combining the norm formula and the finiteness of the length,
for the general (not necessarily lattice-adapted) nonzero `b : B`. Proved by evaluating
`ordFrac_norm_eq_of_mem` at `x = c'` and `x = c' * b` (where `c' = algebraMap A B c` is a
nonzero scalar with `c' • B ⊆ F`, from `NormOrder.normOrd_exists_basis`), and cancelling the
common `c'` contribution using multiplicativity of `Ring.ordFrac A ∘ Algebra.norm K` and the
length additivity `length (B ⧸ (c'b)) = length (B ⧸ (b)) + length (B ⧸ (c'))`. -/
private theorem exists_length_ordFrac_eq {b : B} (hb : b ≠ 0) :
    Module.length A (B ⧸ (Ideal.span {b} : Ideal B)) ≠ ⊤ ∧
    Ring.ordFrac A (Algebra.norm K (algebraMap B L b)) =
      Multiplicative.ofAdd
        ((Module.length A (B ⧸ (Ideal.span {b} : Ideal B))).toNat : ℤ) := by
  classical
  obtain ⟨n, f, vK, c, hv, hli, hc0, hc⟩ :=
    normOrd_exists_basis (A := A) (B := B) (K := K) (L := L)
  set F := Submodule.span A (Set.range f) with hFdef
  have hBF : Module.length A (B ⧸ F) ≠ ⊤ := by
    refine Module.length_ne_top_iff.2
      (OrderFiniteExtension.isFiniteLength_of_smul_eq_zero hc0 fun t => ?_)
    induction t using Submodule.Quotient.induction_on with | _ y => ?_
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hc y
  set c' := algebraMap A B c with hc'def
  have hc'0 : c' ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A B)).2 hc0
  have hc'mem : ∀ y, c' * y ∈ F := fun y => by rw [hc'def, ← Algebra.smul_def]; exact hc y
  have hcbmem : ∀ y, (c' * b) * y ∈ F := fun y => by
    rw [mul_assoc, hc'def, ← Algebra.smul_def]; exact hc _
  obtain ⟨hform_c', hlentop_c'⟩ := ordFrac_norm_eq_of_mem hv hli hBF hc'0 hc'mem
  obtain ⟨hform_cb, hlentop_cb⟩ :=
    ordFrac_norm_eq_of_mem hv hli hBF (mul_ne_zero hc'0 hb) hcbmem
  have hmuladd : Module.length A (B ⧸ (Ideal.span {c' * b} : Ideal B)) =
      Module.length A (B ⧸ (Ideal.span {b} : Ideal B)) +
        Module.length A (B ⧸ (Ideal.span {c'} : Ideal B)) :=
    length_quotient_span_mul hc'0
  have hbtop : Module.length A (B ⧸ (Ideal.span {b} : Ideal B)) ≠ ⊤ := by
    intro htop
    exact hlentop_cb (by rw [hmuladd, htop]; simp)
  refine ⟨hbtop, ?_⟩
  have htoNat : (Module.length A (B ⧸ (Ideal.span {c' * b} : Ideal B))).toNat =
      (Module.length A (B ⧸ (Ideal.span {b} : Ideal B))).toNat +
        (Module.length A (B ⧸ (Ideal.span {c'} : Ideal B))).toNat := by
    rw [hmuladd, ENat.toNat_add hbtop hlentop_c']
  have htoNatZ : ((Module.length A (B ⧸ (Ideal.span {c' * b} : Ideal B))).toNat : ℤ) =
      ((Module.length A (B ⧸ (Ideal.span {b} : Ideal B))).toNat : ℤ) +
        ((Module.length A (B ⧸ (Ideal.span {c'} : Ideal B))).toNat : ℤ) := by
    exact_mod_cast htoNat
  have hmul : Algebra.norm K (algebraMap B L (c' * b)) =
      Algebra.norm K (algebraMap B L c') * Algebra.norm K (algebraMap B L b) := by
    rw [map_mul (algebraMap B L), map_mul (Algebra.norm K)]
  have heqn1 : Multiplicative.ofAdd
        ((Module.length A (B ⧸ (Ideal.span {c' * b} : Ideal B))).toNat : ℤ) =
      Multiplicative.ofAdd ((Module.length A (B ⧸ (Ideal.span {c'} : Ideal B))).toNat : ℤ) *
        Ring.ordFrac A (Algebra.norm K (algebraMap B L b)) := by
    rw [← hform_cb, hmul, map_mul (Ring.ordFrac A), hform_c']
  have heqn2 : Multiplicative.ofAdd
        ((Module.length A (B ⧸ (Ideal.span {c' * b} : Ideal B))).toNat : ℤ) =
      Multiplicative.ofAdd ((Module.length A (B ⧸ (Ideal.span {c'} : Ideal B))).toNat : ℤ) *
        Multiplicative.ofAdd ((Module.length A (B ⧸ (Ideal.span {b} : Ideal B))).toNat : ℤ) := by
    rw [htoNatZ, add_comm, ofAdd_add]
  have hcancel : Multiplicative.ofAdd
        ((Module.length A (B ⧸ (Ideal.span {c'} : Ideal B))).toNat : ℤ) *
        Ring.ordFrac A (Algebra.norm K (algebraMap B L b)) =
      Multiplicative.ofAdd ((Module.length A (B ⧸ (Ideal.span {c'} : Ideal B))).toNat : ℤ) *
        Multiplicative.ofAdd ((Module.length A (B ⧸ (Ideal.span {b} : Ideal B))).toNat : ℤ) := by
    rw [← heqn1, heqn2, WithZero.coe_mul]
  exact mul_left_cancel₀ WithZero.exp_ne_zero hcancel

/-- `Module.length A (B ⧸ (b))` is finite for every nonzero `b : B`. The fraction fields `K`, `L`
are listed explicitly (rather than left to the ambient section `variable`s) so that they remain
available to the proof even though the conclusion itself does not mention them. -/
theorem semilocal_length_ne_top (K L : Type*) [Field K] [Field L] [Algebra A K]
    [IsFractionRing A K] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] {b : B} (hb : b ≠ 0) :
    Module.length A (B ⧸ (Ideal.span {b} : Ideal B)) ≠ ⊤ :=
  (exists_length_ordFrac_eq (K := K) (L := L) hb).1

/-- **The semilocal norm formula (Stacks 10.121.8, Fulton 1.4/A.2.6), without any freeness
hypothesis on `B`.** For `A` a Noetherian local domain of Krull dimension `≤ 1`, `B` a domain,
module-finite and faithful over `A`, and `b : B` nonzero,

`Ring.ordFrac A (Algebra.norm K (algebraMap B L b)) = Multiplicative.ofAdd
  ((Module.length A (B ⧸ (b))).toNat : ℤ)`,

i.e. `Module.length A (B ⧸ (b))` is (additively) the order of vanishing of the norm of `b`. -/
theorem semilocal_length_quotient_span_eq_ordFrac_norm {b : B} (hb : b ≠ 0) :
    Ring.ordFrac A (Algebra.norm K (algebraMap B L b)) =
      Multiplicative.ofAdd
        ((Module.length A (B ⧸ (Ideal.span {b} : Ideal B))).toNat : ℤ) :=
  (exists_length_ordFrac_eq hb).2

attribute [local instance] LocalizedModule.moduleOfIsLocalization

omit [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsDomain B] [FaithfulSMul A B] in
/-- The `q`-summand of `OrderSemilocal.summand` for the quotient `B ⧸ (x)` is `[κ(q):κ_A] ·
Ring.ord (B_q) x`. The two-line proof of `NormPushforward.summand_quotient_span_eq`, reproduced
here to avoid importing the (geometry-heavy) `NormPushforward.lean`. -/
private theorem summand_quotient_span_eq (q : MaximalSpectrum B) (x : B) :
    OrderSemilocal.summand (A := A) (B ⧸ (Ideal.span {x} : Ideal B)) q =
      (Module.finrank (ResidueField A) q.asIdeal.ResidueField : ℕ∞) *
        Ring.ord (Localization.AtPrime q.asIdeal)
          (algebraMap B (Localization.AtPrime q.asIdeal) x) := by
  unfold OrderSemilocal.summand
  congr 1
  exact (OrderBirational.localizedModule_quotient_span_equiv q.asIdeal x).length_eq

/-- **The fibre-sum form of the semilocal norm formula.** The `A`-length `Module.length A
(B ⧸ (b))` decomposes, via `OrderSemilocal.length_eq_finsum`, as the finite sum over
`MaximalSpectrum B` of the local contributions `[κ(q):κ_A] · Ring.ord (B_q) b`; combined with
`semilocal_length_quotient_span_eq_ordFrac_norm` this gives

`Ring.ordFrac A (Algebra.norm K (algebraMap B L b)) = Multiplicative.ofAdd
  ((∑ᶠ q : MaximalSpectrum B, [κ(q):κ_A] · Ring.ord (Localization.AtPrime q.asIdeal)
      (algebraMap B _ b)).toNat : ℤ)`. -/
theorem semilocal_finsum_ord_eq_ordFrac_norm {b : B} (hb : b ≠ 0) :
    Ring.ordFrac A (Algebra.norm K (algebraMap B L b)) =
      Multiplicative.ofAdd
        ((∑ᶠ q : MaximalSpectrum B,
            (Module.finrank (ResidueField A) q.asIdeal.ResidueField : ℕ∞) *
              Ring.ord (Localization.AtPrime q.asIdeal)
                (algebraMap B (Localization.AtPrime q.asIdeal) b)).toNat : ℤ) := by
  have hbtop : Module.length A (B ⧸ (Ideal.span {b} : Ideal B)) ≠ ⊤ :=
    semilocal_length_ne_top K L hb
  have hfin : IsFiniteLength B (B ⧸ (Ideal.span {b} : Ideal B)) :=
    OrderBirational.isFiniteLength_of_isFiniteLength_restrictScalars (A := A)
      (Ideal.span {b}) (Module.length_ne_top_iff.1 hbtop)
  have heq : Module.length A (B ⧸ (Ideal.span {b} : Ideal B)) =
      ∑ᶠ q : MaximalSpectrum B,
        (Module.finrank (ResidueField A) q.asIdeal.ResidueField : ℕ∞) *
          Ring.ord (Localization.AtPrime q.asIdeal)
            (algebraMap B (Localization.AtPrime q.asIdeal) b) := by
    rw [OrderSemilocal.length_eq_finsum hfin]
    exact finsum_congr fun q => summand_quotient_span_eq q b
  rw [semilocal_length_quotient_span_eq_ordFrac_norm hb, heq]

/-- The `Finset.sum` form of `semilocal_finsum_ord_eq_ordFrac_norm`, once a `Fintype` structure
on `MaximalSpectrum B` is supplied (e.g. `Fintype.ofFinite _`, using
`finite_maximalSpectrum_of_finite_over_local`). -/
theorem semilocal_sum_ord_eq_ordFrac_norm {b : B} (hb : b ≠ 0) [Fintype (MaximalSpectrum B)] :
    Ring.ordFrac A (Algebra.norm K (algebraMap B L b)) =
      Multiplicative.ofAdd
        ((∑ q : MaximalSpectrum B,
            (Module.finrank (ResidueField A) q.asIdeal.ResidueField : ℕ∞) *
              Ring.ord (Localization.AtPrime q.asIdeal)
                (algebraMap B (Localization.AtPrime q.asIdeal) b)).toNat : ℤ) := by
  rw [semilocal_finsum_ord_eq_ordFrac_norm hb, finsum_eq_sum_of_fintype]

/-- **Each local term is finite.** For `b ≠ 0` and every `q : MaximalSpectrum B`,
`Ring.ord (Localization.AtPrime q.asIdeal) (algebraMap B _ b) ≠ ⊤`. Proved by bounding the
`q`-summand of the (finite, by `semilocal_length_ne_top`) total sum
`∑ᶠ q, [κ(q):κ_A] · Ring.ord (B_q) b` from below by the single term at `q`
(`Finset.single_le_sum`), then cancelling the nonzero residue degree `[κ(q):κ_A]`. -/
theorem semilocal_ord_localization_ne_top (A : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsLocalRing A] [Algebra A B] [Module.Finite A B]
    [FaithfulSMul A B] (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [IsScalarTower A B L] {b : B} (hb : b ≠ 0) (q : MaximalSpectrum B) :
    Ring.ord (Localization.AtPrime q.asIdeal)
      (algebraMap B (Localization.AtPrime q.asIdeal) b) ≠ ⊤ := by
  classical
  have hfinite : Finite (MaximalSpectrum B) := finite_maximalSpectrum_of_finite_over_local A
  have : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  have hbtop : Module.length A (B ⧸ (Ideal.span {b} : Ideal B)) ≠ ⊤ :=
    semilocal_length_ne_top (A := A) K L hb
  have hfin : IsFiniteLength B (B ⧸ (Ideal.span {b} : Ideal B)) :=
    OrderBirational.isFiniteLength_of_isFiniteLength_restrictScalars (A := A)
      (Ideal.span {b}) (Module.length_ne_top_iff.1 hbtop)
  have heq : Module.length A (B ⧸ (Ideal.span {b} : Ideal B)) =
      ∑ᶠ q' : MaximalSpectrum B, (Module.finrank (ResidueField A) q'.asIdeal.ResidueField : ℕ∞) *
        Ring.ord (Localization.AtPrime q'.asIdeal)
          (algebraMap B (Localization.AtPrime q'.asIdeal) b) := by
    rw [OrderSemilocal.length_eq_finsum hfin]
    exact finsum_congr fun q' => summand_quotient_span_eq q' b
  rw [heq, finsum_eq_sum_of_fintype] at hbtop
  have hnonneg : ∀ q' ∈ (Finset.univ : Finset (MaximalSpectrum B)),
      (0 : ℕ∞) ≤ (Module.finrank (ResidueField A) q'.asIdeal.ResidueField : ℕ∞) *
        Ring.ord (Localization.AtPrime q'.asIdeal)
          (algebraMap B (Localization.AtPrime q'.asIdeal) b) :=
    fun _ _ => zero_le
  have hle : (Module.finrank (ResidueField A) q.asIdeal.ResidueField : ℕ∞) *
      Ring.ord (Localization.AtPrime q.asIdeal) (algebraMap B (Localization.AtPrime q.asIdeal) b) ≤
      ∑ q' : MaximalSpectrum B, (Module.finrank (ResidueField A) q'.asIdeal.ResidueField : ℕ∞) *
        Ring.ord (Localization.AtPrime q'.asIdeal)
          (algebraMap B (Localization.AtPrime q'.asIdeal) b) :=
    Finset.single_le_sum hnonneg (Finset.mem_univ q)
  have hterm_ne_top : (Module.finrank (ResidueField A) q.asIdeal.ResidueField : ℕ∞) *
      Ring.ord (Localization.AtPrime q.asIdeal)
        (algebraMap B (Localization.AtPrime q.asIdeal) b) ≠ ⊤ :=
    (lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hbtop)).ne
  intro htop
  refine hterm_ne_top ?_
  have hpos : (Module.finrank (ResidueField A) q.asIdeal.ResidueField : ℕ∞) ≠ 0 := by
    have : 0 < Module.finrank (ResidueField A) q.asIdeal.ResidueField :=
      (Module.finrank_pos_iff_of_free (ResidueField A) q.asIdeal.ResidueField).mpr inferInstance
    exact_mod_cast this.ne'
  rw [htop]
  exact ENat.mul_top hpos

/-- **The termwise-distributed integer form of the semilocal norm formula.** For `b ≠ 0` and
`Fintype (MaximalSpectrum B)`, each local term `Ring.ord (B_q) b` is finite
(`semilocal_ord_localization_ne_top`), so `.toNat` can be distributed into the sum of
`semilocal_sum_ord_eq_ordFrac_norm` termwise: the resulting integer

`∑ q : MaximalSpectrum B, [κ(q):κ_A] · (Ring.ord (B_q) b).toNat`

equals `Multiplicative.toAdd` of the norm's `ordFrac`, matching Fulton A.3.1 /
`NormPushforward.map_principalCycle_apply_toSpecPoint`'s integer bookkeeping. -/
theorem semilocal_sum_ord_toNat_eq_ordFrac_norm {b : B} (hb : b ≠ 0)
    [Fintype (MaximalSpectrum B)] :
    Multiplicative.ofAdd
        (∑ q : MaximalSpectrum B, (Module.finrank (ResidueField A) q.asIdeal.ResidueField : ℤ) *
            ((Ring.ord (Localization.AtPrime q.asIdeal)
                (algebraMap B (Localization.AtPrime q.asIdeal) b)).toNat : ℤ)) =
      Ring.ordFrac A (Algebra.norm K (algebraMap B L b)) := by
  classical
  have step1 : (∑ q : MaximalSpectrum B,
        (Module.finrank (ResidueField A) q.asIdeal.ResidueField : ℕ∞) *
          Ring.ord (Localization.AtPrime q.asIdeal)
            (algebraMap B (Localization.AtPrime q.asIdeal) b)) =
      ((∑ q : MaximalSpectrum B, (Module.finrank (ResidueField A) q.asIdeal.ResidueField) *
          (Ring.ord (Localization.AtPrime q.asIdeal)
            (algebraMap B (Localization.AtPrime q.asIdeal) b)).toNat : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Nat.cast_mul, ENat.natCast_toNat (semilocal_ord_localization_ne_top A K L hb q)]
  have hS : (∑ q : MaximalSpectrum B,
        (Module.finrank (ResidueField A) q.asIdeal.ResidueField : ℕ∞) *
          Ring.ord (Localization.AtPrime q.asIdeal)
            (algebraMap B (Localization.AtPrime q.asIdeal) b)).toNat =
      ∑ q : MaximalSpectrum B, (Module.finrank (ResidueField A) q.asIdeal.ResidueField) *
        (Ring.ord (Localization.AtPrime q.asIdeal)
          (algebraMap B (Localization.AtPrime q.asIdeal) b)).toNat := by
    rw [step1, ENat.toNat_natCast]
  have hZ : (∑ q : MaximalSpectrum B, (Module.finrank (ResidueField A) q.asIdeal.ResidueField : ℤ) *
        ((Ring.ord (Localization.AtPrime q.asIdeal)
            (algebraMap B (Localization.AtPrime q.asIdeal) b)).toNat : ℤ)) =
      ((∑ q : MaximalSpectrum B, (Module.finrank (ResidueField A) q.asIdeal.ResidueField) *
          (Ring.ord (Localization.AtPrime q.asIdeal)
            (algebraMap B (Localization.AtPrime q.asIdeal) b)).toNat : ℕ) : ℤ) := by
    push_cast
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hZ, semilocal_finsum_ord_eq_ordFrac_norm hb, finsum_eq_sum_of_fintype, hS]

/-- **The `WithZero.unzero` form** of `semilocal_sum_ord_toNat_eq_ordFrac_norm`: the same
integer sum equals `Multiplicative.toAdd` of the unit represented by the (nonzero, since
`Algebra.norm K` of a nonzero element along a map of domains is nonzero) norm's `ordFrac`. -/
theorem semilocal_sum_ord_toNat_eq_toAdd_ordFrac_norm {b : B} (hb : b ≠ 0)
    [Fintype (MaximalSpectrum B)]
    (h : Ring.ordFrac A (Algebra.norm K (algebraMap B L b)) ≠ 0) :
    (∑ q : MaximalSpectrum B, (Module.finrank (ResidueField A) q.asIdeal.ResidueField : ℤ) *
        ((Ring.ord (Localization.AtPrime q.asIdeal)
            (algebraMap B (Localization.AtPrime q.asIdeal) b)).toNat : ℤ)) =
      Multiplicative.toAdd (WithZero.unzero h) := by
  have hthis := semilocal_sum_ord_toNat_eq_ordFrac_norm (A := A) (K := K) (L := L) hb
  rw [← WithZero.coe_unzero h] at hthis
  exact WithZero.coe_injective hthis

end SemilocalNormFormula

end GromovWitten.Algebra
