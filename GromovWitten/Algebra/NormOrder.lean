/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.Algebra.OrderDeterminant
import GromovWitten.Algebra.OrderFiniteExtension
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Orders of norms along finite extensions of one-dimensional local domains

Let `A → B` be an injective, module-finite map of Noetherian local domains of Krull dimension
`≤ 1`, with fraction fields `K` and `L`. This file proves Stacks Project, Algebra,
Lemma 10.121.8 (local case): for `z ∈ Lˣ`,
`ordFrac_A (Norm_{L/K} z) = ordFrac_B z ^ [κ(B) : κ(A)]` in `ℤᵐ⁰`, i.e. additively
`ord_A (N z) = [κ(B) : κ(A)] · ord_B z`.

The proof follows Stacks: we choose a finite free `A`-submodule `F ⊆ B` spanned by elements of
`B` forming a `K`-basis of `L`, and a nonzero `c ∈ A` with `c B ⊆ F`. For `x ∈ B` with
`x B ⊆ F`, multiplication by `x` restricts to an endomorphism `φ_x` of `F` whose determinant maps
to `Norm_{L/K} x`, and `length_A (F / φ_x F) = length_A (B / x B)` because `B / F` has finite
length. Combined with Fulton's Lemma A.2.6 (`OrderDeterminant.length_quotient_range_eq_ord_det`)
and `length_A = [κ(B) : κ(A)] · length_B` this gives the formula for `x = c` and `x = c b`,
whence for `b`, and then for all of `Lˣ` by multiplicativity.

## Main results

* `GromovWitten.Algebra.length_quotient_span_eq_finrank_mul_ord`:
  `length_A (B ⧸ (x)) = [κ(B) : κ(A)] · ord_B x` for local `A → B`.
* `GromovWitten.Algebra.ordFrac_norm_algebraMap`: for `b : B`, `b ≠ 0`,
  `ordFrac A (Algebra.norm K (algebraMap B L b)) = ordFrac B (algebraMap B L b) ^ [κ(B) : κ(A)]`.
* `GromovWitten.Algebra.ordFrac_norm_of_ne_zero`: the same for any nonzero `z : L`.
* `GromovWitten.Algebra.ordFrac_norm_units`: the same for `z : Lˣ`.
-/

namespace GromovWitten.Algebra

open Module IsLocalRing

section Lengths

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- For submodules `P ≤ Q` of `M`, `length (M ⧸ P) = length (Q ⧸ P) + length (M ⧸ Q)`, where
`Q ⧸ P` is written as the quotient of `Q` by the pullback of `P`. -/
theorem normOrd_length_quotient_of_le {P Q : Submodule R M} (hPQ : P ≤ Q) :
    Module.length R (M ⧸ P) =
      Module.length R (Q ⧸ P.comap Q.subtype) + Module.length R (M ⧸ Q) := by
  let f : (Q ⧸ P.comap Q.subtype) →ₗ[R] M ⧸ P := (P.comap Q.subtype).mapQ P Q.subtype le_rfl
  let g : (M ⧸ P) →ₗ[R] M ⧸ Q := P.factor hPQ
  refine Module.length_eq_add_of_exact f g ?_ ?_ ?_
  · intro x y hxy
    induction x using Submodule.Quotient.induction_on with | _ x => ?_
    induction y using Submodule.Quotient.induction_on with | _ y => ?_
    simp only [f, Submodule.mapQ_apply, Submodule.Quotient.eq] at hxy ⊢
    simpa using hxy
  · intro z
    induction z using Submodule.Quotient.induction_on with | _ m => ?_
    exact ⟨Submodule.Quotient.mk m, rfl⟩
  · intro y
    induction y using Submodule.Quotient.induction_on with | _ m => ?_
    change (Submodule.Quotient.mk m : M ⧸ Q) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hm
      exact ⟨Submodule.Quotient.mk ⟨m, hm⟩, rfl⟩
    · rintro ⟨x, hx⟩
      induction x using Submodule.Quotient.induction_on with | _ x => ?_
      simp only [f, Submodule.mapQ_apply, Submodule.Quotient.eq] at hx
      have : m = (x : M) - ((x : M) - m) := by abel
      rw [this]
      exact Q.sub_mem x.2 (hPQ hx)

/-- If `μ` is an injective endomorphism of `M` with image inside a submodule `F` such that
`M ⧸ F` has finite length, then the cokernel of the restriction `F → F` of `μ` has the same
length as the cokernel of `μ`. -/
theorem normOrd_length_quotient_restrict {F : Submodule R M} {μ : M →ₗ[R] M}
    (hμ : Function.Injective μ) (hμF : ∀ y, μ y ∈ F) (hF : Module.length R (M ⧸ F) ≠ ⊤) :
    Module.length R (F ⧸ LinearMap.range (μ.restrict (p := F) (q := F) fun y _ => hμF y)) =
      Module.length R (M ⧸ LinearMap.range μ) := by
  set P : Submodule R M := F.map μ with hP
  have hPF : P ≤ F := Submodule.map_le_iff_le_comap.2 fun y _ => hμF y
  have hPR : P ≤ LinearMap.range μ := LinearMap.map_le_range
  have h1 := normOrd_length_quotient_of_le hPF
  have h2 := normOrd_length_quotient_of_le hPR
  have heq1 : LinearMap.range (μ.restrict (p := F) (q := F) fun y _ => hμF y) =
      P.comap F.subtype := by
    ext ⟨z, hz⟩
    simp [P]
  have heq2 : F.map (LinearEquiv.ofInjective μ hμ : M →ₗ[R] LinearMap.range μ) =
      P.comap (LinearMap.range μ).subtype := by
    ext ⟨z, hz⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_map, P]
    constructor
    · rintro ⟨w, hw, hwe⟩
      exact ⟨w, hw, congrArg Subtype.val hwe⟩
    · rintro ⟨w, hw, hwe⟩
      exact ⟨w, hw, Subtype.ext hwe⟩
  have e1 := (Submodule.quotEquivOfEq _ _ heq1).length_eq
  have e2 := (Submodule.Quotient.equiv F _ (LinearEquiv.ofInjective μ hμ) heq2).length_eq
  rw [e1]
  rw [h2, ← e2] at h1
  have hc := ENat.addLECancellable_of_ne_top hF
  rw [add_comm _ (Module.length R (M ⧸ F))] at h1
  exact le_antisymm (hc h1.ge) (hc h1.le)

end Lengths

/-- For a local homomorphism `A → B` of local rings with finite residue field extension and
`x : B`, `length_A (B ⧸ (x)) = [κ(B) : κ(A)] · ord_B x`. -/
theorem length_quotient_span_eq_finrank_mul_ord {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Module.Finite (ResidueField A) (ResidueField B)] (x : B) :
    Module.length A (B ⧸ (Ideal.span {x} : Ideal B)) =
      (Module.finrank (ResidueField A) (ResidueField B) : ℕ∞) * Ring.ord B x := by
  rw [IsLocalRing.length_restrictScalars A B, Module.length_eq_finrank, mul_comm]
  rfl

section Extension

variable {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
  [Module.Finite A B]
  {K L : Type*} [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]

omit [IsFractionRing A K] [Algebra K L] [IsScalarTower A K L] in
/-- Every element of `L = Frac B` becomes an element of `B` after multiplication by a nonzero
element of `A` (as `B` is integral over `A`). -/
theorem normOrd_exists_mul_mem (l : L) :
    ∃ e : A, e ≠ 0 ∧ ∃ y : B, algebraMap A L e * l = algebraMap B L y := by
  obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors B) l
  have hy0 : (y : B) ≠ 0 := nonZeroDivisors.ne_zero y.2
  have hne := Ideal.comap_ne_bot_of_integral_mem hy0 (Ideal.mem_span_singleton_self (y : B))
    (Algebra.IsIntegral.isIntegral (R := A) (y : B))
  obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at he
  obtain ⟨z, hz⟩ := he
  refine ⟨e, he0, z * x, ?_⟩
  rw [IsScalarTower.algebraMap_apply A B L, ← hz, map_mul, map_mul, mul_assoc,
    mul_comm (algebraMap B L (y : B)), IsLocalization.mk'_spec]

/-- There is a family `f : Fin n → B` which is a `K`-basis of `L`, together with a nonzero
`c ∈ A` such that `c B` lies in the `A`-span of `f`. -/
theorem normOrd_exists_basis :
    ∃ (n : ℕ) (f : Fin n → B) (vK : Basis (Fin n) K L) (c : A),
      (∀ i, vK i = algebraMap B L (f i)) ∧ LinearIndependent A f ∧ c ≠ 0 ∧
        ∀ y : B, c • y ∈ Submodule.span A (Set.range f) := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule A B).FG)
  set S : Set L := algebraMap B L '' (s : Set B) with hSdef
  have hinjK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hspan : Submodule.span K S = ⊤ := by
    refine eq_top_iff.2 fun l _ => ?_
    obtain ⟨e, he0, y, hy⟩ := normOrd_exists_mul_mem (A := A) (B := B) l
    have hyS : algebraMap B L y ∈ Submodule.span K S := by
      have hy' : y ∈ Submodule.span A (s : Set B) := hs ▸ Submodule.mem_top
      have h' := Submodule.mem_map_of_mem (f := (IsScalarTower.toAlgHom A B L).toLinearMap) hy'
      rw [Submodule.map_span] at h'
      exact Submodule.span_le_restrictScalars A K S h'
    have heK : algebraMap A K e ≠ 0 := (map_ne_zero_iff _ hinjK).2 he0
    have hl : l = (algebraMap A K e)⁻¹ • algebraMap B L y := by
      rw [Algebra.smul_def, ← hy, IsScalarTower.algebraMap_apply A K L, ← mul_assoc, map_inv₀,
        inv_mul_cancel₀ ((map_ne_zero _).2 heK), one_mul]
    rw [hl]
    exact Submodule.smul_mem _ _ hyS
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent K S
  have hbfin : b.Finite := (s.finite_toSet.image _).subset hbS
  have : Finite b := hbfin.to_subtype
  have : Fintype b := Fintype.ofFinite b
  let vK0 : Basis b K L := Basis.mk hbli (by rw [Subtype.range_coe, hbspan, hspan])
  choose f0 hf0s hf0 using fun i : b => hbS i.2
  let e := Fintype.equivFin b
  let vK := vK0.reindex e
  let f : Fin (Fintype.card b) → B := fun i => f0 (e.symm i)
  have hv : ∀ i, vK i = algebraMap B L (f i) := fun i => by
    simp [vK, f, vK0, hf0]
  have hliK : LinearIndependent K (algebraMap B L ∘ f) := by
    have : algebraMap B L ∘ f = vK := funext fun i => (hv i).symm
    rw [this]
    exact vK.linearIndependent
  have hliA : LinearIndependent A f :=
    (hliK.restrict_scalars' A).of_comp (IsScalarTower.toAlgHom A B L).toLinearMap
  set F : Submodule A B := Submodule.span A (Set.range f) with hF
  have hinjL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  have hlin : ∀ (a : A) (y : B), algebraMap B L (a • y) = a • algebraMap B L y := by
    intro a y
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
  have hper : ∀ y : B, ∃ q : A, q ≠ 0 ∧ q • y ∈ F := by
    intro y
    obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A)
      (fun i => vK.repr (algebraMap B L y) i)
    choose a ha using hq
    refine ⟨q, nonZeroDivisors.ne_zero q.2, ?_⟩
    have hsum : algebraMap B L ((q : A) • y) = algebraMap B L (∑ i, a i • f i) := by
      rw [hlin, map_sum, ← vK.sum_repr (algebraMap B L y), Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hlin, ← hv, ← algebraMap_smul K (a i) (vK i), ha i, smul_assoc]
    rw [hinjL hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  choose q hq0 hqF using hper
  refine ⟨_, f, vK, ∏ g ∈ s, q g, hv, hliA, Finset.prod_ne_zero_iff.2 fun g _ => hq0 g, ?_⟩
  have hcg : ∀ g ∈ s, (∏ g ∈ s, q g) • g ∈ F := fun g hg => by
    rw [← Finset.prod_erase_mul s q hg, mul_smul]
    exact F.smul_mem _ (hqF g)
  have hle : Submodule.span A (s : Set B) ≤ F.comap (LinearMap.lsmul A B (∏ g ∈ s, q g)) :=
    Submodule.span_le.2 fun g hg => hcg g hg
  intro y
  exact hle (hs ▸ Submodule.mem_top)

omit [IsDomain A] [IsDomain B] [Module.Finite A B] [IsFractionRing B L] [IsFractionRing A K]
  [Algebra K L] [IsScalarTower A K L] in
/-- `algebraMap B L` is `A`-linear. -/
theorem normOrd_algebraMap_smul (a : A) (y : B) :
    algebraMap B L (a • y) = a • algebraMap B L y := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]

omit [IsDomain A] [IsDomain B] [Module.Finite A B] [IsFractionRing B L] [IsFractionRing A K] in
/-- Let `f : Fin n → B` be `A`-linearly independent with image a `K`-basis `vK` of `L`, and let
`x ∈ B` with `x B ⊆ F := span_A f`. Then the determinant of multiplication by `x` on `F` maps to
`Norm_{L/K} x` in `K`. -/
theorem normOrd_algebraMap_det {n : ℕ} {f : Fin n → B} {vK : Basis (Fin n) K L}
    (hv : ∀ i, vK i = algebraMap B L (f i)) (hli : LinearIndependent A f) {x : B}
    (hx : ∀ y, x * y ∈ Submodule.span A (Set.range f)) :
    algebraMap A K (LinearMap.det ((LinearMap.mulLeft A x).restrict
      (p := Submodule.span A (Set.range f)) (q := Submodule.span A (Set.range f))
      fun y _ => hx y)) = Algebra.norm K (algebraMap B L x) := by
  classical
  set F := Submodule.span A (Set.range f)
  set φ : F →ₗ[A] F := (LinearMap.mulLeft A x).restrict (p := F) (q := F) fun y _ => hx y
  let bF : Basis (Fin n) A F := Basis.span hli
  rw [Algebra.norm_eq_matrix_det vK, ← LinearMap.det_toMatrix bF, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    LinearMap.toMatrix_apply]
  set r := bF.repr (φ (bF j))
  have hφ : ((φ (bF j) : F) : B) = x * f j := by
    change x * ((bF j : F) : B) = x * f j
    rw [Basis.span_apply]
  have h1 : x * f j = ∑ i, r i • f i := by
    have h := congrArg Subtype.val (bF.sum_repr (φ (bF j)))
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul] at h
    rw [← hφ, ← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    change r k • ((bF k : F) : B) = _
    rw [Basis.span_apply]
  have h2 : algebraMap B L x * vK j = vK.equivFun.symm (fun i => algebraMap A K (r i)) := by
    rw [Basis.equivFun_symm_apply, hv j, ← map_mul, h1, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hv, normOrd_algebraMap_smul, algebraMap_smul]
  rw [h2]
  change _ = vK.equivFun (vK.equivFun.symm (fun i => algebraMap A K (r i))) i
  rw [LinearEquiv.apply_symm_apply]

omit [IsFractionRing B L] [IsFractionRing A K] [Algebra K L] [IsScalarTower A K L] in
/-- For local `A → B` (injective and finite), `x ∈ B` nonzero with `x B ⊆ F := span_A f` where
`f` is `A`-linearly independent and `B ⧸ F` has finite length, the order of the determinant of
multiplication by `x` on `F` is `ord_B x · [κ(B) : κ(A)]`. -/
theorem normOrd_ord_det [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsLocalRing A]
    [IsLocalRing B] [FaithfulSMul A B] {n : ℕ} {f : Fin n → B} (hli : LinearIndependent A f)
    (hBF : Module.length A (B ⧸ Submodule.span A (Set.range f)) ≠ ⊤) {x : B} (hx0 : x ≠ 0)
    (hx : ∀ y, x * y ∈ Submodule.span A (Set.range f)) :
    Ring.ord A (LinearMap.det ((LinearMap.mulLeft A x).restrict
      (p := Submodule.span A (Set.range f)) (q := Submodule.span A (Set.range f))
      fun y _ => hx y)) =
      Ring.ord B x * (Module.finrank (ResidueField A) (ResidueField B) : ℕ∞) := by
  classical
  set F := Submodule.span A (Set.range f)
  let bF : Basis (Fin n) A F := Basis.span hli
  have : Module.Free A F := Module.Free.of_basis bF
  have : Module.Finite A F := Module.Finite.of_basis bF
  have hμ : Function.Injective (LinearMap.mulLeft A x) := mul_right_injective₀ hx0
  have hφ : Function.Injective ((LinearMap.mulLeft A x).restrict (p := F) (q := F)
      fun y _ => hx y) := fun a b h => Subtype.ext (hμ (congrArg Subtype.val h))
  rw [← OrderDeterminant.length_quotient_range_eq_ord_det_of_injective hφ,
    normOrd_length_quotient_restrict hμ hx hBF]
  have hrange : LinearMap.range (LinearMap.mulLeft A x) =
      (Ideal.span {x} : Ideal B).restrictScalars A := by
    ext z
    simp [Ideal.mem_span_singleton', mul_comm, eq_comm]
  rw [hrange, (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {x})).length_eq,
    IsLocalRing.length_restrictScalars A B, Module.length_eq_finrank]
  rfl

omit [Algebra A B] [Module.Finite A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [IsScalarTower A B L] in
/-- Translation of `ord_A d = ord_B x · m` into the multiplicative `ordFrac` language. -/
theorem normOrd_ordFrac_of_ord_eq [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsNoetherianRing B]
    [Ring.KrullDimLE 1 B] {d : A} (hd : d ≠ 0) {x : B} (hx : x ≠ 0) {m : ℕ}
    (h : Ring.ord A d = Ring.ord B x * (m : ℕ∞)) :
    Ring.ordFrac A (algebraMap A K d) = Ring.ordFrac B (algebraMap B L x) ^ m := by
  have := (IsFractionRing.injective B L).isDomain
  rw [Ring.ordFrac_eq_ord A hd, Ring.ordFrac_eq_ord B hx]
  obtain ⟨k, hk⟩ :=
    ENat.ne_top_iff_exists.mp (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hx))
  rw [← hk, ← Nat.cast_mul] at h
  rw [Ring.ordMonoidWithZeroHom_eq_coe A (mem_nonZeroDivisors_of_ne_zero hd) h,
    Ring.ordMonoidWithZeroHom_eq_coe B (mem_nonZeroDivisors_of_ne_zero hx) hk.symm,
    ← WithZero.coe_pow, ← ofAdd_nsmul]
  push_cast
  rw [nsmul_eq_mul, mul_comm]

/-- **Stacks, Algebra, Lemma 10.121.8** (local case, elements of `B`). Let `A → B` be an
injective module-finite map of Noetherian local domains of Krull dimension `≤ 1`, with fraction
fields `K`, `L`. For `b : B`, `b ≠ 0`,
`ordFrac_A (Norm_{L/K} b) = ordFrac_B b ^ [κ(B) : κ(A)]`. -/
theorem ordFrac_norm_algebraMap [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsLocalRing A]
    [IsNoetherianRing B] [Ring.KrullDimLE 1 B] [IsLocalRing B] [FaithfulSMul A B]
    {b : B} (hb : b ≠ 0) :
    Ring.ordFrac A (Algebra.norm K (algebraMap B L b)) =
      Ring.ordFrac B (algebraMap B L b) ^ Module.finrank (ResidueField A) (ResidueField B) := by
  obtain ⟨n, f, vK, c, hv, hli, hc0, hc⟩ := normOrd_exists_basis (A := A) (B := B) (K := K) (L := L)
  set F := Submodule.span A (Set.range f)
  have hinjL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  have hBF : Module.length A (B ⧸ F) ≠ ⊤ := by
    refine Module.length_ne_top_iff.2
      (OrderFiniteExtension.isFiniteLength_of_smul_eq_zero hc0 fun t => ?_)
    induction t using Submodule.Quotient.induction_on with | _ y => ?_
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hc y
  have key : ∀ x : B, x ≠ 0 → (∀ y, x * y ∈ F) →
      Ring.ordFrac A (Algebra.norm K (algebraMap B L x)) =
        Ring.ordFrac B (algebraMap B L x) ^ Module.finrank (ResidueField A) (ResidueField B) := by
    intro x hx0 hx
    have hdet := normOrd_algebraMap_det hv hli hx
    have hdet0 : LinearMap.det ((LinearMap.mulLeft A x).restrict (p := F) (q := F)
        fun y _ => hx y) ≠ 0 := by
      intro h
      rw [h, map_zero] at hdet
      exact (Algebra.norm_ne_zero_iff_of_basis vK).2 ((map_ne_zero_iff _ hinjL).2 hx0) hdet.symm
    rw [← hdet]
    exact normOrd_ordFrac_of_ord_eq hdet0 hx0 (normOrd_ord_det hli hBF hx0 hx)
  set c' := algebraMap A B c
  have hc'0 : c' ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A B)).2 hc0
  have h1 := key c' hc'0 fun y => by rw [← Algebra.smul_def]; exact hc y
  have h2 := key (c' * b) (mul_ne_zero hc'0 hb) fun y => by
    rw [mul_assoc, ← Algebra.smul_def]; exact hc _
  rw [map_mul, map_mul, map_mul, map_mul, mul_pow, h1] at h2
  have hne : Ring.ordFrac B (algebraMap B L c') ^
      Module.finrank (ResidueField A) (ResidueField B) ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero _).2 ((map_ne_zero_iff _ hinjL).2 hc'0))
  exact mul_left_cancel₀ hne h2

/-- **Stacks, Algebra, Lemma 10.121.8** (local case). Let `A → B` be an injective module-finite
map of Noetherian local domains of Krull dimension `≤ 1`, with fraction fields `K`, `L`. For
every nonzero `z : L`, `ordFrac_A (Norm_{L/K} z) = ordFrac_B z ^ [κ(B) : κ(A)]`. -/
theorem ordFrac_norm_of_ne_zero [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsLocalRing A]
    [IsNoetherianRing B] [Ring.KrullDimLE 1 B] [IsLocalRing B] [FaithfulSMul A B]
    {z : L} (hz : z ≠ 0) :
    Ring.ordFrac A (Algebra.norm K z) =
      Ring.ordFrac B z ^ Module.finrank (ResidueField A) (ResidueField B) := by
  obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors B) z
  have hinjL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  have hy : (y : B) ≠ 0 := nonZeroDivisors.ne_zero y.2
  have hx : x ≠ 0 := by
    rintro rfl
    exact hz (IsLocalization.mk'_zero _)
  have hmk : IsLocalization.mk' L x y * algebraMap B L y = algebraMap B L x :=
    IsLocalization.mk'_spec L x y
  have hA := congrArg (fun w => Ring.ordFrac A (Algebra.norm K w)) hmk
  simp only [map_mul] at hA
  rw [ordFrac_norm_algebraMap hx, ordFrac_norm_algebraMap hy] at hA
  have hB : Ring.ordFrac B (IsLocalization.mk' L x y) * Ring.ordFrac B (algebraMap B L y) =
      Ring.ordFrac B (algebraMap B L x) := by rw [← map_mul, hmk]
  rw [← hB, mul_pow] at hA
  exact mul_right_cancel₀ (pow_ne_zero _ ((map_ne_zero _).2 ((map_ne_zero_iff _ hinjL).2 hy))) hA

/-- **Stacks, Algebra, Lemma 10.121.8** (local case, units of `L`): for `z : Lˣ`,
`ordFrac_A (Norm_{L/K} z) = ordFrac_B z ^ [κ(B) : κ(A)]`. -/
theorem ordFrac_norm_units [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsLocalRing A]
    [IsNoetherianRing B] [Ring.KrullDimLE 1 B] [IsLocalRing B] [FaithfulSMul A B] (z : Lˣ) :
    Ring.ordFrac A (Algebra.norm K (z : L)) =
      Ring.ordFrac B (z : L) ^ Module.finrank (ResidueField A) (ResidueField B) :=
  ordFrac_norm_of_ne_zero z.ne_zero

end Extension

end GromovWitten.Algebra
