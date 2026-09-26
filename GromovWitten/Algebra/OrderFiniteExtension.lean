/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 5
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.LocalOrdSymmetry
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.Regular.Category
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.FiniteLength
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The order of vanishing and the length-Euler-characteristic on finite free modules

This file develops a small piece of Fulton's Appendix A.2 (*Intersection Theory*): the additive
"Euler characteristic" `chiKer a M`/`chiCoker a M` of a scalar `a` acting on a module `M`, already
introduced in `GromovWitten.AlgebraicGeometry.IntersectionTheory.LocalOrdSymmetry`, agrees on
modules of finite length (`chiKer_eq_chiCoker_of_lengthNeTop`), and on a finite free module `M`
with basis indexed by a finite type `ι`, `chiCoker a M` (i.e. `Module.length A (M ⧸ a • M)`)
equals `(Fintype.card ι) * Ring.ord A a` (`chiCoker_pi`, `chiCoker_of_free`).

For a finitely generated torsion-free module `M` of `A`-rank `r` over a Noetherian local domain
`A` of Krull dimension one, Fulton's Lemma A.2.3 asserts
`Module.length A (M ⧸ a • M) = r * Ring.ord A a`; this file records the free-module case of that
statement (`length_quotient_smul_eq_of_free`, `length_quotient_smulTop_eq_of_free`), which is the
key computational input used to build the general statement, but does **not** establish the
existence, for a general finitely generated torsion-free `M`, of an embedding of a finite free
module into `M` with a cokernel of finite length -- this is the remaining gap towards Fulton
A.2.3 in full generality (see the final report for the precise obstruction).

## Main declarations

* `OrderFiniteExtension.chiKer_eq_chiCoker_of_lengthNeTop`: for any module `T` of finite length,
  `chiKer a T = chiCoker a T` (Fulton: the Euler characteristic of `a` vanishes on finite-length
  modules).
* `OrderFiniteExtension.chiCoker_pi`: `chiCoker a (ι → A) = (Fintype.card ι) * Ring.ord A a`.
* `OrderFiniteExtension.chiKer_pi_eq_zero`: on a domain `A`, for `a ≠ 0`, `chiKer a (ι → A) = 0`.
* `OrderFiniteExtension.chiCoker_of_free`, `OrderFiniteExtension.chiKer_of_free`: the same two
  facts transported along a basis to an arbitrary finite free module.
* `OrderFiniteExtension.length_quotient_smul_eq_of_free`,
  `OrderFiniteExtension.length_quotient_smulTop_eq_of_free`: for `M` finite free of rank
  `Fintype.card ι`, `Module.length A (M ⧸ a • M) = (Fintype.card ι) * Ring.ord A a`, stated with
  the quotient by `LinearMap.range (LinearMap.lsmul A M a)` and by the pointwise submodule
  `a • (⊤ : Submodule A M)` respectively (`range_lsmul_eq_smul_top` relates the two).
-/

open GromovWitten.AlgebraicGeometry.IntersectionTheory
open scoped Pointwise

namespace OrderFiniteExtension

section FiniteLength

variable {A : Type*} [CommRing A] {T : Type*} [AddCommGroup T] [Module A T]

/-- On a module of finite length, the "kernel" and "cokernel" Euler-characteristic pieces of
multiplication by `a` agree: `Module.length A (ker (a • ·)) = Module.length A (T ⧸ a • T)`.
This is Fulton's remark (Appendix A.2) that the Euler characteristic `chiCoker - chiKer` vanishes
on finite-length modules, stated additively (without subtraction in `ℕ∞`). -/
theorem chiKer_eq_chiCoker_of_lengthNeTop (a : A) (h : Module.length A T ≠ ⊤) :
    LocalOrdSymmetry.chiKer a T = LocalOrdSymmetry.chiCoker a T := by
  set φ := LinearMap.lsmul A T a with hφ
  have h1 : Module.length A T
      = LocalOrdSymmetry.chiKer a T + Module.length A (LinearMap.range φ) :=
    LocalOrdSymmetry.length_eq_ker_add_range φ
  have h2 : Module.length A T
      = Module.length A (LinearMap.range φ) + LocalOrdSymmetry.chiCoker a T :=
    Module.length_eq_add_of_exact (LinearMap.range φ).subtype (LinearMap.range φ).mkQ
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
      (LinearMap.exact_subtype_mkQ _)
  have hlt : Module.length A (LinearMap.range φ) ≠ ⊤ :=
    fun htop ↦ h (by rw [h1, htop, add_top])
  have heq := h1.symm.trans h2
  rw [add_comm (Module.length A (LinearMap.range φ))] at heq
  exact LocalOrdSymmetry.enat_add_right_cancel hlt heq

end FiniteLength

section FreeModules

variable {A : Type*} [CommRing A]

/-- The range of scalar multiplication by `a` on a finite power `ι → A` of `A` is the product of
the principal ideals `Ideal.span {a}`. -/
theorem range_lsmul_pi {ι : Type*} (a : A) :
    LinearMap.range (LinearMap.lsmul A (ι → A) a)
      = Submodule.pi Set.univ (fun _ : ι ↦ (Ideal.span {a} : Submodule A A)) := by
  classical
  ext f
  simp only [LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, forall_true_left,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨g, rfl⟩ i
    refine ⟨g i, ?_⟩
    simp only [LinearMap.lsmul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · intro h
    choose g hg using h
    refine ⟨g, funext fun i ↦ ?_⟩
    simp only [LinearMap.lsmul_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]
    exact hg i

/-- `chiCoker` of scalar multiplication by `a` on a finite power `ι → A` equals `Fintype.card ι`
copies of `Ring.ord A a`; this is the "`A^r ⧸ a A^r ≅ (A ⧸ aA)^r`" computation behind Fulton's
Lemma A.2.3 on a free module. -/
theorem chiCoker_pi {ι : Type*} [Fintype ι] (a : A) :
    LocalOrdSymmetry.chiCoker a (ι → A) = (Fintype.card ι : ℕ∞) * Ring.ord A a := by
  classical
  have hrange := range_lsmul_pi (A := A) (ι := ι) a
  have hequiv : ((ι → A) ⧸ LinearMap.range (LinearMap.lsmul A (ι → A) a))
      ≃ₗ[A] (ι → (A ⧸ Ideal.span {a})) := by
    rw [hrange]
    exact Submodule.quotientPi (fun _ : ι ↦ (Ideal.span {a} : Submodule A A))
  rw [LocalOrdSymmetry.chiCoker, LinearEquiv.length_eq hequiv, Module.length_pi_of_fintype,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rfl

/-- On a domain, scalar multiplication by a nonzero `a` is injective on any finite power `ι → A`,
so the "kernel" Euler-characteristic piece `chiKer` vanishes. -/
theorem chiKer_pi_eq_zero [IsDomain A] {ι : Type*} {a : A} (ha : a ≠ 0) :
    LocalOrdSymmetry.chiKer a (ι → A) = 0 := by
  have hinj : Function.Injective (LinearMap.lsmul A (ι → A) a) := by
    intro f g h
    funext i
    have := congrFun h i
    simp only [LinearMap.lsmul_apply] at this
    exact (smul_right_injective A ha) this
  rw [LocalOrdSymmetry.chiKer, LinearMap.ker_eq_bot.2 hinj]
  exact Module.length_eq_zero

/-- `chiCoker` of scalar multiplication by `a` on a finite free module `M` (with basis indexed by
a finite type `ι`) equals `Fintype.card ι` copies of `Ring.ord A a`. -/
theorem chiCoker_of_free {M : Type*} [AddCommGroup M] [Module A M] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι A M) (a : A) :
    LocalOrdSymmetry.chiCoker a M = (Fintype.card ι : ℕ∞) * Ring.ord A a := by
  rw [LocalOrdSymmetry.chiCoker_congr a b.equivFun]
  exact chiCoker_pi a

/-- On a domain, `chiKer` of scalar multiplication by a nonzero `a` vanishes on a finite free
module. -/
theorem chiKer_of_free [IsDomain A] {M : Type*} [AddCommGroup M] [Module A M] {ι : Type*}
    [Finite ι] (b : Module.Basis ι A M) {a : A} (ha : a ≠ 0) :
    LocalOrdSymmetry.chiKer a M = 0 := by
  rw [LocalOrdSymmetry.chiKer_congr a b.equivFun]
  exact chiKer_pi_eq_zero ha

/-- **Fulton, Appendix A.2.3 (free case).** For `M` a finite free `A`-module of rank
`Fintype.card ι`, the length of `M ⧸ a • M` is `Fintype.card ι` copies of the order of vanishing
`Ring.ord A a`. -/
theorem length_quotient_smul_eq_of_free {M : Type*} [AddCommGroup M] [Module A M]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι A M) (a : A) :
    Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M a))
      = (Fintype.card ι : ℕ∞) * Ring.ord A a :=
  chiCoker_of_free b a

/-- The range of scalar multiplication by `a` on `M` is the pointwise submodule `a • ⊤`, i.e.
`a • M` in the usual (Fulton-style) notation for the submodule of multiples of `a`. -/
theorem range_lsmul_eq_smul_top {M : Type*} [AddCommGroup M] [Module A M] (a : A) :
    LinearMap.range (LinearMap.lsmul A M a) = a • (⊤ : Submodule A M) := by
  have h := LinearMap.exact_lsmul_mkQ_smul_top M a
  rw [LinearMap.exact_iff, Submodule.ker_mkQ] at h
  first
  | exact h
  | exact h.symm

/-- **Fulton, Appendix A.2.3 (free case), restated with the submodule `a • M`.** For `M` a finite
free `A`-module of rank `Fintype.card ι`, the length of `M ⧸ a • M` is `Fintype.card ι` copies of
the order of vanishing `Ring.ord A a`. -/
theorem length_quotient_smulTop_eq_of_free {M : Type*} [AddCommGroup M] [Module A M]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι A M) (a : A) :
    Module.length A (M ⧸ a • (⊤ : Submodule A M)) = (Fintype.card ι : ℕ∞) * Ring.ord A a := by
  rw [← range_lsmul_eq_smul_top]
  exact length_quotient_smul_eq_of_free b a

end FreeModules

section TorsionFree

open scoped TensorProduct

variable {A : Type*} [CommRing A] [IsDomain A]

/-- The canonical `A`-linear map `M → FractionRing A ⊗[A] M`, `m ↦ 1 ⊗ m`, realising the base
change of `M` to the fraction field of `A`. -/
noncomputable def toFrac (M : Type*) [AddCommGroup M] [Module A M] :
    M →ₗ[A] FractionRing A ⊗[A] M :=
  TensorProduct.mk A (FractionRing A) M 1

instance isLocalizedModule_toFrac (M : Type*) [AddCommGroup M] [Module A M] :
    IsLocalizedModule (nonZeroDivisors A) (toFrac (A := A) M) :=
  IsLocalization.tensorProduct_isLocalizedModule (nonZeroDivisors A) (FractionRing A)

/-- `toFrac` is injective on a torsion-free module. -/
theorem toFrac_injective {M : Type*} [AddCommGroup M] [Module A M] [NoZeroSMulDivisors A M] :
    Function.Injective (toFrac (A := A) M) := by
  rw [IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors A) (toFrac (A := A) M)]
  intro c
  exact smul_right_injective M (mem_nonZeroDivisors_iff_ne_zero.mp c.2)

omit [IsDomain A] in
/-- The image of `M` spans `FractionRing A ⊗[A] M` over the fraction field. -/
theorem span_range_toFrac_eq_top {M : Type*} [AddCommGroup M] [Module A M] :
    Submodule.span (FractionRing A) (Set.range (toFrac (A := A) M)) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  induction x with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul k m =>
    have hkm : k ⊗ₜ[A] m = k • toFrac (A := A) M m := by
      simp [toFrac, TensorProduct.smul_tmul']
    rw [hkm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

/-- A finitely generated module over a Noetherian domain of Krull dimension `≤ 1`, on which a
fixed nonzero scalar `c` acts as zero, has finite length. This is the "torsion part" input to
Fulton's Lemma A.2.3. -/
theorem isFiniteLength_of_smul_eq_zero [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    {T : Type*} [AddCommGroup T] [Module A T] [Module.Finite A T] {c : A} (hc : c ≠ 0)
    (hcT : ∀ t : T, c • t = 0) : IsFiniteLength A T := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule A T).FG)
  set π : (s → A) →ₗ[A] T :=
    { toFun := fun g => ∑ i : s, g i • (i : T)
      map_add' := fun g g' => by simp [Finset.sum_add_distrib, add_smul]
      map_smul' := fun a g => by simp [Finset.smul_sum, smul_smul] } with hπdef
  have hsurj : Function.Surjective π := by
    have hle : Submodule.span A (s : Set T) ≤ LinearMap.range π := by
      refine Submodule.span_le.mpr ?_
      rintro x hx
      refine LinearMap.mem_range.mpr
        ⟨fun i => if i = (⟨x, hx⟩ : s) then (1 : A) else 0, ?_⟩
      change ∑ i : s, (if i = (⟨x, hx⟩ : s) then (1 : A) else 0) • (i : T) = x
      rw [Fintype.sum_eq_single (⟨x, hx⟩ : s) (fun i hi => by simp [hi])]
      simp
    rw [hs] at hle
    exact LinearMap.range_eq_top.mp (top_le_iff.mp hle)
  have hker : LinearMap.range (LinearMap.lsmul A (s → A) c) ≤ LinearMap.ker π := by
    rintro x ⟨g, rfl⟩
    have hcomm : π (c • g) = c • π g := π.map_smul c g
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply, hcomm, hcT]
  set π' := (LinearMap.range (LinearMap.lsmul A (s → A) c)).liftQ π hker with hπ'def
  have hsurj' : Function.Surjective π' := by
    intro t
    obtain ⟨g, rfl⟩ := hsurj t
    exact ⟨Submodule.Quotient.mk g, Submodule.liftQ_apply _ π _⟩
  have hcs : c ∈ nonZeroDivisors A := mem_nonZeroDivisors_iff_ne_zero.mpr hc
  have hlen_ne_top :
      Module.length A ((s → A) ⧸ LinearMap.range (LinearMap.lsmul A (s → A) c)) ≠ ⊤ := by
    have heq : LocalOrdSymmetry.chiCoker c (s → A) = (Fintype.card s : ℕ∞) * Ring.ord A c :=
      chiCoker_pi c
    rw [LocalOrdSymmetry.chiCoker] at heq
    rw [heq]
    exact WithTop.mul_ne_top (ENat.natCast_ne_top _) (Ring.ord_ne_top hcs)
  have hfl : IsFiniteLength A ((s → A) ⧸ LinearMap.range (LinearMap.lsmul A (s → A) c)) :=
    Module.length_ne_top_iff.mp hlen_ne_top
  exact hfl.of_surjective hsurj'

/-- **Fulton, Appendix A.2.3 (existence of the free submodule).** A finitely generated
torsion-free module `M` over a Noetherian domain `A` of Krull dimension `≤ 1` contains a finite
free submodule `N`, spanned by an `A`-linearly independent family `f` indexed by a finite type
`ι` whose image is `A`-linearly independent, such that `M ⧸ N` has finite length. Moreover `ι`
has the same cardinality as a basis of `FractionRing A ⊗[A] M`, i.e. `f` realises a maximal
`A`-linearly independent subset of `M`. -/
theorem exists_free_submodule_finiteLength_quotient [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] [NoZeroSMulDivisors A M] :
    ∃ (n : ℕ) (f : Fin n → M), LinearIndependent A f ∧
      Module.length A (M ⧸ Submodule.span A (Set.range f)) ≠ ⊤ := by
  classical
  set K := FractionRing A
  set V := K ⊗[A] M
  -- Step 1: a `K`-linearly independent subset `b` of the image of `M`, spanning `V`.
  obtain ⟨b, hb_sub, hb_span, hb_li⟩ :=
    exists_linearIndependent K (Set.range (toFrac (A := A) M))
  have hspan_top : Submodule.span K (Set.range (Subtype.val : b → V)) = ⊤ := by
    rw [Subtype.range_coe, hb_span, span_range_toFrac_eq_top]
  -- Step 2: `b` is finite, since `V` is a finite-dimensional `K`-vector space.
  have hVfin : Module.Finite K V := inferInstance
  obtain ⟨w, hw⟩ := (Module.Finite.fg_top : (⊤ : Submodule K V).FG)
  have hbfinite : Finite b :=
    hb_li.finite_of_le_span_finite (Subtype.val : b → V) (w : Set V)
      (by rw [Subtype.range_coe, hw]; exact le_top)
  have : Fintype b := Fintype.ofFinite b
  -- Step 3: pull `b` back to a family `f : b → M` with `toFrac ∘ f = Subtype.val`.
  have hpre : ∀ i : b, ∃ m : M, toFrac (A := A) M m = (i : V) := fun i => hb_sub i.2
  choose f hf using hpre
  have htf : toFrac (A := A) M ∘ f = (Subtype.val : b → V) := funext hf
  have hli_toFrac : LinearIndependent K (toFrac (A := A) M ∘ f) := by
    rw [htf]; exact hb_li
  have hli_A : LinearIndependent A f :=
    (hli_toFrac.restrict_scalars' A).of_comp (toFrac (A := A) M)
  set N : Submodule A M := Submodule.span A (Set.range f)
  -- Step 4: `M ⧸ N` is torsion: every `x : M` has `(q : A) • x ∈ N` for some `q ≠ 0`, obtained
  -- by clearing denominators of the coordinates of `toFrac x` in the spanning family `b`.
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule A M).FG)
  have htorsion : ∀ x : M, ∃ q : nonZeroDivisors A, (q : A) • x ∈ N := by
    intro x
    obtain ⟨k, hk⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp
      (hspan_top ▸ Submodule.mem_top : toFrac (A := A) M x ∈
        Submodule.span K (Set.range (Subtype.val : b → V)))
    obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) k
    choose a ha using hq
    refine ⟨q, ?_⟩
    have hV : (q : A) • toFrac (A := A) M x = ∑ i : b, (a i) • toFrac (A := A) M (f i) := by
      rw [← hk, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hf i, ← smul_assoc, ← ha i, algebraMap_smul]
    have hmem : ∑ i : b, (a i) • f i ∈ N :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have heq : toFrac (A := A) M ((q : A) • x) = toFrac (A := A) M (∑ i : b, (a i) • f i) := by
      rw [(toFrac (A := A) M).map_smul, hV, map_sum (toFrac (A := A) M)]
      exact Finset.sum_congr rfl fun i _ => by rw [(toFrac (A := A) M).map_smul]
    rw [toFrac_injective (A := A) (M := M) heq]
    exact hmem
  choose qg hqg using fun g : s => htorsion (g : M)
  set c : A := ∏ g : s, (qg g : A) with hcdef
  have hc_ne : c ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun g _ => mem_nonZeroDivisors_iff_ne_zero.mp (qg g).2
  have hc_mem : ∀ g : s, c • (g : M) ∈ N := by
    intro g
    have hfactor : c = (∏ h ∈ Finset.univ.erase g, (qg h : A)) * (qg g : A) := by
      rw [hcdef]
      exact (Finset.prod_erase_mul Finset.univ (fun h => (qg h : A)) (Finset.mem_univ g)).symm
    rw [hfactor, mul_smul]
    exact Submodule.smul_mem _ _ (hqg g)
  have hMc : ∀ x : M, c • x ∈ N := by
    have hle : (⊤ : Submodule A M) ≤ Submodule.comap (LinearMap.lsmul A M c) N := by
      rw [← hs]
      refine Submodule.span_le.mpr ?_
      rintro x hx
      exact hc_mem ⟨x, hx⟩
    intro x
    have := hle (Submodule.mem_top (x := x))
    simpa using this
  have hquot : ∀ y : M ⧸ N, c • y = 0 := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hMc x
  have hfl : IsFiniteLength A (M ⧸ N) := isFiniteLength_of_smul_eq_zero hc_ne hquot
  have hlen : Module.length A (M ⧸ N) ≠ ⊤ := Module.length_ne_top_iff.mpr hfl
  -- Step 5: repackage the `b`-indexed data as `Fin n`-indexed data.
  set e : b ≃ Fin (Fintype.card b) := Fintype.equivFin b
  refine ⟨Fintype.card b, f ∘ e.symm, hli_A.comp e.symm e.symm.injective, ?_⟩
  have hrange : Set.range (f ∘ e.symm) = Set.range f := by
    rw [Set.range_comp, e.symm.surjective.range_eq, Set.image_univ]
  rw [hrange]
  exact hlen

/-- **Fulton, Appendix A.2.3.** For `M` a finitely generated torsion-free module over a
Noetherian domain `A` of Krull dimension `≤ 1` and `a ≠ 0`, the length of `M ⧸ a • M` is
`n * Ring.ord A a` for some natural number `n` (the "rank" of `M`, realised as the cardinality
of a maximal `A`-linearly independent family in `M`; compare
`exists_free_submodule_finiteLength_quotient`). -/
theorem exists_length_quotient_smulTop_eq [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] [NoZeroSMulDivisors A M]
    {a : A} (ha : a ≠ 0) :
    ∃ n : ℕ, Module.length A (M ⧸ a • (⊤ : Submodule A M)) = (n : ℕ∞) * Ring.ord A a := by
  obtain ⟨n, f, hli, hlen⟩ := exists_free_submodule_finiteLength_quotient (A := A) (M := M)
  set N : Submodule A M := Submodule.span A (Set.range f)
  have hb : Module.Basis (Fin n) A N := Module.Basis.span hli
  have hkN : LocalOrdSymmetry.chiKer a N = 0 := chiKer_of_free hb ha
  have hcN : LocalOrdSymmetry.chiCoker a N = (n : ℕ∞) * Ring.ord A a := by
    rw [chiCoker_of_free hb a, Fintype.card_fin]
  have hkM : LocalOrdSymmetry.chiKer a M = 0 := by
    rw [LocalOrdSymmetry.chiKer, LinearMap.ker_eq_bot.2 (smul_right_injective M ha)]
    exact Module.length_eq_zero
  have hkQ : LocalOrdSymmetry.chiKer a (M ⧸ N) = LocalOrdSymmetry.chiCoker a (M ⧸ N) :=
    chiKer_eq_chiCoker_of_lengthNeTop a hlen
  have hkQ_le : LocalOrdSymmetry.chiKer a (M ⧸ N) ≤ Module.length A (M ⧸ N) := by
    rw [LocalOrdSymmetry.chiKer]
    exact Module.length_le_of_injective (Submodule.subtype _) (Submodule.subtype_injective _)
  have hne2 : LocalOrdSymmetry.chiCoker a (M ⧸ N) ≠ ⊤ := hkQ ▸ ne_top_of_le_ne_top hlen hkQ_le
  have key := LocalOrdSymmetry.chi_add_submodule a N
  rw [hkN, hkM, add_zero, zero_add, hkQ] at key
  have hcoker_eq : LocalOrdSymmetry.chiCoker a M = LocalOrdSymmetry.chiCoker a N :=
    LocalOrdSymmetry.enat_add_right_cancel hne2 key
  refine ⟨n, ?_⟩
  rw [← range_lsmul_eq_smul_top]
  change LocalOrdSymmetry.chiCoker a M = _
  rw [hcoker_eq, hcN]

end TorsionFree

end OrderFiniteExtension
