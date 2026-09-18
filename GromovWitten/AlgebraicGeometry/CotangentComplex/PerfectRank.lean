/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.PerfectDualInvariance
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The rank of a strictly perfect complex is a homotopy invariant

`CotangentComplex/PerfectDualInvariance.lean` carries the explicit hypothesis
`RankHomotopyInvariant R` (the rank of a strictly perfect complex of `R`-modules is unchanged by
homotopy equivalences) in its statements about the rank of a perfect object and of its dual.
This file proves that hypothesis for every commutative ring, so that the rank of a perfect object
of the derived category is unconditionally well defined.

## The argument

A homotopy equivalence `e : K ≃ L` has a contractible mapping cone: in the homotopy category
the cone of an isomorphism is a zero object (`Pretriangulated.Triangle.isZero₃_iff_isIso₁`
applied to the distinguished triangle of the cone), and a complex is a zero object of the
homotopy category exactly when its identity is null-homotopic.  Since rank is additive on cones
(`rank_mappingCone`), it suffices to show that a contractible strictly perfect complex has rank
zero.  For that, choose a maximal ideal `m` of `R` and base change to the residue field
`k = R ⧸ m`: base change preserves the rank of finite free modules (`Module.finrank_baseChange`)
and the contracting homotopy, so it is enough to show that a bounded family of finite-dimensional
vector spaces `V i` with maps `d i j : V i → V j` satisfying `d ∘ d = 0` and
`ker d ⊆ im d` (exactness, which follows from the contraction) has vanishing alternating sum of
dimensions.  Rank–nullity gives `dim V i = b (i - 1) + b i` with `b i = dim (im (d i (i+1)))`,
and the alternating sum of `b (i - 1) + b i` telescopes to zero.

## Main results

* `finsum_negOnePow_finrank_eq_zero` : the alternating sum of dimensions of a bounded exact
  family of finite-dimensional vector spaces is zero.
* `rank_eq_zero_of_homotopy_id_zero` : a contractible strictly perfect complex has rank zero.
* `rank_eq_of_homotopyEquiv` : homotopy equivalent strictly perfect complexes have the same rank.
* `rankHomotopyInvariant` : `RankHomotopyInvariant R` holds for every commutative ring `R`.
* `IsPerfect.rank_eq_of_rep'`, `IsPerfect.rank_dualObject'` : the unconditional forms of the
  two statements of `PerfectDualInvariance.lean` that carried the hypothesis.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TensorProduct

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

namespace PerfectComplex

universe u

/-! ## Alternating sums of dimensions of an exact bounded family -/

section Field

variable {k : Type u} [Field k] (V : ℤ → Type u) [∀ i, AddCommGroup (V i)]
  [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)]
  (d : ∀ i j, V i →ₗ[k] V j)

/-- The dimension of the image of the map `d i (i + 1)` of a family of vector spaces. -/
noncomputable def boundaryRank (i : ℤ) : ℕ :=
  Module.finrank k (LinearMap.range (d i (i + 1)))

/-- The image of `d i (i + 1)` has dimension at most `dim V i`. -/
theorem boundaryRank_le (i : ℤ) : boundaryRank V d i ≤ Module.finrank k (V i) :=
  LinearMap.finrank_range_le _

/-- The image of `d i (i + 1)` has dimension at most `dim V (i + 1)`. -/
theorem boundaryRank_le_succ (i : ℤ) : boundaryRank V d i ≤ Module.finrank k (V (i + 1)) :=
  Submodule.finrank_le _

/-- Rank–nullity for an exact family: `dim V i = b (i - 1) + b i` where `b` is the dimension of
the boundaries.  The hypotheses are `d ∘ d = 0` and exactness `ker ⊆ im` at every spot, stated
with explicit degree equations so that no degree arithmetic occurs inside the types. -/
theorem finrank_eq_boundaryRank_add
    (hdd : ∀ i j l, j = i + 1 → l = j + 1 → (d j l).comp (d i j) = 0)
    (hex : ∀ i j l, j = i + 1 → l = j + 1 → LinearMap.ker (d j l) ≤ LinearMap.range (d i j))
    (i : ℤ) :
    Module.finrank k (V i) = boundaryRank V d (i - 1) + boundaryRank V d i := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (d i (i + 1))
  have hker : LinearMap.ker (d i (i + 1)) = LinearMap.range (d (i - 1) i) :=
    le_antisymm (hex (i - 1) i (i + 1) (by omega) rfl)
      (LinearMap.range_le_ker_iff.mpr (hdd (i - 1) i (i + 1) (by omega) rfl))
  have hb : Module.finrank k (LinearMap.range (d (i - 1) i)) = boundaryRank V d (i - 1) := by
    have key : ∀ j, j = i - 1 + 1 →
        Module.finrank k (LinearMap.range (d (i - 1) j)) = boundaryRank V d (i - 1) := by
      rintro j rfl
      rfl
    exact key i (by omega)
  rw [← h1, hker, hb, add_comm]
  rfl

/-- **The alternating sum of dimensions of a bounded exact family of finite-dimensional vector
spaces vanishes.**  Boundedness is expressed by finiteness of the support of the dimension
function. -/
theorem finsum_negOnePow_finrank_eq_zero
    (hdd : ∀ i j l, j = i + 1 → l = j + 1 → (d j l).comp (d i j) = 0)
    (hex : ∀ i j l, j = i + 1 → l = j + 1 → LinearMap.ker (d j l) ≤ LinearMap.range (d i j))
    (hfin : (Function.support fun i => Module.finrank k (V i)).Finite) :
    ∑ᶠ i, (i.negOnePow : ℤ) * (Module.finrank k (V i) : ℤ) = 0 := by
  set r : ℤ → ℤ := fun i => (boundaryRank V d i : ℤ) with hr
  set S : Finset ℤ := hfin.toFinset with hS
  have hmemS : ∀ i, i ∉ S → Module.finrank k (V i) = 0 := fun i hi => by
    by_contra h
    exact hi (by rw [hS, Set.Finite.mem_toFinset]; exact h)
  have hr_zero : ∀ i, i ∉ S → r i = 0 := fun i hi => by
    have := boundaryRank_le V d i
    rw [hmemS i hi] at this
    simp only [hr, Nat.cast_eq_zero]
    omega
  have hr_zero' : ∀ i, i ∉ S → r (i - 1) = 0 := fun i hi => by
    have := boundaryRank_le_succ V d (i - 1)
    rw [show i - 1 + 1 = i by omega, hmemS i hi] at this
    simp only [hr, Nat.cast_eq_zero]
    omega
  -- rewrite the summand through rank--nullity
  have hcongr : ∀ i, (i.negOnePow : ℤ) * (Module.finrank k (V i) : ℤ) =
      (i.negOnePow : ℤ) * r (i - 1) + (i.negOnePow : ℤ) * r i := fun i => by
    rw [finrank_eq_boundaryRank_add V d hdd hex i]
    simp only [hr]
    push_cast
    ring
  have hsupp1 : (Function.support fun i : ℤ => (i.negOnePow : ℤ) * r (i - 1)) ⊆ S := by
    intro i hi
    by_contra h
    exact hi (by simp [hr_zero' i h])
  have hsupp2 : (Function.support fun i : ℤ => (i.negOnePow : ℤ) * r i) ⊆ S := by
    intro i hi
    by_contra h
    exact hi (by simp [hr_zero i h])
  have hsupp0 : (Function.support fun i : ℤ =>
      (i.negOnePow : ℤ) * (Module.finrank k (V i) : ℤ)) ⊆ S := by
    intro i hi
    by_contra h
    exact hi (by simp [hmemS i h])
  rw [finsum_eq_sum_of_support_subset _ hsupp0]
  simp_rw [hcongr]
  rw [Finset.sum_add_distrib, ← finsum_eq_sum_of_support_subset _ hsupp1,
    ← finsum_eq_sum_of_support_subset _ hsupp2]
  -- reindex the first sum by `i ↦ i + 1`
  have hshift : (∑ᶠ i : ℤ, (i.negOnePow : ℤ) * r (i - 1)) =
      ∑ᶠ i : ℤ, ((i + 1).negOnePow : ℤ) * r i := by
    rw [← finsum_comp_equiv (Equiv.addRight (1 : ℤ))
      (f := fun i : ℤ => (i.negOnePow : ℤ) * r (i - 1))]
    refine finsum_congr fun i => ?_
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
  have hneg : (∑ᶠ i : ℤ, ((i + 1).negOnePow : ℤ) * r i) =
      -∑ᶠ i : ℤ, (i.negOnePow : ℤ) * r i := by
    rw [← finsum_neg_distrib]
    refine finsum_congr fun i => ?_
    rw [Int.negOnePow_succ]
    simp
  rw [hshift, hneg]
  ring

end Field

/-! ## Contractible strictly perfect complexes have rank zero -/

section Contractible

variable {R : Type u} [CommRing R]

/-- **A contractible strictly perfect complex has rank zero.**  The proof base changes to the
residue field of a maximal ideal, where the contraction makes the complex exact, and applies
`finsum_negOnePow_finrank_eq_zero`. -/
theorem rank_eq_zero_of_homotopy_id_zero [Nontrivial R] {C : CochainComplex (ModuleCat.{u} R) ℤ}
    (hC : IsStrictlyPerfect C) (h : Homotopy (𝟙 C) 0) : rank C = 0 := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  let _ : m.IsMaximal := hm
  let k : Type u := R ⧸ m
  let _ : Field k := Ideal.Quotient.field m
  let V : ℤ → Type u := fun i => k ⊗[R] (C.X i)
  let d : ∀ i j, V i →ₗ[k] V j := fun i j => (C.d i j).hom.baseChange k
  have hfinite : ∀ i, Module.Finite k (V i) := fun i => by
    have := (hC.finiteFree i).finite
    exact Module.Finite.base_change R k (C.X i)
  have hrank : ∀ i, rankOf (C.X i) = Module.finrank k (V i) := fun i => by
    have := (hC.finiteFree i).free
    exact (Module.finrank_baseChange (R := k) (S := R) (M' := C.X i)).symm
  have hdd : ∀ i j l, j = i + 1 → l = j + 1 → (d j l).comp (d i j) = 0 := by
    intro i j l _ _
    simp only [d]
    rw [← LinearMap.baseChange_comp, ← ModuleCat.hom_comp, C.d_comp_d, ModuleCat.hom_zero,
      LinearMap.baseChange_zero]
  have hex : ∀ i j l, j = i + 1 → l = j + 1 →
      LinearMap.ker (d j l) ≤ LinearMap.range (d i j) := by
    intro i j l hj hl
    subst hj
    subst hl
    intro x hx
    have hc := h.comm (i + 1)
    rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel (i + 1) (i + 1 + 1) from rfl),
      prevD_eq h.hom (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl)] at hc
    simp only [HomologicalComplex.id_f, HomologicalComplex.zero_f, add_zero] at hc
    have hc' := congrArg (fun φ : C.X (i + 1) ⟶ C.X (i + 1) => φ.hom.baseChange k) hc
    simp only [ModuleCat.hom_id, ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.baseChange_id,
      LinearMap.baseChange_add, LinearMap.baseChange_comp] at hc'
    have hx' := congrArg (fun φ : V (i + 1) →ₗ[k] V (i + 1) => φ x) hc'
    simp only [LinearMap.id_apply, LinearMap.add_apply, LinearMap.comp_apply] at hx'
    rw [LinearMap.mem_ker] at hx
    refine ⟨(h.hom (i + 1) i).hom.baseChange k x, ?_⟩
    simp only [d] at hx ⊢
    rw [hx, map_zero, zero_add] at hx'
    exact hx'.symm
  have hfin : (Function.support fun i => Module.finrank k (V i)).Finite := by
    obtain ⟨a, b, hab⟩ := hC.bounded
    refine (Finset.finite_toSet (Finset.Icc a b)).subset fun i hi => ?_
    simp only [Function.mem_support] at hi
    by_contra hcon
    apply hi
    simp only [Finset.coe_Icc, Set.mem_Icc, not_and_or, not_le] at hcon
    rw [← hrank, rankOf_eq_zero_of_isZero (hab i hcon)]
  have key := finsum_negOnePow_finrank_eq_zero V d hdd hex hfin
  rw [rank]
  simp_rw [hrank]
  exact key

/-- **Homotopy equivalent strictly perfect complexes have the same rank.** -/
theorem rank_eq_of_homotopyEquiv {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L) (e : HomotopyEquiv K L) :
    rank K = rank L := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · -- over the zero ring every module has `finrank` one, so both ranks are the same finsum
    have hone : ∀ M : ModuleCat.{u} R, rankOf M = 1 := fun _ => Module.finrank_subsingleton
    simp only [rank, hone]
  · have hT := HomotopyCategory.mappingCone_triangleh_distinguished e.hom
    have hiso : IsIso (CochainComplex.mappingCone.triangleh e.hom).mor₁ := by
      change IsIso ((HomotopyCategory.quotient _ _).map e.hom)
      exact (HomotopyCategory.isoOfHomotopyEquiv e).isIso_hom
    have hZ : IsZero ((HomotopyCategory.quotient _ _).obj (CochainComplex.mappingCone e.hom)) :=
      (Triangle.isZero₃_iff_isIso₁ _ hT).mpr hiso
    obtain ⟨h0⟩ := (HomotopyCategory.isZero_quotient_obj_iff _).mp hZ
    have hcone := rank_eq_zero_of_homotopy_id_zero (isStrictlyPerfect_mappingCone e.hom hK hL) h0
    rw [rank_mappingCone e.hom hK hL] at hcone
    linarith

/-- **`RankHomotopyInvariant` holds for every commutative ring.** -/
theorem rankHomotopyInvariant : RankHomotopyInvariant R :=
  fun hK hL e => rank_eq_of_homotopyEquiv hK hL e

end Contractible

/-! ## Unconditional rank statements for perfect objects -/

section Derived

variable {R : Type u} [CommRing R]

attribute [local instance] HasDerivedCategory.standard

variable {E : DerivedCategory (ModuleCat.{u} R)}

/-- **The rank of a perfect object is well defined**: it can be computed on any strictly
perfect representative.  This is `IsPerfect.rank_eq_of_rep` with its hypothesis discharged. -/
theorem IsPerfect.rank_eq_of_rep' (h : IsPerfect E)
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyPerfect K)
    (f : DerivedCategory.Q.obj K ≅ E) : PerfectComplex.rank K = h.rank :=
  IsPerfect.rank_eq_of_rep rankHomotopyInvariant h hK f

/-- **The dual of a perfect object has the same rank**, unconditionally. -/
theorem IsPerfect.rank_dualObject' [Nontrivial R] (h : IsPerfect E) :
    h.isPerfect_dualObject.rank = h.rank :=
  IsPerfect.rank_dualObject rankHomotopyInvariant h

end Derived

end PerfectComplex

end GromovWitten.AlgebraicGeometry.CotangentComplex
