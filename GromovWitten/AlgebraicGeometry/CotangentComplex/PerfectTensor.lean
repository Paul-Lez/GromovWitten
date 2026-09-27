/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.PerfectDualInvariance
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.Algebra.Homology.BifunctorHomotopy

/-!
# The derived tensor product of perfect complexes (chain-level construction)

This file builds the derived tensor product of two perfect objects of
`DerivedCategory (ModuleCat R)` from the chain-level tensor product of strictly perfect
complexes.  The tensor product of complexes is Mathlib's general monoidal structure on
`CochainComplex (ModuleCat R) ℤ` (`HomologicalComplex.tensorObj`, Koszul signs included); what is
new here is the proof that this operation preserves strict perfectness, and the descent of the
construction to perfect objects of the derived category.

## Main definitions

* `tensorComplex K L` : the chain-level tensor product `K ⊗ L`.
* `IsStrictlyPerfect.tensorComplex` : the tensor product of two strictly perfect complexes is
  strictly perfect.
* `rank_tensorComplex` : rank is multiplicative for the tensor product of strictly perfect
  complexes.
* `homotopyTensorHomRight/Left`, `tensorRightHomotopyEquiv`, `tensorLeftHomotopyEquiv` :
  tensoring with a fixed complex sends a homotopy (resp. a homotopy equivalence) to a homotopy
  (resp. a homotopy equivalence).
* `tensorIsoRight`, `tensorIsoLeft`, `derivedTensorIndepIso` : **representative independence**,
  i.e. an explicit isomorphism of derived objects `Q K ≅ Q K'` (resp. `Q L ≅ Q L'`) between
  strictly perfect complexes induces an isomorphism `Q (K ⊗ L) ≅ Q (K' ⊗ L')`
  (`nonempty_derivedTensorIndepIso` gives the mere-existence form).
* `derivedTensor`, `isPerfect_derivedTensor`, `derivedTensorRepIso` : the derived tensor
  product of two perfect objects of the derived category, computed on chosen strictly perfect
  representatives; it is again perfect, and `derivedTensorRepIso` gives the canonical isomorphism
  between any two choices of representatives (`nonempty_derivedTensorRepIso` : the existence
  form).
* `isStrictlyPerfect_tensorUnit`, `derivedTensorUnitIso` : the monoidal unit `R[0]` is strictly
  perfect, and `derivedTensorUnitIso` exhibits tensoring a perfect object with (the class of)
  `R[0]` as isomorphic to it (`nonempty_derivedTensorUnitIso` : the existence form).
* `derivedTensorAssocIso` : the canonical associativity isomorphism of the derived tensor
  product (`nonempty_derivedTensorAssocIso` : the existence form).
* `tensorSingleXIso` : the degree-`n` term of `K ⊗ M[0]` (`M` placed in degree `0`) is
  `K.X n ⊗ M`, i.e. the chain-level comparison with `PerfectComplex.tensorRight` at the level of
  terms (see "What is not proved" below).

## Implementation notes

`HomologicalComplex.tensorObj` defines the degree-`n` term of `K ⊗ L` as an a priori infinite
coproduct of the objects `K.X i ⊗ L.X j` over all pairs `i + j = n`.  When `K` is supported in
`[a, b]`, only the summands with `i ∈ [a, b]` can be nonzero, so this coproduct collapses to a
finite biproduct; `tensorXIsoOfBounded` records this collapse explicitly and is the key tool
used to transport finite-freeness and rank across the tensor product.

Representative independence goes through the homotopy category: a quasi-isomorphism between
strictly perfect (hence K-projective) complexes is a homotopy equivalence
(`homotopyEquivalences_of_quasiIso` from `PerfectDualInvariance.lean`), and tensoring a homotopy
equivalence with a fixed complex again gives a homotopy equivalence, using Mathlib's
`HomologicalComplex.mapBifunctorMapHomotopy₁/₂` (which shows that tensoring a fixed complex
sends a homotopy of chain maps to a homotopy of the tensored chain maps).

**What is not proved.**  `derivedTensor_symm` (braiding) is not established: Mathlib does not
equip `HomologicalComplex C c` with a braided/symmetric monoidal structure (the Koszul-signed
swap map is not formalized there), so constructing it here would mean building the braiding from
scratch, which is out of scope.  The comparison with `tensorRight` (`tensorSingleXIso` gives the
termwise object isomorphism `(K ⊗ M[0]).X n ≅ K.X n ⊗ M`) is not upgraded to an isomorphism of
complexes: that needs compatibility with the differentials of `K ⊗ M[0]` and `tensorRight K M`,
i.e. unwinding the Koszul sign of `HomologicalComplex.tensorObj`'s differential in the direction
of the (zero) differential of `M[0]`; `HomologicalComplex.isoOfComponents` is the right
constructor once that compatibility is in hand.  A genuine bifunctor on the derived category
(via `Localization.lift₂`) is also not constructed; see the repository issue tracker (`#55`) for
these follow-ups.
-/

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

namespace PerfectComplex

universe u

variable {R : Type u} [CommRing R]

/-! ## The chain-level tensor product -/

/-- The chain-level tensor product of two cochain complexes of `R`-modules: Mathlib's monoidal
structure on `CochainComplex (ModuleCat R) ℤ`, with Koszul signs in the differential. -/
noncomputable abbrev tensorComplex (K L : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  K ⊗ L

/-! ## Basic finiteness lemmas for the tensor product -/

/-- Tensoring a finite free module with a finite free module gives a finite free module. -/
theorem IsFiniteFree.tensorObj {M N : ModuleCat.{u} R} (hM : IsFiniteFree M)
    (hN : IsFiniteFree N) : IsFiniteFree (M ⊗ N) := by
  have := hM.free
  have := hM.finite
  have := hN.free
  have := hN.finite
  exact ⟨Module.Free.tensor, Module.Finite.tensorProduct R M N⟩

/-- Tensoring a zero module object with anything on the right gives a zero module object. -/
theorem isZero_tensorObj_left {M N : ModuleCat.{u} R} (h : IsZero M) : IsZero (M ⊗ N) :=
  (MonoidalCategory.tensorRight N).map_isZero h

/-- Tensoring a zero module object with anything on the left gives a zero module object. -/
theorem isZero_tensorObj_right {M N : ModuleCat.{u} R} (h : IsZero N) : IsZero (M ⊗ N) :=
  (MonoidalCategory.tensorLeft M).map_isZero h

/-! ## Collapsing the tensor product to a finite biproduct -/

/-- Given that `K` is supported in `[a, b]`, the degree-`n` term of `K ⊗ L` is a finite
biproduct of the terms `K.X i ⊗ L.X (n - i)` for `i ∈ [a, b]`.  This bypasses the a priori
infinite coproduct used to define `HomologicalComplex.tensorObj`, and is the key device behind
`IsStrictlyPerfect.tensorComplex` below. -/
noncomputable def tensorXIsoOfBounded {K : CochainComplex (ModuleCat.{u} R) ℤ} {a b : ℤ}
    (hab : IsSupportedIn K a b) (L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (K ⊗ L).X n ≅ ⨁ (fun i : ↑(Finset.Icc a b) => K.X (i : ℤ) ⊗ L.X (n - (i : ℤ))) := by
  classical
  set f : ↑(Finset.Icc a b) → ModuleCat.{u} R :=
    fun i => K.X (i : ℤ) ⊗ L.X (n - (i : ℤ)) with hf
  refine ⟨HomologicalComplex.mapBifunctorDesc (fun i j h => by
      have h' : i + j = n := h
      by_cases hi : i ∈ Finset.Icc a b
      · have hj : j = n - i := by omega
        subst hj
        exact biproduct.ι f ⟨i, hi⟩
      · exact 0),
    biproduct.desc (fun i => HomologicalComplex.ιTensorObj K L (i : ℤ) (n - (i : ℤ)) n (by ring)),
    ?_, ?_⟩
  · apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j h
    have h' : i + j = n := h
    simp only [← Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
    by_cases hi : i ∈ Finset.Icc a b
    · have hj : j = n - i := by omega
      subst hj
      simp only [dif_pos hi, biproduct.ι_desc]
      rfl
    · simp only [dif_neg hi, zero_comp]
      have hz : IsZero (K.X i ⊗ L.X j) := isZero_tensorObj_left (hab i (by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hi
        omega))
      exact hz.eq_of_src _ _
  · apply biproduct.hom_ext'
    intro i
    simp only [Category.comp_id, ← Category.assoc, biproduct.ι_desc,
      HomologicalComplex.ι_mapBifunctorDesc, dif_pos i.2]

/-! ## Finite biproducts of zero objects and of finite free modules -/

/-- A finite biproduct of zero module objects is a zero module object. -/
theorem isZero_biproduct {J : Type} [Finite J] {f : J → ModuleCat.{u} R}
    (h : ∀ j, IsZero (f j)) : IsZero (⨁ f) := by
  classical
  rw [IsZero.iff_id_eq_zero]
  apply biproduct.hom_ext'
  intro j
  rw [Category.comp_id, comp_zero]
  exact (h j).eq_of_src _ _

/-- A finite biproduct of finite free module objects is finite free. -/
theorem isFiniteFree_biproduct {J : Type} [Finite J] {f : J → ModuleCat.{u} R}
    (h : ∀ j, IsFiniteFree (f j)) : IsFiniteFree (⨁ f) := by
  classical
  have hfree : ∀ j, Module.Free R (f j) := fun j => (h j).free
  have hfin : ∀ j, Module.Finite R (f j) := fun j => (h j).finite
  have hfint : Fintype J := Fintype.ofFinite J
  have hDF : Module.Finite R (DirectSum J (fun j => (f j : Type u))) :=
    Module.Finite.instDirectSum _
  have hfinPi : Module.Finite R (∀ j, f j) :=
    Module.Finite.equiv (DFinsupp.linearEquivFunOnFintype (ι := J) (M := fun j => (f j : Type u)))
  have hfreePi : Module.Free R (∀ j, f j) := Module.Free.pi R (fun j => (f j : Type u))
  have e : (⨁ f : ModuleCat.{u} R) ≃ₗ[R] (∀ j, f j) := (ModuleCat.biproductIsoPi f).toLinearEquiv
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩

/-! ## Comparison with `tensorRight` -/

/-- The degree-`n` term of `K ⊗ M[0]` (`M` placed in cohomological degree `0`) is `K.X n ⊗ M`:
only the pair `(n, 0)` contributes to the coproduct defining `HomologicalComplex.tensorObj`. -/
noncomputable def tensorSingleXIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (M : ModuleCat.{u} R)
    (n : ℤ) :
    (K ⊗ (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M).X n ≅
      K.X n ⊗ M := by
  set S := (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M with hS
  refine ⟨HomologicalComplex.mapBifunctorDesc (fun i j h => by
      have h' : i + j = n := h
      by_cases hj : j = 0
      · subst hj
        have hi : n = i := by omega
        subst hi
        exact 𝟙 (K.X n) ⊗ₘ (HomologicalComplex.singleObjXSelf _ 0 M).hom
      · exact 0),
    (𝟙 (K.X n) ⊗ₘ (HomologicalComplex.singleObjXSelf _ 0 M).inv) ≫
      HomologicalComplex.ιTensorObj K S n 0 n (by ring),
    ?_, ?_⟩
  · apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j h
    have h' : i + j = n := h
    simp only [← Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
    by_cases hj : j = 0
    · subst hj
      have hi : n = i := by omega
      subst hi
      simp only [dif_pos trivial, ← MonoidalCategory.id_tensor_comp,
        Iso.hom_inv_id, MonoidalCategory.id_tensorHom_id]
      rfl
    · simp only [dif_neg hj, zero_comp]
      have hz : IsZero (S.X j) := HomologicalComplex.isZero_single_obj_X _ 0 M j hj
      exact (isZero_tensorObj_right hz).eq_of_src _ _
  · simp only [Category.assoc, HomologicalComplex.ι_mapBifunctorDesc, dif_pos trivial,
      ← MonoidalCategory.id_tensor_comp, Iso.inv_hom_id, MonoidalCategory.id_tensorHom_id]

/-! ## Strict perfectness of the tensor product -/

/-- If `K` is supported in `[a, b]` and `L` is supported in `[a', b']`, then `K ⊗ L` is
supported in `[a + a', b + b']`. -/
theorem IsSupportedIn.tensorComplex {K L : CochainComplex (ModuleCat.{u} R) ℤ} {a b a' b' : ℤ}
    (hab : IsSupportedIn K a b) (hab' : IsSupportedIn L a' b') :
    IsSupportedIn (K ⊗ L) (a + a') (b + b') := by
  intro n hn
  refine IsZero.of_iso (isZero_biproduct fun i => ?_) (tensorXIsoOfBounded hab L n)
  refine isZero_tensorObj_right (hab' (n - (i : ℤ)) ?_)
  have hi := i.2
  simp only [Finset.mem_Icc] at hi
  omega

/-- **The tensor product of two strictly perfect complexes is strictly perfect.**  Each term is
identified, via `tensorXIsoOfBounded`, with a finite biproduct of finite free modules. -/
theorem IsStrictlyPerfect.tensorComplex {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L) : IsStrictlyPerfect (K ⊗ L) := by
  obtain ⟨a, b, hab⟩ := hK.bounded
  obtain ⟨a', b', hab'⟩ := hL.bounded
  refine ⟨⟨a + a', b + b', hab.tensorComplex hab'⟩, fun n => ?_⟩
  refine IsFiniteFree.of_iso (isFiniteFree_biproduct fun i => ?_)
    (tensorXIsoOfBounded hab L n).symm
  exact (hK.finiteFree (i : ℤ)).tensorObj (hL.finiteFree (n - (i : ℤ)))

/-! ## Rank of finite biproducts and of tensor products -/

/-- The rank of a finite biproduct of finite free module objects is the sum of the ranks. -/
theorem rankOf_biproduct [Nontrivial R] {J : Type} [Fintype J] {f : J → ModuleCat.{u} R}
    (h : ∀ j, IsFiniteFree (f j)) : rankOf (⨁ f) = ∑ j, rankOf (f j) := by
  have hfree : ∀ j, Module.Free R (f j) := fun j => (h j).free
  have hfin : ∀ j, Module.Finite R (f j) := fun j => (h j).finite
  have e : (⨁ f : ModuleCat.{u} R) ≃ₗ[R] (∀ j, f j) := (ModuleCat.biproductIsoPi f).toLinearEquiv
  exact e.finrank_eq.trans (Module.finrank_pi_fintype (R := R) (M := fun j => (f j : Type u)))

/-- The rank of a tensor product of finite free module objects is the product of the ranks. -/
theorem rankOf_tensorObj [Nontrivial R] {M N : ModuleCat.{u} R} (hM : IsFiniteFree M)
    (hN : IsFiniteFree N) :
    rankOf (M ⊗ N) = rankOf M * rankOf N := by
  have := hM.free
  have := hM.finite
  have := hN.free
  have := hN.finite
  exact Module.finrank_tensorProduct

/-- **Rank is multiplicative for tensor products of strictly perfect complexes.**  The key
computation identifies both sides with the same double sum, via `tensorXIsoOfBounded` and a
reindexing of the inner sum by `Equiv.subRight`. -/
theorem rank_tensorComplex [Nontrivial R] {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L) :
    rank (K ⊗ L) = rank K * rank L := by
  obtain ⟨a, b, hab⟩ := hK.bounded
  obtain ⟨a', b', hab'⟩ := hL.bounded
  have hinner : ∀ i ∈ Finset.Icc a b,
      ∑ n ∈ Finset.Icc (a + a') (b + b'),
        (n.negOnePow : ℤ) * (rankOf (K.X i ⊗ L.X (n - i)) : ℤ) =
      (i.negOnePow : ℤ) * (rankOf (K.X i) : ℤ) * rank L := by
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have hreindex :
        ∑ n ∈ Finset.Icc (a + a') (b + b'),
          (n.negOnePow : ℤ) * (rankOf (K.X i ⊗ L.X (n - i)) : ℤ) =
        ∑ j ∈ Finset.Icc (a + a' - i) (b + b' - i),
          ((i + j).negOnePow : ℤ) * (rankOf (K.X i ⊗ L.X j) : ℤ) := by
      refine Finset.sum_equiv (Equiv.subRight i) (fun n => ?_) (fun n _ => ?_)
      · simp only [Finset.mem_Icc, Equiv.subRight_apply]
        omega
      · simp only [Equiv.subRight_apply]
        rw [show i + (n - i) = n from by omega]
    rw [hreindex]
    have hsub : Finset.Icc a' b' ⊆ Finset.Icc (a + a' - i) (b + b' - i) := by
      intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    have hzero : ∀ j ∈ Finset.Icc (a + a' - i) (b + b' - i), j ∉ Finset.Icc a' b' →
        ((i + j).negOnePow : ℤ) * (rankOf (K.X i ⊗ L.X j) : ℤ) = 0 := by
      intro j _ hj
      have hz : IsZero (K.X i ⊗ L.X j) :=
        isZero_tensorObj_right (hab' j (by simp only [Finset.mem_Icc] at hj; omega))
      rw [rankOf_eq_zero_of_isZero hz]
      simp
    rw [← Finset.sum_subset hsub hzero, rank_eq_sum_Icc hab', Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [rankOf_tensorObj (hK.finiteFree i) (hL.finiteFree j)]
    push_cast [Int.negOnePow_add]
    ring
  rw [rank_eq_sum_Icc (hab.tensorComplex hab')]
  have hstep : ∀ n ∈ Finset.Icc (a + a') (b + b'),
      (n.negOnePow : ℤ) * (rankOf ((K ⊗ L).X n) : ℤ) =
        ∑ i ∈ Finset.Icc a b, (n.negOnePow : ℤ) * (rankOf (K.X i ⊗ L.X (n - i)) : ℤ) := by
    intro n _
    rw [rankOf_congr (tensorXIsoOfBounded hab L n),
      rankOf_biproduct (f := fun i : ↑(Finset.Icc a b) => K.X (i : ℤ) ⊗ L.X (n - (i : ℤ)))
        (fun i => (hK.finiteFree (i : ℤ)).tensorObj (hL.finiteFree (n - (i : ℤ))))]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_coe_sort (Finset.Icc a b)
      (fun i => (n.negOnePow : ℤ) * (rankOf (K.X i ⊗ L.X (n - i)) : ℤ))
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm, rank_eq_sum_Icc hab, Finset.sum_mul]
  exact Finset.sum_congr rfl hinner

/-! ## Homotopy invariance of tensoring with a fixed complex -/

/-- Tensoring on the right with a fixed complex `L` sends a homotopy between two chain maps to
a homotopy between the tensored chain maps. -/
noncomputable def homotopyTensorHomRight {K K' L : CochainComplex (ModuleCat.{u} R) ℤ}
    {f f' : K ⟶ K'} (h : Homotopy f f') :
    Homotopy (f ⊗ₘ 𝟙 L) (f' ⊗ₘ 𝟙 L) :=
  HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 L)
    (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)

/-- Tensoring on the left with a fixed complex `K` sends a homotopy between two chain maps to
a homotopy between the tensored chain maps. -/
noncomputable def homotopyTensorHomLeft {K L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    {g g' : L ⟶ L'} (h : Homotopy g g') :
    Homotopy (𝟙 K ⊗ₘ g) (𝟙 K ⊗ₘ g') :=
  HomologicalComplex.mapBifunctorMapHomotopy₂ (h₂ := h) (f₁ := 𝟙 K)
    (F := MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (c := ComplexShape.up ℤ)

/-- **Tensoring a homotopy equivalence on the right with a fixed complex `L` gives a homotopy
equivalence.** -/
noncomputable def tensorRightHomotopyEquiv {K K' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : HomotopyEquiv K K') (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    HomotopyEquiv (K ⊗ L) (K' ⊗ L) where
  hom := f.hom ⊗ₘ 𝟙 L
  inv := f.inv ⊗ₘ 𝟙 L
  homotopyHomInvId :=
    ((Homotopy.ofEq (MonoidalCategory.comp_tensor_id f.hom f.inv)).symm.trans
      (homotopyTensorHomRight f.homotopyHomInvId)).trans
      (Homotopy.ofEq (MonoidalCategory.id_tensorHom_id K L))
  homotopyInvHomId :=
    ((Homotopy.ofEq (MonoidalCategory.comp_tensor_id f.inv f.hom)).symm.trans
      (homotopyTensorHomRight f.homotopyInvHomId)).trans
      (Homotopy.ofEq (MonoidalCategory.id_tensorHom_id K' L))

/-- **The tensor of a quasi-isomorphism between strictly perfect complexes with the identity
on a fixed complex `L` is again a quasi-isomorphism.**  The quasi-isomorphism is upgraded to a
homotopy equivalence (using that strictly perfect complexes are K-projective), which is tensored
with `L` via `HomotopyEquiv.tensorRight`; homotopy equivalences are quasi-isomorphisms. -/
theorem quasiIso_tensorHom_right {K K' : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) (hK' : IsStrictlyPerfect K') {φ : K ⟶ K'} (hφ : QuasiIso φ)
    (L : CochainComplex (ModuleCat.{u} R) ℤ) : QuasiIso (φ ⊗ₘ 𝟙 L) := by
  obtain ⟨f, hf⟩ := homotopyEquivalences_of_quasiIso hK hK' φ hφ
  subst hf
  have h2 := homotopyEquivalences_le_quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ) _
    (tensorRightHomotopyEquiv f L).homotopyEquivalences_hom
  rwa [HomologicalComplex.mem_quasiIso_iff] at h2

section DerivedIndep

attribute [local instance] HasDerivedCategory.standard

/-- The tensor of a morphism inducing an isomorphism in the derived category, between strictly
perfect complexes, with the identity on a fixed complex `L`, again induces an isomorphism in the
derived category. -/
theorem isIso_Q_map_tensorHom_right {K K' : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) (hK' : IsStrictlyPerfect K') {φ : K ⟶ K'}
    (hφ : IsIso (DerivedCategory.Q.map φ)) (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsIso (DerivedCategory.Q.map (φ ⊗ₘ 𝟙 L)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (quasiIso_tensorHom_right hK hK' ((DerivedCategory.isIso_Q_map_iff_quasiIso _ φ).1 hφ) L)

/-- **Representative independence of the derived tensor product in the left-hand variable.**  An
isomorphism `Q K ≅ Q K'` between strictly perfect complexes induces an isomorphism `Q (K ⊗ L)
≅ Q (K' ⊗ L)` for any fixed complex `L`. -/
noncomputable def tensorIsoRight {K K' : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) (hK' : IsStrictlyPerfect K')
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj K')
    (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    DerivedCategory.Q.obj (K ⊗ L) ≅ DerivedCategory.Q.obj (K' ⊗ L) :=
  have : IsIso (DerivedCategory.Q.map (derivedIsoChainMap hK e ⊗ₘ 𝟙 L)) :=
    isIso_Q_map_tensorHom_right hK hK' (by rw [Q_map_derivedIsoChainMap]; exact e.isIso_hom) L
  asIso (DerivedCategory.Q.map (derivedIsoChainMap hK e ⊗ₘ 𝟙 L))

/-- **Tensoring a homotopy equivalence on the left with a fixed complex `K` gives a homotopy
equivalence.** -/
noncomputable def tensorLeftHomotopyEquiv (K : CochainComplex (ModuleCat.{u} R) ℤ)
    {L L' : CochainComplex (ModuleCat.{u} R) ℤ} (φ : HomotopyEquiv L L') :
    HomotopyEquiv (K ⊗ L) (K ⊗ L') where
  hom := 𝟙 K ⊗ₘ φ.hom
  inv := 𝟙 K ⊗ₘ φ.inv
  homotopyHomInvId :=
    ((Homotopy.ofEq (MonoidalCategory.id_tensor_comp φ.hom φ.inv)).symm.trans
      (homotopyTensorHomLeft φ.homotopyHomInvId)).trans
      (Homotopy.ofEq (MonoidalCategory.id_tensorHom_id K L))
  homotopyInvHomId :=
    ((Homotopy.ofEq (MonoidalCategory.id_tensor_comp φ.inv φ.hom)).symm.trans
      (homotopyTensorHomLeft φ.homotopyInvHomId)).trans
      (Homotopy.ofEq (MonoidalCategory.id_tensorHom_id K L'))

/-- **The tensor of a quasi-isomorphism between strictly perfect complexes with the identity on
a fixed complex `K`, on the LEFT, is again a quasi-isomorphism.** -/
theorem quasiIso_tensorHom_left {L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (hL : IsStrictlyPerfect L) (hL' : IsStrictlyPerfect L') {ψ : L ⟶ L'} (hψ : QuasiIso ψ)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) : QuasiIso (𝟙 K ⊗ₘ ψ) := by
  obtain ⟨φ, hf⟩ := homotopyEquivalences_of_quasiIso hL hL' ψ hψ
  subst hf
  have h2 := homotopyEquivalences_le_quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ) _
    (tensorLeftHomotopyEquiv K φ).homotopyEquivalences_hom
  rwa [HomologicalComplex.mem_quasiIso_iff] at h2

/-- The tensor of a morphism inducing an isomorphism in the derived category, between strictly
perfect complexes, with the identity on a fixed complex `K`, on the LEFT, again induces an
isomorphism in the derived category. -/
theorem isIso_Q_map_tensorHom_left {L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (hL : IsStrictlyPerfect L) (hL' : IsStrictlyPerfect L') {ψ : L ⟶ L'}
    (hψ : IsIso (DerivedCategory.Q.map ψ)) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsIso (DerivedCategory.Q.map (𝟙 K ⊗ₘ ψ)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (quasiIso_tensorHom_left hL hL' ((DerivedCategory.isIso_Q_map_iff_quasiIso _ ψ).1 hψ) K)

/-- **Representative independence of the derived tensor product in the right-hand variable.**
An isomorphism `Q L ≅ Q L'` between strictly perfect complexes induces an isomorphism
`Q (K ⊗ L) ≅ Q (K ⊗ L')` for any fixed complex `K`. -/
noncomputable def tensorIsoLeft (K : CochainComplex (ModuleCat.{u} R) ℤ)
    {L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (hL : IsStrictlyPerfect L) (hL' : IsStrictlyPerfect L')
    (e : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj L') :
    DerivedCategory.Q.obj (K ⊗ L) ≅ DerivedCategory.Q.obj (K ⊗ L') :=
  have : IsIso (DerivedCategory.Q.map (𝟙 K ⊗ₘ derivedIsoChainMap hL e)) :=
    isIso_Q_map_tensorHom_left hL hL' (by rw [Q_map_derivedIsoChainMap]; exact e.isIso_hom) K
  asIso (DerivedCategory.Q.map (𝟙 K ⊗ₘ derivedIsoChainMap hL e))

/-- **Representative independence of the derived tensor product.**  Isomorphisms `Q K ≅ Q K'`
and `Q L ≅ Q L'` between strictly perfect complexes induce an isomorphism
`Q (K ⊗ L) ≅ Q (K' ⊗ L')`. -/
noncomputable def derivedTensorIndepIso {K K' L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) (hK' : IsStrictlyPerfect K')
    (hL : IsStrictlyPerfect L) (hL' : IsStrictlyPerfect L')
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj K')
    (e' : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj L') :
    DerivedCategory.Q.obj (K ⊗ L) ≅ DerivedCategory.Q.obj (K' ⊗ L') :=
  tensorIsoRight hK hK' e L ≪≫ tensorIsoLeft K' hL hL' e'

/-- Existence form of `derivedTensorIndepIso`. -/
theorem nonempty_derivedTensorIndepIso {K K' L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) (hK' : IsStrictlyPerfect K')
    (hL : IsStrictlyPerfect L) (hL' : IsStrictlyPerfect L')
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj K')
    (e' : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj L') :
    Nonempty (DerivedCategory.Q.obj (K ⊗ L) ≅ DerivedCategory.Q.obj (K' ⊗ L')) :=
  ⟨derivedTensorIndepIso hK hK' hL hL' e e'⟩

end DerivedIndep

/-! ## The derived tensor product of perfect objects -/

section Derived

attribute [local instance] HasDerivedCategory.standard

variable {E F : DerivedCategory (ModuleCat.{u} R)}

/-- **The derived tensor product of two perfect objects.**  Computed on chosen strictly perfect
representatives of `E` and `F`; representative independence is not established in this file
(see the module docstring). -/
noncomputable def derivedTensor (hE : IsPerfect E) (hF : IsPerfect F) :
    DerivedCategory (ModuleCat.{u} R) :=
  DerivedCategory.Q.obj (hE.rep ⊗ hF.rep)

/-- **The derived tensor product of two perfect objects is perfect.** -/
theorem isPerfect_derivedTensor (hE : IsPerfect E) (hF : IsPerfect F) :
    IsPerfect (derivedTensor hE hF) :=
  isPerfect_Q (hE.rep_isStrictlyPerfect.tensorComplex hF.rep_isStrictlyPerfect)

/-- **Representative independence of `derivedTensor`.**  Any two choices of strictly perfect
representatives of `E` and `F` give isomorphic derived tensor products. -/
noncomputable def derivedTensorRepIso (hE hE' : IsPerfect E) (hF hF' : IsPerfect F) :
    derivedTensor hE hF ≅ derivedTensor hE' hF' :=
  derivedTensorIndepIso hE.rep_isStrictlyPerfect hE'.rep_isStrictlyPerfect
    hF.rep_isStrictlyPerfect hF'.rep_isStrictlyPerfect
    (hE.repIso ≪≫ hE'.repIso.symm) (hF.repIso ≪≫ hF'.repIso.symm)

/-- Existence form of `derivedTensorRepIso`. -/
theorem nonempty_derivedTensorRepIso (hE hE' : IsPerfect E) (hF hF' : IsPerfect F) :
    Nonempty (derivedTensor hE hF ≅ derivedTensor hE' hF') :=
  ⟨derivedTensorRepIso hE hE' hF hF'⟩

/-- The monoidal unit of `CochainComplex (ModuleCat R) ℤ` is strictly perfect: it is `R`
placed in degree `0`. -/
theorem isStrictlyPerfect_tensorUnit :
    IsStrictlyPerfect (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) :=
  isStrictlyPerfect_single ⟨inferInstance, inferInstance⟩ 0

/-- **The derived tensor product with the unit is trivial.**  For a perfect object `E`, tensoring
with the class of the monoidal unit `R[0]` gives back (a canonical isomorphic copy of) `E`. -/
noncomputable def derivedTensorUnitIso (hE : IsPerfect E) :
    derivedTensor hE (isPerfect_Q isStrictlyPerfect_tensorUnit) ≅ E :=
  tensorIsoLeft hE.rep (isPerfect_Q isStrictlyPerfect_tensorUnit).rep_isStrictlyPerfect
      isStrictlyPerfect_tensorUnit (isPerfect_Q isStrictlyPerfect_tensorUnit).repIso ≪≫
    DerivedCategory.Q.mapIso (MonoidalCategory.rightUnitor hE.rep) ≪≫ hE.repIso

/-- Existence form of `derivedTensorUnitIso`. -/
theorem nonempty_derivedTensorUnitIso (hE : IsPerfect E) :
    Nonempty (derivedTensor hE (isPerfect_Q isStrictlyPerfect_tensorUnit) ≅ E) :=
  ⟨derivedTensorUnitIso hE⟩

/-- **Associativity of the derived tensor product.**  For perfect objects `E`, `F`, `G`, the two
ways of parenthesising the derived tensor product agree up to a canonical isomorphism. -/
noncomputable def derivedTensorAssocIso {G : DerivedCategory (ModuleCat.{u} R)} (hE : IsPerfect E)
    (hF : IsPerfect F) (hG : IsPerfect G) :
    derivedTensor (isPerfect_derivedTensor hE hF) hG ≅
      derivedTensor hE (isPerfect_derivedTensor hF hG) :=
  tensorIsoRight (isPerfect_derivedTensor hE hF).rep_isStrictlyPerfect
      (hE.rep_isStrictlyPerfect.tensorComplex hF.rep_isStrictlyPerfect)
      (isPerfect_derivedTensor hE hF).repIso hG.rep ≪≫
    DerivedCategory.Q.mapIso (MonoidalCategory.associator hE.rep hF.rep hG.rep) ≪≫
    tensorIsoLeft hE.rep (hF.rep_isStrictlyPerfect.tensorComplex hG.rep_isStrictlyPerfect)
      (isPerfect_derivedTensor hF hG).rep_isStrictlyPerfect
      (isPerfect_derivedTensor hF hG).repIso.symm

/-- Existence form of `derivedTensorAssocIso`. -/
theorem nonempty_derivedTensorAssocIso {G : DerivedCategory (ModuleCat.{u} R)} (hE : IsPerfect E)
    (hF : IsPerfect F) (hG : IsPerfect G) :
    Nonempty (derivedTensor (isPerfect_derivedTensor hE hF) hG ≅
      derivedTensor hE (isPerfect_derivedTensor hF hG)) :=
  ⟨derivedTensorAssocIso hE hF hG⟩

end Derived

end PerfectComplex

end GromovWitten.AlgebraicGeometry.CotangentComplex
