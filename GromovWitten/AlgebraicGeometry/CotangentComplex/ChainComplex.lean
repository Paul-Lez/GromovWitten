/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.AllDegree
import GromovWitten.AlgebraicGeometry.CotangentComplex.Augmentation
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# The alternating face complex of the cotriple cotangent modules

The cotriple resolution supplies an actual family of face maps on the
scalar-extended Kähler differential modules.  This file forms their
alternating sum and proves its square is zero directly from the proved
face-face relation. It constructs the corresponding nonpositive cochain
complex, its derived-category image, and the augmentation to Kähler
differentials. Comparisons with other resolutions are not asserted here.
-/

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Preadditive
open scoped TensorProduct

universe u

namespace AllDegree

noncomputable section

namespace Cotriple

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

attribute [local instance] HasDerivedCategory.standard

/-! ## Alternating differential -/

/-- The face map regarded as a morphism of `S`-modules. -/
abbrev faceHom (n : ℕ) (i : Fin (n + 2)) :
    ModuleCat.of S (module R S (n + 1)) ⟶ ModuleCat.of S (module R S n) :=
  ModuleCat.ofHom (faceMap R S n i)

/-- The alternating sum of the face maps in degree `n`. -/
noncomputable def differential (n : ℕ) :
    ModuleCat.of S (module R S (n + 1)) ⟶ ModuleCat.of S (module R S n) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • faceHom R S n i

lemma faceHom_comp_faceHom (n : ℕ) (i j : Fin (n + 2)) (hij : i ≤ j) :
    faceHom R S (n + 1) j.succ ≫ faceHom R S n i =
      faceHom R S (n + 1) i.castSucc ≫ faceHom R S n j := by
  change ModuleCat.ofHom ((faceMap R S n i).comp
      (faceMap R S (n + 1) j.succ)) =
    ModuleCat.ofHom ((faceMap R S n j).comp
      (faceMap R S (n + 1) i.castSucc))
  rw [Cotriple.faceMap_comp_faceMap R S n i j hij]

/-! The next lemma is the finite sign cancellation. The bijection
`(i,j) ↦ (j,i+1)` pairs the two complementary index regions of the double
sum; the only geometric input is `faceHom_comp_faceHom`. -/

set_option maxHeartbeats 1000000 in
-- The finite sign-pairing proof normalizes nested categorical sums and Fin casts.
theorem differential_comp (n : ℕ) :
    differential R S (n + 1) ≫ differential R S n = 0 := by
  dsimp [differential]
  simp only [comp_sum, sum_comp, ← Finset.sum_product']
  let P := Fin (n + 2) × Fin (n + 3)
  let T : Finset P := {ij : P | (ij.2 : ℕ) ≤ (ij.1 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl T,
    ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ T → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right
      (Fin.is_lt ij.1)), ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [T, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    lia
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using! congr_arg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using!
        congr_arg Fin.castSucc (congr_arg Prod.fst h)⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [T, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred (by
      rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij'), Fin.castSucc i'), ?_, ?_⟩
    · simpa [T] using! Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    dsimp
    simp only [zsmul_comp, comp_zsmul, smul_smul, ← neg_smul]
    congr 1
    · simp only [φ, Fin.val_succ, pow_add, pow_one, mul_neg, neg_neg, mul_one]
      apply mul_comm
    · rw [faceHom_comp_faceHom R S _ _ _]
      simpa [T] using! hij

/-- The all-degree cotriple cotangent complex, indexed homologically by
`ℕ`.  Its degree `n` term is `S ⊗[Pₙ] Ω(Pₙ/R)`. -/
noncomputable def chainComplex : ChainComplex (ModuleCat S) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of S (module R S n))
    (differential R S) (differential_comp R S)

@[simp]
lemma chainComplex_X (n : ℕ) :
    (chainComplex R S).X n = ModuleCat.of S (module R S n) :=
  rfl

@[simp]
lemma chainComplex_d (n : ℕ) :
    (chainComplex R S).d (n + 1) n = differential R S n := by
  change ChainComplex.of.d (fun n => ModuleCat.of S (module R S n))
      (differential R S) (n + 1) n = differential R S n
  exact ChainComplex.of_d (fun n => ModuleCat.of S (module R S n))
    (differential R S) n

/-- Reindex the homological complex by the map n ↦ -n.  This is a cochain
complex in the nonpositive degrees, with zero terms in positive degrees. -/
noncomputable def cochainComplex : CochainComplex (ModuleCat S) ℤ :=
  (chainComplex R S).extend ComplexShape.embeddingDownNat

/-- The image of the full cotriple complex in the derived category of
S-modules. -/
noncomputable def derivedObject : DerivedCategory (ModuleCat S) :=
  DerivedCategory.Q.obj (cochainComplex R S)

/-- The augmentation of the alternating complex in degree zero.  The
single-zero-complex constructor extends this map by zero in every higher
degree, and its defining condition is exactly the degree-one cancellation. -/
noncomputable def chainAugmentation :
    chainComplex R S ⟶
      (ChainComplex.single₀ (ModuleCat S)).obj
        (ModuleCat.of S Ω[S⁄R]) :=
  (ChainComplex.toSingle₀Equiv (chainComplex R S)
    (ModuleCat.of S Ω[S⁄R])).symm
    ⟨ModuleCat.ofHom (moduleAugmentation R S 0), by
      change differential R S 0 ≫ ModuleCat.ofHom (moduleAugmentation R S 0) = 0
      dsimp [differential]
      simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero, one_smul,
        Fin.val_one, pow_one, neg_smul, add_comp, neg_comp]
      have h0 :
          faceHom R S 0 0 ≫ ModuleCat.ofHom (moduleAugmentation R S 0) =
            ModuleCat.ofHom (moduleAugmentation R S 1) := by
        rw [← ModuleCat.ofHom_comp]
        exact congrArg ModuleCat.ofHom
          (moduleAugmentation_faceMap R S 0 0)
      have h1 :
          faceHom R S 0 1 ≫ ModuleCat.ofHom (moduleAugmentation R S 0) =
            ModuleCat.ofHom (moduleAugmentation R S 1) := by
        rw [← ModuleCat.ofHom_comp]
        exact congrArg ModuleCat.ofHom
          (moduleAugmentation_faceMap R S 0 1)
      rw [h0, h1, add_neg_cancel]⟩

end Cotriple

end
end AllDegree
end GromovWitten.AlgebraicGeometry.CotangentComplex
