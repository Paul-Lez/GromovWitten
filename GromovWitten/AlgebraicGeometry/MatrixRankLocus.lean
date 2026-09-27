/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.FittingIdeals
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Matrix rank loci

For a finite rectangular matrix over a commutative ring, this file identifies the locus on the
prime spectrum where the matrix over the residue field has rank at least a prescribed integer.
The proof uses the actual `Matrix.rank` and the determinantal ideals from `FittingIdeals`.
-/

namespace GromovWitten.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u v w

noncomputable section

namespace Matrix

variable {R : Type u} [CommRing R]
variable {m : Type v} {n : Type w} [Finite m] [Fintype n]

/-! ### Rank and minors over a field -/

theorem rank_ge_iff_exists_minor {K : Type*} [Field K] (A : Matrix m n K) (k : ℕ) :
    k ≤ A.rank ↔
      ∃ (rows : Fin k ↪ m) (cols : Fin k ↪ n),
        minor A k rows cols ≠ 0 := by
  classical
  let _ := Fintype.ofFinite m
  constructor
  · intro hA
    let r := Module.finrank K (Submodule.span K (Set.range A.col))
    have hrank : k ≤ r := by
      simpa [r, A.rank_eq_finrank_span_cols] using hA
    obtain ⟨f, hfmem, _hfspan, hfind⟩ :=
      Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.col)
    let cast : Fin k → Fin r := Fin.castLE hrank
    have hcast : Function.Injective cast := Fin.castLE_injective hrank
    let f' : Fin k → m → K := f ∘ cast
    have hf'ind : LinearIndependent K f' := hfind.comp cast hcast
    choose g hg using fun i : Fin k => hfmem (cast i)
    have hg' : (fun i : Fin k => A.col (g i)) = f' := by
      funext i
      exact hg i
    have hind : LinearIndependent K (fun i : Fin k => A.col (g i)) := by
      rw [hg']
      exact hf'ind
    have hginj : Function.Injective g := by
      intro i j hij
      apply hf'ind.injective
      change f (cast i) = f (cast j)
      exact (hg i).symm.trans ((congrArg (fun x => A.col x) hij).trans (hg j))
    let ge : Fin k ↪ n := ⟨g, hginj⟩
    let C : Matrix m (Fin k) K := A.submatrix id ge
    have hCind : LinearIndependent K C.col := by
      change LinearIndependent K (fun i => A.col (ge i))
      simpa [ge] using hind
    have hCker : LinearMap.ker C.mulVecLin = ⊥ :=
      LinearMap.ker_eq_bot.mpr (Matrix.mulVec_injective_iff.mpr hCind)
    obtain ⟨G, hG⟩ := C.mulVecLin.exists_leftInverse_of_injective hCker
    let U : Matrix (Fin k) m K := LinearMap.toMatrix' G
    have hUC : U * C = (1 : Matrix (Fin k) (Fin k) K) := by
      have hCmat : LinearMap.toMatrix' C.mulVecLin = C := by
        rw [← Matrix.toLin'_apply' C]
        exact LinearMap.toMatrix'_toLin' C
      calc
        U * C = LinearMap.toMatrix' G * LinearMap.toMatrix' C.mulVecLin := by rw [hCmat]
        _ = LinearMap.toMatrix' (G ∘ₗ C.mulVecLin) :=
          (LinearMap.toMatrix'_comp G C.mulVecLin).symm
        _ = LinearMap.toMatrix' LinearMap.id := by rw [hG]
        _ = 1 := LinearMap.toMatrix'_id
    have hone : (1 : K) ∈ minorIdeal C k := by
      have hmem : (U * C).det ∈ minorIdeal (U * C) k := by
        exact Ideal.subset_span
          ⟨⟨id, Function.injective_id⟩, ⟨id, Function.injective_id⟩, rfl⟩
      have hmem' := (minorIdeal_mul_left_le U C k) hmem
      simpa [hUC] using hmem'
    by_contra hminor
    have hbot : minorIdeal C k = ⊥ := by
      apply le_antisymm
      · rw [minorIdeal]
        apply Ideal.span_le.mpr
        intro x hx
        rcases hx with ⟨rows, cols, rfl⟩
        apply Ideal.mem_bot.mpr
        by_contra hne
        apply hminor
        refine ⟨rows, cols.trans ge, ?_⟩
        simpa [C, minor, Matrix.submatrix, Function.Embedding.trans_apply] using hne
      · exact bot_le
    have hzero : (1 : K) = 0 := by
      apply Ideal.mem_bot.mp
      rw [← hbot]
      exact hone
    exact one_ne_zero hzero
  · rintro ⟨rows, cols, hdet⟩
    have hdet' : (A.submatrix rows cols).det ≠ 0 := by
      change Matrix.det (fun i j => A (rows i) (cols j)) ≠ 0
      exact hdet
    have hk : k ≤ (A.submatrix rows cols).rank := by
      rw [Matrix.rank_of_det_ne_zero hdet']
      simp
    exact hk.trans (Matrix.rank_submatrix_le A rows cols)

/-! ### Residue-field rank locus -/

/-- The matrix obtained by reducing the entries of `A` to the residue field at `p`. -/
def residueMatrix (A : Matrix m n R) (p : PrimeSpectrum R) :
    Matrix m n p.asIdeal.ResidueField :=
  fun i j => algebraMap R p.asIdeal.ResidueField (A i j)

/-- The locus where the reduction of `A` to the residue field has rank at least `k`. -/
def rankLocus (A : Matrix m n R) (k : ℕ) : Set (PrimeSpectrum R) :=
  {p | k ≤ (residueMatrix A p).rank}

omit [Finite m] [Fintype n] in
theorem residue_minor_ne_zero_iff (A : Matrix m n R) (p : PrimeSpectrum R) (k : ℕ)
    (rows : Fin k ↪ m) (cols : Fin k ↪ n) :
    minor (residueMatrix A p) k rows cols ≠ 0 ↔
      minor A k rows cols ∉ p.asIdeal := by
  change minor (fun i j => algebraMap R p.asIdeal.ResidueField (A i j)) k rows cols ≠ 0 ↔
    minor A k rows cols ∉ p.asIdeal
  constructor
  · intro h hmem
    apply h
    rw [minor_map, Ideal.algebraMap_residueField_eq_zero.mpr hmem]
  · intro h hzero
    apply h
    apply Ideal.algebraMap_residueField_eq_zero.mp
    rw [← minor_map]
    exact hzero

theorem rankLocus_eq_iUnion_basicOpen (A : Matrix m n R) (k : ℕ) :
    rankLocus A k =
      ⋃ (rows : Fin k ↪ m) (cols : Fin k ↪ n),
        (PrimeSpectrum.basicOpen (minor A k rows cols) : Set (PrimeSpectrum R)) := by
  ext p
  constructor
  · intro hp
    obtain ⟨rows, cols, hminor⟩ :=
      (rank_ge_iff_exists_minor (residueMatrix A p) k).mp hp
    refine Set.mem_iUnion.2 ⟨rows, Set.mem_iUnion.2 ⟨cols, ?_⟩⟩
    change p ∈ PrimeSpectrum.basicOpen (minor A k rows cols)
    rw [PrimeSpectrum.mem_basicOpen]
    exact (residue_minor_ne_zero_iff A p k rows cols).mp hminor
  · intro hp
    rcases Set.mem_iUnion.1 hp with ⟨rows, hp⟩
    rcases Set.mem_iUnion.1 hp with ⟨cols, hp⟩
    apply (rank_ge_iff_exists_minor (residueMatrix A p) k).mpr
    change p ∈ PrimeSpectrum.basicOpen (minor A k rows cols) at hp
    have hmem : minor A k rows cols ∉ p.asIdeal :=
      (PrimeSpectrum.mem_basicOpen _ _).mp hp
    exact ⟨rows, cols, (residue_minor_ne_zero_iff A p k rows cols).mpr hmem⟩

theorem isOpen_rankLocus (A : Matrix m n R) (k : ℕ) :
    IsOpen (rankLocus A k) := by
  rw [rankLocus_eq_iUnion_basicOpen]
  exact isOpen_iUnion fun rows ↦ isOpen_iUnion fun cols ↦ PrimeSpectrum.isOpen_basicOpen

end Matrix
end
end GromovWitten.AlgebraicGeometry
