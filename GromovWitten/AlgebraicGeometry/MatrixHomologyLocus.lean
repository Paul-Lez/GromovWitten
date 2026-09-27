/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.MatrixRankLocus
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Homology loci of finite matrix complexes

For a pair of matrices whose product is zero, the actual homology over a residue field is the
quotient of the kernel by the image.  Its dimension is the dimension of the middle free module
minus the ranks of the two matrices.  This identifies the locus where that dimension is at most
a prescribed integer as an open subset of the prime spectrum.
-/

namespace GromovWitten.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u v w z

noncomputable section

namespace Matrix

variable {K : Type u} [Field K]
variable {R : Type u} [CommRing R]
variable {m : Type v} {n : Type w} {l : Type z}
variable [Fintype m] [Fintype n]

/-! ### Homology over a field -/

/-- The map into the kernel of `g` induced by `f` in a matrix complex. -/
def kernelMap (f : Matrix m n K) (g : Matrix l m K)
    (h : g.mulVecLin.comp f.mulVecLin = 0) :
    (n → K) →ₗ[K] LinearMap.ker g.mulVecLin :=
  f.mulVecLin.codRestrict (LinearMap.ker g.mulVecLin) (fun x => by
    change g.mulVecLin (f.mulVecLin x) = 0
    rw [← LinearMap.comp_apply, h]
    simp)

/-- The dimension of the homology of the matrix complex `f`, `g`. -/
noncomputable def homologyFinrank (f : Matrix m n K) (g : Matrix l m K)
    (h : g.mulVecLin.comp f.mulVecLin = 0) : ℕ :=
  Module.finrank K (LinearMap.ker g.mulVecLin ⧸ LinearMap.range (kernelMap f g h))

lemma ker_kernelMap (f : Matrix m n K) (g : Matrix l m K)
    (h : g.mulVecLin.comp f.mulVecLin = 0) :
    LinearMap.ker (kernelMap f g h) = LinearMap.ker f.mulVecLin := by
  ext x
  simp [kernelMap]

lemma finrank_range_kernelMap (f : Matrix m n K) (g : Matrix l m K)
    (h : g.mulVecLin.comp f.mulVecLin = 0) :
    Module.finrank K (LinearMap.range (kernelMap f g h)) = f.rank := by
  have hrf := LinearMap.finrank_range_add_finrank_ker f.mulVecLin
  have hrk := LinearMap.finrank_range_add_finrank_ker (kernelMap f g h)
  rw [ker_kernelMap f g h] at hrk
  have hrange : Module.finrank K (LinearMap.range (kernelMap f g h)) =
      Module.finrank K (LinearMap.range f.mulVecLin) := by
    omega
  simpa [Matrix.rank] using hrange

theorem homologyFinrank_add_rank_add_rank (f : Matrix m n K) (g : Matrix l m K)
    (h : g.mulVecLin.comp f.mulVecLin = 0) :
    homologyFinrank f g h + f.rank + g.rank = Fintype.card m := by
  have hq := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (kernelMap f g h))
  have hr := LinearMap.finrank_range_add_finrank_ker g.mulVecLin
  have hfrange := finrank_range_kernelMap f g h
  have hq' : homologyFinrank f g h + f.rank =
      Module.finrank K (LinearMap.ker g.mulVecLin) := by
    rw [hfrange] at hq
    simpa [homologyFinrank] using hq
  calc
    homologyFinrank f g h + f.rank + g.rank =
        Module.finrank K (LinearMap.ker g.mulVecLin) + g.rank := by rw [hq']
    _ = Module.finrank K (LinearMap.ker g.mulVecLin) +
        Module.finrank K (LinearMap.range g.mulVecLin) := by
      rw [Matrix.rank]
    _ = Module.finrank K (LinearMap.range g.mulVecLin) +
        Module.finrank K (LinearMap.ker g.mulVecLin) := by rw [add_comm]
    _ = Module.finrank K (m → K) := hr
    _ = Fintype.card m := by simp

/-! ### Identification with categorical module homology -/

universe q

variable {K' : Type q} [Field K']
variable {X₁ X₂ X₃ : Type q}
variable [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃]
variable [Module K' X₁] [Module K' X₂] [Module K' X₃]

/-- The finrank of the actual categorical homology of a module short complex. -/
noncomputable def moduleHomologyFinrank (f : X₁ →ₗ[K'] X₂) (g : X₂ →ₗ[K'] X₃)
    (h : g.comp f = 0) : ℕ :=
  Module.finrank K' ((CategoryTheory.ShortComplex.moduleCatMk f g h).homology)

lemma moduleHomologyFinrank_eq_quotient (f : X₁ →ₗ[K'] X₂) (g : X₂ →ₗ[K'] X₃)
    (h : g.comp f = 0) :
    moduleHomologyFinrank f g h =
      Module.finrank K' (LinearMap.ker g ⧸ LinearMap.range (f.codRestrict (LinearMap.ker g)
        (fun x => by simpa using LinearMap.congr_fun h x))) := by
  let S := CategoryTheory.ShortComplex.moduleCatMk f g h
  have he := (S.moduleCatLeftHomologyData.homologyIso).toLinearEquiv.finrank_eq
  rw [moduleHomologyFinrank]
  change Module.finrank K' (S.homology : Type q) = _
  rw [he]
  rw [CategoryTheory.ShortComplex.moduleCatLeftHomologyData_H]
  rfl

lemma moduleHomologyFinrank_add_finrank_range_add_finrank_range
    [Module.Finite K' X₁] [Module.Finite K' X₂]
    (f : X₁ →ₗ[K'] X₂) (g : X₂ →ₗ[K'] X₃)
    (h : g.comp f = 0) :
    moduleHomologyFinrank f g h + Module.finrank K' (LinearMap.range f) +
        Module.finrank K' (LinearMap.range g) = Module.finrank K' X₂ := by
  let kf : X₁ →ₗ[K'] LinearMap.ker g :=
    f.codRestrict (LinearMap.ker g) (fun x => by simpa using LinearMap.congr_fun h x)
  have hker : LinearMap.ker kf = LinearMap.ker f := by
    ext x
    simp [kf]
  have hrange : Module.finrank K' (LinearMap.range kf) =
      Module.finrank K' (LinearMap.range f) := by
    have h₁ := kf.finrank_range_add_finrank_ker
    have h₂ := f.finrank_range_add_finrank_ker
    rw [hker] at h₁
    omega
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range kf)
  have hg := g.finrank_range_add_finrank_ker
  have hq' : moduleHomologyFinrank f g h + Module.finrank K' (LinearMap.range f) =
      Module.finrank K' (LinearMap.ker g) := by
    rw [moduleHomologyFinrank_eq_quotient]
    rw [hrange] at hq
    exact hq
  calc
    moduleHomologyFinrank f g h + Module.finrank K' (LinearMap.range f) +
          Module.finrank K' (LinearMap.range g) =
        Module.finrank K' (LinearMap.ker g) + Module.finrank K' (LinearMap.range g) := by
          rw [hq']
    _ = Module.finrank K' X₂ := by omega

lemma shortComplexHomologyFinrank_add_finrank_range_add_finrank_range
    (S : CategoryTheory.ShortComplex (ModuleCat.{q} K'))
    [Module.Finite K' (S.X₁ : Type q)] [Module.Finite K' (S.X₂ : Type q)] :
    Module.finrank K' (S.homology) + Module.finrank K' (LinearMap.range S.f.hom) +
        Module.finrank K' (LinearMap.range S.g.hom) = Module.finrank K' (S.X₂ : Type q) := by
  let hd := S.moduleCatLeftHomologyData
  have he := (hd.homologyIso).toLinearEquiv.finrank_eq
  let kf : (S.X₁ : Type q) →ₗ[K'] LinearMap.ker S.g.hom :=
    S.f.hom.codRestrict (LinearMap.ker S.g.hom)
      (fun x => by
        change S.g.hom (S.f.hom x) = 0
        exact congrArg (fun m => m x) (congrArg ModuleCat.Hom.hom S.zero))
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range kf)
  have hker : LinearMap.ker kf = LinearMap.ker S.f.hom := by
    ext x
    simp [kf]
  have hrange : Module.finrank K' (LinearMap.range kf) =
      Module.finrank K' (LinearMap.range S.f.hom) := by
    have h₁ := kf.finrank_range_add_finrank_ker
    have h₂ := S.f.hom.finrank_range_add_finrank_ker
    rw [hker] at h₁
    omega
  have hq' : Module.finrank K' (hd.H) + Module.finrank K' (LinearMap.range S.f.hom) =
      Module.finrank K' (LinearMap.ker S.g.hom) := by
    change Module.finrank K' (LinearMap.ker S.g.hom ⧸ LinearMap.range kf) +
      Module.finrank K' (LinearMap.range S.f.hom) = Module.finrank K' (LinearMap.ker S.g.hom)
    rw [hrange] at hq
    exact hq
  have hg := S.g.hom.finrank_range_add_finrank_ker
  rw [he]
  change Module.finrank K' (hd.H) + Module.finrank K' (LinearMap.range S.f.hom) +
      Module.finrank K' (LinearMap.range S.g.hom) = _
  omega

variable {m' n' l' : Type q} [Fintype m'] [Fintype n']

theorem matrixHomologyFinrank_eq_moduleHomologyFinrank
    (f : Matrix m' n' K') (g : Matrix l' m' K')
    (h : g.mulVecLin.comp f.mulVecLin = 0) :
    homologyFinrank f g h = moduleHomologyFinrank f.mulVecLin g.mulVecLin h := by
  rw [moduleHomologyFinrank_eq_quotient]
  rfl

/-! ### Reduction to residue fields -/

omit [Fintype n] in
lemma residueMatrix_mul (B : Matrix l m R) (A : Matrix m n R)
    (p : PrimeSpectrum R) :
    residueMatrix (B * A) p = residueMatrix B p * residueMatrix A p := by
  ext i j
  simp [residueMatrix, Matrix.mul_apply, map_sum]

lemma residueMatrix_comp_eq_zero {R : Type u} [CommRing R]
    (f : Matrix m n R) (g : Matrix l m R) (h : g * f = 0) (p : PrimeSpectrum R) :
    (residueMatrix g p).mulVecLin.comp (residueMatrix f p).mulVecLin = 0 := by
  rw [← Matrix.mulVecLin_mul, ← residueMatrix_mul]
  rw [h]
  apply LinearMap.ext
  intro x
  funext i
  simp [Matrix.mulVec, dotProduct, residueMatrix]

/-! ### The open homology locus -/

noncomputable def residueHomologyFinrank {R : Type u} [CommRing R]
    (f : Matrix m n R) (g : Matrix l m R) (h : g * f = 0) (p : PrimeSpectrum R) : ℕ :=
  homologyFinrank (residueMatrix f p) (residueMatrix g p)
    (residueMatrix_comp_eq_zero f g h p)

theorem residueHomologyFinrank_eq_moduleHomologyFinrank
    {R' : Type q} [CommRing R'] {m' n' l' : Type q} [Fintype m'] [Fintype n']
    (f : Matrix m' n' R') (g : Matrix l' m' R') (h : g * f = 0) (p : PrimeSpectrum R') :
    residueHomologyFinrank f g h p =
      moduleHomologyFinrank (residueMatrix f p).mulVecLin (residueMatrix g p).mulVecLin
        (residueMatrix_comp_eq_zero f g h p) := by
  exact matrixHomologyFinrank_eq_moduleHomologyFinrank _ _ _

def homologyLocus {R : Type u} [CommRing R]
    (f : Matrix m n R) (g : Matrix l m R) (h : g * f = 0) (d : ℕ) :
    Set (PrimeSpectrum R) :=
  {p | residueHomologyFinrank f g h p ≤ d}

theorem homologyLocus_eq_iUnion_rankLocus {R : Type u} [CommRing R]
    (f : Matrix m n R) (g : Matrix l m R) (h : g * f = 0) (d : ℕ) :
    homologyLocus f g h d =
      ⋃ (a : ℕ) (b : ℕ) (_hcard : Fintype.card m ≤ d + a + b),
        rankLocus f a ∩ rankLocus g b := by
  ext p
  constructor
  · intro hp
    let a := (residueMatrix f p).rank
    let b := (residueMatrix g p).rank
    have hformula := homologyFinrank_add_rank_add_rank
      (residueMatrix f p) (residueMatrix g p) (residueMatrix_comp_eq_zero f g h p)
    have hcard : Fintype.card m ≤ d + a + b := by
      change residueHomologyFinrank f g h p ≤ d at hp
      dsimp [a, b]
      dsimp [residueHomologyFinrank] at hp
      omega
    refine Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨b, Set.mem_iUnion.2 ⟨hcard, ?_⟩⟩⟩
    constructor
    · change a ≤ (residueMatrix f p).rank
      exact le_rfl
    · change b ≤ (residueMatrix g p).rank
      exact le_rfl
  · intro hp
    rcases Set.mem_iUnion.1 hp with ⟨a, hp⟩
    rcases Set.mem_iUnion.1 hp with ⟨b, hp⟩
    rcases Set.mem_iUnion.1 hp with ⟨hcard, hp⟩
    rcases hp with ⟨hfa, hgb⟩
    change residueHomologyFinrank f g h p ≤ d
    have hformula := homologyFinrank_add_rank_add_rank
      (residueMatrix f p) (residueMatrix g p) (residueMatrix_comp_eq_zero f g h p)
    change a ≤ (residueMatrix f p).rank at hfa
    change b ≤ (residueMatrix g p).rank at hgb
    dsimp [residueHomologyFinrank]
    omega

theorem isOpen_homologyLocus {R : Type u} [CommRing R] [Finite l]
    (f : Matrix m n R) (g : Matrix l m R) (h : g * f = 0) (d : ℕ) :
    IsOpen (homologyLocus f g h d) := by
  rw [homologyLocus_eq_iUnion_rankLocus]
  exact isOpen_iUnion fun a ↦ isOpen_iUnion fun b ↦ isOpen_iUnion fun hcard ↦
    (isOpen_rankLocus f a).inter (isOpen_rankLocus g b)

end Matrix
end
end GromovWitten.AlgebraicGeometry
