/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import Mathlib.Algebra.DirectSum.Internal
import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Veronese graded algebras

For an internally graded algebra `𝒜`, `veronese 𝒜 d` is the external direct-sum algebra whose
`n`th piece is `𝒜 (d * n)`.  Keeping the direct sum as the ambient ring is useful here: the
Veronese is a genuine ring even when the original algebra has nonzero pieces in degrees which are
not divisible by `d`.
-/

open DirectSum

namespace GromovWitten.AlgebraicGeometry

universe u

noncomputable section

variable {R A : Type u} [CommSemiring R] [CommSemiring A] [Algebra R A]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜]

/-- The family of pieces retained by the `d`th Veronese. -/
def veronesePiece (d : ℕ) (𝒜 : ℕ → Submodule R A) : ℕ → Submodule R A :=
  fun n => 𝒜 (d * n)

instance veronesePiece_gradedMonoid (d : ℕ) :
    SetLike.GradedMonoid (veronesePiece d 𝒜) where
  one_mem := by
    simpa [veronesePiece] using (SetLike.one_mem_graded 𝒜)
  mul_mem i j x y hx hy := by
    simpa [veronesePiece, Nat.mul_add] using
      (SetLike.mul_mem_graded (A := 𝒜) hx hy)

/-- The ambient ring of the `d`th Veronese, before identifying its homogeneous pieces. -/
abbrev Veronese (d : ℕ) (𝒜 : ℕ → Submodule R A) :=
  DirectSum ℕ (fun n => veronesePiece d 𝒜 n)

instance veroneseCommSemiring (d : ℕ) : CommSemiring (Veronese d 𝒜) :=
  inferInstance

instance veroneseAlgebra (d : ℕ) : Algebra R (Veronese d 𝒜) :=
  inferInstance

/-- The `n`th homogeneous piece of the external Veronese direct sum. -/
def veroneseComponent (d : ℕ) (𝒜 : ℕ → Submodule R A) (n : ℕ) :
    Submodule R (Veronese d 𝒜) :=
  LinearMap.range (DirectSum.lof R ℕ (fun n => veronesePiece d 𝒜 n) n)

private def veroneseComponentInclusion (d : ℕ) (𝒜 : ℕ → Submodule R A) (n : ℕ) :
    veronesePiece d 𝒜 n →ₗ[R] veroneseComponent d 𝒜 n :=
  LinearMap.codRestrict (veroneseComponent d 𝒜 n)
    (DirectSum.lof R ℕ (fun n => veronesePiece d 𝒜 n) n) (fun x =>
      show (DirectSum.lof R ℕ (fun n => veronesePiece d 𝒜 n) n) x ∈
          LinearMap.range (DirectSum.lof R ℕ (fun n => veronesePiece d 𝒜 n) n) from
        ⟨x, rfl⟩)

private def veroneseDecompose (d : ℕ) (𝒜 : ℕ → Submodule R A) :
    Veronese d 𝒜 →ₗ[R] DirectSum ℕ (fun n => veroneseComponent d 𝒜 n) :=
  { toFun := DirectSum.map (fun n => (veroneseComponentInclusion d 𝒜 n).toAddMonoidHom)
    map_add' := by intro x y; ext n; simp
    map_smul' := by
      intro r x
      apply DirectSum.ext
      intro n
      change (veroneseComponentInclusion d 𝒜 n) ((r • x) n) =
        r • (veroneseComponentInclusion d 𝒜 n) (x n)
      exact (veroneseComponentInclusion d 𝒜 n).map_smul r (x n) }

private theorem veroneseDecompose_left_inverse (d : ℕ) (𝒜 : ℕ → Submodule R A) :
    (DirectSum.coeLinearMap (fun n => veroneseComponent d 𝒜 n)).comp
        (veroneseDecompose d 𝒜) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp [veroneseDecompose]
  | of n x =>
      change (DirectSum.coeLinearMap (fun n => veroneseComponent d 𝒜 n))
          (DirectSum.map (fun n => (veroneseComponentInclusion d 𝒜 n).toAddMonoidHom)
            (DirectSum.of (fun n => veronesePiece d 𝒜 n) n x)) = _
      rw [DirectSum.map_of, DirectSum.coeLinearMap_of]
      apply congrArg (DirectSum.of (fun n => veronesePiece d 𝒜 n) n)
      apply Subtype.ext
      rfl
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy]

private theorem veroneseDecompose_right_inverse (d : ℕ) (𝒜 : ℕ → Submodule R A) :
    (veroneseDecompose d 𝒜).comp
        (DirectSum.coeLinearMap (fun n => veroneseComponent d 𝒜 n)) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp [veroneseDecompose]
  | of n x =>
      obtain ⟨y, hy⟩ := x.property
      change veroneseDecompose d 𝒜
          (DirectSum.coeLinearMap (fun n => veroneseComponent d 𝒜 n)
            (DirectSum.of (fun n => veroneseComponent d 𝒜 n) n x)) = _
      rw [DirectSum.coeLinearMap_of, ← hy, DirectSum.lof_eq_of]
      change (DirectSum.map
          (fun n => (veroneseComponentInclusion d 𝒜 n).toAddMonoidHom))
          (DirectSum.of (fun n => veronesePiece d 𝒜 n) n y) = _
      rw [DirectSum.map_of]
      apply congrArg (DirectSum.of (fun n => veroneseComponent d 𝒜 n) n)
      apply Subtype.ext
      exact hy
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy]

instance veroneseComponent_gradedMonoid (d : ℕ) :
    SetLike.GradedMonoid (veroneseComponent d 𝒜) where
  one_mem := by
    let gOne : veronesePiece d 𝒜 0 :=
      @GradedMonoid.GOne.one ℕ (fun n => veronesePiece d 𝒜 n)
        inferInstance inferInstance
    refine ⟨⟨1, by simpa [veronesePiece] using (SetLike.one_mem_graded 𝒜)⟩, ?_⟩
    calc
      (DirectSum.lof R ℕ (fun n => veronesePiece d 𝒜 n) 0)
          ⟨1, by simpa [veronesePiece] using (SetLike.one_mem_graded 𝒜)⟩ =
          DirectSum.of (fun n => veronesePiece d 𝒜 n) 0
            ⟨1, by simpa [veronesePiece] using (SetLike.one_mem_graded 𝒜)⟩ :=
        DirectSum.lof_eq_of R ℕ (fun n => veronesePiece d 𝒜 n) 0 _
      _ = DirectSum.of (fun n => veronesePiece d 𝒜 n) 0 gOne := by
        congr 1
      _ = 1 := by
        simpa [gOne] using
          (DirectSum.one_def (fun n => veronesePiece d 𝒜 n)).symm
  mul_mem i j x y hx hy := by
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    let z : veronesePiece d 𝒜 (i + j) :=
      ⟨(x' : A) * (y' : A), by
        simpa [veronesePiece, Nat.mul_add] using
          (SetLike.mul_mem_graded x'.property y'.property)⟩
    refine ⟨z, ?_⟩
    rw [← hx', ← hy']
    change (DirectSum.lof R ℕ (fun n => veronesePiece d 𝒜 n) (i + j))
        z =
      (DirectSum.lof R ℕ (fun n => veronesePiece d 𝒜 n) i x') *
        (DirectSum.lof R ℕ (fun n => veronesePiece d 𝒜 n) j y')
    rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.lof_eq_of,
      DirectSum.of_mul_of]
    congr 1

instance veroneseGradedAlgebra (d : ℕ) :
    GradedAlgebra (veroneseComponent d 𝒜) :=
  letI : DirectSum.Decomposition (veroneseComponent d 𝒜) :=
    DirectSum.Decomposition.ofLinearMap
      (veroneseComponent d 𝒜)
      (veroneseDecompose d 𝒜)
      (veroneseDecompose_left_inverse d 𝒜)
      (veroneseDecompose_right_inverse d 𝒜)
  DirectSum.IsInternal.gradedAlgebra
    (DirectSum.Decomposition.isInternal (veroneseComponent d 𝒜))

omit [GradedAlgebra 𝒜] in
@[simp]
theorem veroneseComponent_mem (d n : ℕ) (x : veronesePiece d 𝒜 n) :
    (DirectSum.of (fun n => veronesePiece d 𝒜 n) n x) ∈ veroneseComponent d 𝒜 n :=
  ⟨x, rfl⟩

/-- The canonical algebra map from a Veronese direct sum to the original algebra.  Its formula on
the `n`th summand is the inclusion of `𝒜 (d * n)` into `A`. -/
def veroneseToOriginal (d : ℕ) : Veronese d 𝒜 →ₐ[R] A :=
  DirectSum.coeAlgHom (veronesePiece d 𝒜)

@[simp]
theorem veroneseToOriginal_of (d n : ℕ) (x : veronesePiece d 𝒜 n) :
    veroneseToOriginal d (DirectSum.of (fun n => veronesePiece d 𝒜 n) n x) = x :=
  DirectSum.coeAlgHom_of (veronesePiece d 𝒜) n x

/-- For positive `d`, the canonical Veronese map is injective.  The proof reads each retained
component back with the original graded decomposition; positivity is exactly what makes
`n ↦ d * n` cancellative. -/
theorem veroneseToOriginal_injective {d : ℕ} (hd : 0 < d) :
    Function.Injective (veroneseToOriginal (𝒜 := 𝒜) d) := by
  have hcoord : ∀ (z : Veronese d 𝒜) (n : ℕ),
      (DirectSum.decompose 𝒜
          (veroneseToOriginal (𝒜 := 𝒜) d z) (d * n) : A) = (z n : A) := by
    intro z
    induction z using DirectSum.induction_on with
    | zero => intro n; simp
    | of j y =>
        intro n
        by_cases h : j = n
        · subst n
          simp only [veroneseToOriginal_of,
            DirectSum.decompose_of_mem_same 𝒜 y.property,
            DirectSum.of_eq_same]
        · have hdeg : d * j ≠ d * n := by
            intro hdeg
            exact h (Nat.mul_left_cancel hd hdeg)
          have h' : n ≠ j := fun hn => h hn.symm
          simp only [veroneseToOriginal_of,
            DirectSum.decompose_of_mem_ne 𝒜 y.property hdeg,
            DirectSum.of_eq_of_ne (β := fun n => veronesePiece d 𝒜 n) j n y h']
          rfl
    | add z w hz hw =>
        intro n
        simp only [map_add, DirectSum.decompose_add, add_apply, hz, hw,
          AddMemClass.coe_add]
  intro x y hxy
  apply DirectSum.ext
  intro n
  apply Subtype.ext
  have hxy' := congrArg (fun z : A =>
    (DirectSum.decompose 𝒜 z (d * n) : A)) hxy
  rw [hcoord x n, hcoord y n] at hxy'
  exact hxy'

/-- The embedded Veronese subalgebra of `A` for a positive Veronese index. -/
abbrev veroneseSubalgebra (d : ℕ) : Subalgebra R A :=
  (veroneseToOriginal (𝒜 := 𝒜) d).range

/-- The canonical map to the embedded Veronese subalgebra. -/
abbrev veroneseToSubalgebra (d : ℕ) :
    Veronese d 𝒜 →ₐ[R] veroneseSubalgebra (𝒜 := 𝒜) d :=
  (veroneseToOriginal (𝒜 := 𝒜) d).rangeRestrict

theorem veroneseToSubalgebra_injective {d : ℕ} (hd : 0 < d) :
    Function.Injective (veroneseToSubalgebra (𝒜 := 𝒜) d) := by
  intro x y hxy
  apply veroneseToOriginal_injective hd
  exact congr_arg Subtype.val hxy

/-- The set of products of two prescribed homogeneous pieces. -/
def homogeneousProducts (m n : ℕ) : Set A :=
  {z | ∃ x ∈ 𝒜 m, ∃ y ∈ 𝒜 n, x * y = z}

/-- Degreewise multiplication spans the next homogeneous piece.  This is the concrete
surjectivity hypothesis used by the Veronese generation theorem below; it is a statement about
the input graded algebra, rather than a field recording the desired Veronese conclusion. -/
def MultiplicationSpans : Prop :=
  ∀ m n, 𝒜 (m + n) ≤ Submodule.span R (homogeneousProducts (𝒜 := 𝒜) m n)

private def degreeProjection (k : ℕ) : A →ₗ[R] 𝒜 k :=
  LinearMap.codRestrict (𝒜 k) (GradedAlgebra.proj 𝒜 k) fun x => by
    rw [GradedAlgebra.proj_apply]
    exact (DirectSum.decompose 𝒜 x k).property

private def veroneseProjection (d n : ℕ) : A →ₗ[R] veronesePiece d 𝒜 n :=
    LinearMap.codRestrict (veronesePiece d 𝒜 n)
    ((𝒜 (d * n)).subtype.comp (degreeProjection (𝒜 := 𝒜) (d * n))) (fun x => by
      exact (degreeProjection (𝒜 := 𝒜) (d * n) x).property)

/-- If every homogeneous multiplication map spans its target, then the Veronese algebra is
generated by degrees zero and one.  The proof applies the original homogeneous projection to the
finite `R`-linear combinations supplied by `MultiplicationSpans`; this is what prevents
nonhomogeneous cancellation from being mistaken for a homogeneous generation argument. -/
theorem veronese_isGeneratedInDegreeOne (d : ℕ) (h𝒜 : MultiplicationSpans (𝒜 := 𝒜)) :
    Algebra.adjoin R
        ((veroneseComponent d 𝒜 0 : Set (Veronese d 𝒜)) ∪
          (veroneseComponent d 𝒜 1 : Set (Veronese d 𝒜))) = ⊤ := by
  let B : Subalgebra R (Veronese d 𝒜) :=
    Algebra.adjoin R
      ((veroneseComponent d 𝒜 0 : Set (Veronese d 𝒜)) ∪
        (veroneseComponent d 𝒜 1 : Set (Veronese d 𝒜)))
  have hcomponent : ∀ n (x : veronesePiece d 𝒜 n),
      DirectSum.of (fun n => veronesePiece d 𝒜 n) n x ∈ B := by
    intro n
    induction n with
    | zero =>
        intro x
        exact Algebra.subset_adjoin (Or.inl (veroneseComponent_mem d 0 x))
    | succ n ih =>
        intro x
        let f : A →ₗ[R] Veronese d 𝒜 :=
          (DirectSum.lof R ℕ (fun n => veronesePiece d 𝒜 n) (n + 1)).comp
            (veroneseProjection (𝒜 := 𝒜) d (n + 1))
        have hxspan : (x : A) ∈
            Submodule.span R (homogeneousProducts (𝒜 := 𝒜) d (d * n)) := by
          apply h𝒜 d (d * n)
          simpa [veronesePiece, Nat.mul_succ, Nat.add_comm] using x.property
        have hmap : ∀ z : A, z ∈
            Submodule.span R (homogeneousProducts (𝒜 := 𝒜) d (d * n)) → f z ∈ B := by
          intro z hz
          induction hz using Submodule.span_induction with
          | mem y hy =>
              rcases hy with ⟨a, ha, b, hb, rfl⟩
              have hab : a * b ∈ 𝒜 (d * (n + 1)) := by
                simpa [Nat.mul_succ, Nat.add_comm] using
                  (SetLike.mul_mem_graded ha hb)
              have hab' : a * b ∈ veronesePiece d 𝒜 (n + 1) := by
                simpa [veronesePiece] using hab
              have hproj : veroneseProjection (𝒜 := 𝒜) d (n + 1) (a * b) =
                  ⟨a * b, hab'⟩ := by
                apply Subtype.ext
                unfold veroneseProjection
                change ↑(degreeProjection (𝒜 := 𝒜) (d * (n + 1)) (a * b)) = a * b
                change GradedAlgebra.proj 𝒜 (d * (n + 1)) (a * b) = a * b
                rw [GradedAlgebra.proj_apply,
                  DirectSum.decompose_of_mem_same 𝒜 hab]
              have haB : DirectSum.of (fun n => veronesePiece d 𝒜 n) 1
                    ⟨a, by simpa [veronesePiece] using ha⟩ ∈ B :=
                Algebra.subset_adjoin (Or.inr (veroneseComponent_mem d 1 _))
              have hbB : DirectSum.of (fun n => veronesePiece d 𝒜 n) n
                    ⟨b, by simpa [veronesePiece] using hb⟩ ∈ B := ih _
              have hmulB := B.mul_mem hbB haB
              change (DirectSum.lof R ℕ (fun n => veronesePiece d 𝒜 n) (n + 1))
                  (veroneseProjection (𝒜 := 𝒜) d (n + 1) (a * b)) ∈ B
              rw [hproj]
              have hterm :
                  DirectSum.of (fun n => veronesePiece d 𝒜 n) (n + 1)
                      ⟨a * b, hab'⟩ =
                    DirectSum.of (fun n => veronesePiece d 𝒜 n) n
                        ⟨b, by simpa [veronesePiece] using hb⟩ *
                      DirectSum.of (fun n => veronesePiece d 𝒜 n) 1
                        ⟨a, by simpa [veronesePiece] using ha⟩ := by
                rw [DirectSum.of_mul_of]
                congr 1
                exact Subtype.ext (mul_comm _ _)
              exact hterm.symm ▸ hmulB
          | zero => simpa only [map_zero] using B.zero_mem
          | add y z _ _ hy hz => simpa only [map_add] using B.add_mem hy hz
          | smul r y _ hy => simpa only [map_smul] using B.smul_mem hy r
        have hfx : f (x : A) ∈ B := hmap (x : A) hxspan
        have hprojx : veroneseProjection (𝒜 := 𝒜) d (n + 1) (x : A) = x := by
          apply Subtype.ext
          unfold veroneseProjection
          change ↑(degreeProjection (𝒜 := 𝒜) (d * (n + 1)) (x : A)) = (x : A)
          change GradedAlgebra.proj 𝒜 (d * (n + 1)) (x : A) = (x : A)
          rw [GradedAlgebra.proj_apply,
            DirectSum.decompose_of_mem_same 𝒜 x.property]
        rw [← DirectSum.lof_eq_of R ℕ (fun n => veronesePiece d 𝒜 n) (n + 1) x]
        rw [← hprojx]
        exact hfx
  change B = ⊤
  apply top_unique
  intro x hx
  clear hx
  induction x using DirectSum.induction_on with
  | zero => exact B.zero_mem
  | of n x => exact hcomponent n x
  | add x y hx hy => exact B.add_mem hx hy

/-- The degree-zero part is generated by the base algebra when every degree-zero homogeneous
element comes from `R`. -/
def DegreeZeroGenerated : Prop :=
  ∀ x : 𝒜 0, ∃ r : R, algebraMap R A r = (x : A)

/-- Under the usual degree-zero hypothesis, the Veronese is generated by its degree-one piece
over the base algebra. -/
theorem veronese_isGeneratedInDegreeOne_of_degreeZeroGenerated (d : ℕ)
    (h𝒜 : MultiplicationSpans (𝒜 := 𝒜))
    (hzero : DegreeZeroGenerated (𝒜 := 𝒜)) :
    Algebra.adjoin R (veroneseComponent d 𝒜 1 : Set (Veronese d 𝒜)) = ⊤ := by
  let B : Subalgebra R (Veronese d 𝒜) :=
    Algebra.adjoin R (veroneseComponent d 𝒜 1 : Set (Veronese d 𝒜))
  have hle :
      Algebra.adjoin R
          ((veroneseComponent d 𝒜 0 : Set (Veronese d 𝒜)) ∪
            (veroneseComponent d 𝒜 1 : Set (Veronese d 𝒜))) ≤ B := by
    refine Algebra.adjoin_le ?_
    rintro z (hz | hz)
    · rcases hz with ⟨x, rfl⟩
      rcases hzero x with ⟨r, hr⟩
      have hscalar :
          DirectSum.of (fun n => veronesePiece d 𝒜 n) 0 x =
            algebraMap R (Veronese d 𝒜) r := by
        rw [DirectSum.algebraMap_apply]
        apply congrArg (DirectSum.of (fun n => veronesePiece d 𝒜 n) 0)
        apply Subtype.ext
        exact hr.symm
      rw [DirectSum.lof_eq_of, hscalar]
      exact B.algebraMap_mem r
    · exact Algebra.subset_adjoin hz
  have htop := veronese_isGeneratedInDegreeOne (𝒜 := 𝒜) d h𝒜
  apply top_unique
  rw [← htop]
  exact hle

section MvPolynomial

variable {σ S : Type u} [CommSemiring S]

/-- Homogeneous pieces of a multivariate polynomial ring satisfy the product-span input used by
`veronese_isGeneratedInDegreeOne`.  This is the standard graded algebra case: the proof uses
Mathlib's actual equality `H₁ ^ n = Hₙ`, rather than assuming the Veronese generation conclusion.
-/
theorem mvPolynomial_multiplicationSpans :
    MultiplicationSpans
      (𝒜 := MvPolynomial.homogeneousSubmodule σ S) := by
  intro m n
  have hspan :
      Submodule.span S
          (homogeneousProducts
            (𝒜 := MvPolynomial.homogeneousSubmodule σ S) m n) =
        MvPolynomial.homogeneousSubmodule σ S m *
          MvPolynomial.homogeneousSubmodule σ S n := by
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro z ⟨a, ha, b, hb, rfl⟩
      exact Submodule.mul_mem_mul ha hb
    · refine Submodule.mul_le.2 ?_
      intro a ha b hb
      exact Submodule.subset_span ⟨a, ha, b, hb, rfl⟩
  calc
    MvPolynomial.homogeneousSubmodule σ S (m + n) =
        (MvPolynomial.homogeneousSubmodule σ S 1) ^ (m + n) :=
      (MvPolynomial.homogeneousSubmodule_one_pow (R := S) (σ := σ) (m + n)).symm
    _ = (MvPolynomial.homogeneousSubmodule σ S 1) ^ m *
          (MvPolynomial.homogeneousSubmodule σ S 1) ^ n := by
      rw [pow_add]
    _ = MvPolynomial.homogeneousSubmodule σ S m *
          MvPolynomial.homogeneousSubmodule σ S n := by
      rw [MvPolynomial.homogeneousSubmodule_one_pow,
        MvPolynomial.homogeneousSubmodule_one_pow]
    _ ≤ Submodule.span S
          (homogeneousProducts
            (𝒜 := MvPolynomial.homogeneousSubmodule σ S) m n) :=
      hspan.ge

end MvPolynomial

end

end AlgebraicGeometry

end GromovWitten
