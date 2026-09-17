/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Graded cones and vector bundles over an affine base

A cone over `Spec R` is the spectrum of a graded `R`-algebra `S = ⨁ₙ Sₙ` with `S₀ = R`.  Rather
than carrying the grading itself, the file encodes the equivalent datum of the associated
contraction action of the multiplicative monoid `𝔸¹`, namely a coaction

`ψ : S →ₐ[R] S[t]`,  `ψ s = s · tⁿ` for `s` homogeneous of degree `n`,

subject to the two monoid-action axioms (`GradedCone.IsConeCoaction`).  Every `ℕ`-graded
`R`-algebra in Mathlib's sense produces such a coaction (`GradedCone.gradedCoaction`), and the
degree-`n` part is recovered from the coaction, so nothing is lost.

The file constructs, and proves the defining laws of:

* the contraction operators `GradedCone.contraction ψ r` and the action axioms
  (`contraction_one`, `contraction_mul`), also as morphisms of schemes;
* the vertex, characterised as the fixed locus of `t = 0` (`GradedCone.IsConeVertex`);
* morphisms of cones, closed subcones, products, and abelian hulls;
* the affine cone `Spec Sym(M)` and the Rees normal cone `Spec gr_I(R)` as examples;
* vector bundles `C(F) = Spec Sym(F)`: functor of points, rank, smoothness, base change.
-/

open CategoryTheory AlgebraicGeometry Polynomial

namespace GromovWitten.AlgebraicGeometry

universe u v

namespace GradedCone

section Eval

variable {R S S' B C : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [CommRing S'] [Algebra R S'] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]

/-- The `R`-algebra map `S[t] →ₐ[R] B` determined by an `R`-algebra map `φ : S →ₐ[R] B` on
coefficients together with a value `b` for the variable `t`. -/
noncomputable def evalHom (φ : S →ₐ[R] B) (b : B) : Polynomial S →ₐ[R] B :=
  Polynomial.eval₂AlgHom φ b fun _ => Commute.all _ _

@[simp]
theorem evalHom_C (φ : S →ₐ[R] B) (b : B) (s : S) : evalHom φ b (Polynomial.C s) = φ s :=
  Polynomial.eval₂_C _ _

@[simp]
theorem evalHom_X (φ : S →ₐ[R] B) (b : B) : evalHom φ b (Polynomial.X : Polynomial S) = b :=
  Polynomial.eval₂_X _ _

/-- `evalHom φ b` is the unique `R`-algebra map on `S[t]` extending `φ` and sending `t` to `b`. -/
theorem evalHom_unique {φ : S →ₐ[R] B} {b : B} (g : Polynomial S →ₐ[R] B)
    (hC : ∀ s, g (Polynomial.C s) = φ s) (hX : g (Polynomial.X : Polynomial S) = b) :
    g = evalHom φ b :=
  Polynomial.algHom_ext' (AlgHom.ext fun s => (hC s).trans (evalHom_C φ b s).symm)
    (hX.trans (evalHom_X φ b).symm)

/-- Post-composing an evaluation map with an algebra map is again an evaluation map. -/
theorem comp_evalHom (g : B →ₐ[R] C) (φ : S →ₐ[R] B) (b : B) :
    g.comp (evalHom φ b) = evalHom (g.comp φ) (g b) :=
  evalHom_unique _ (fun s => by simp) (by simp)

/-- Pre-composing an evaluation map with a coefficientwise map is again an evaluation map. -/
theorem evalHom_comp_mapAlgHom (φ : S' →ₐ[R] B) (b : B) (ψ : S →ₐ[R] S') :
    (evalHom φ b).comp (Polynomial.mapAlgHom ψ) = evalHom (φ.comp ψ) b :=
  evalHom_unique _ (fun s => by simp) (by simp)

end Eval

section Coaction

variable {R S B C : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]

/-- The comultiplication `S[t] →ₐ[R] S[t][u]` sending a coefficient `s` to `s` and `t` to `u · t`.
It is dual to the multiplication of the monoid `𝔸¹`. -/
noncomputable def comul : Polynomial S →ₐ[R] Polynomial (Polynomial S) :=
  evalHom (Polynomial.CAlgHom.comp Polynomial.CAlgHom)
    (Polynomial.C Polynomial.X * Polynomial.X)

/-- The comultiplication sends a constant polynomial to the corresponding constant. -/
@[simp]
theorem comul_C (s : S) :
    comul (R := R) (Polynomial.C s) = Polynomial.C (Polynomial.C s : Polynomial S) :=
  evalHom_C _ _ _

/-- The comultiplication sends the variable `t` to `u · t`. -/
@[simp]
theorem comul_X :
    comul (R := R) (Polynomial.X : Polynomial S) =
      Polynomial.C (Polynomial.X : Polynomial S) * Polynomial.X :=
  evalHom_X _ _

/-- A contraction coaction of the multiplicative monoid `𝔸¹` on the affine scheme `Spec S` over
`Spec R`: an `R`-algebra map `ψ : S →ₐ[R] S[t]` satisfying the counit and coassociativity laws.
This is exactly the datum of an `ℕ`-grading of the `R`-algebra `S`, with `ψ s = s · tⁿ` on the
degree-`n` part.  Both fields are the defining laws of a monoid action, and they are *proved*
for every coaction constructed in this file. -/
structure IsConeCoaction (ψ : S →ₐ[R] Polynomial S) : Prop where
  /-- Contracting by the scalar `1` is the identity. -/
  counit : (evalHom (AlgHom.id R S) (1 : S)).comp ψ = AlgHom.id R S
  /-- Contracting twice agrees with contracting by the product of the two scalars. -/
  coassoc : (Polynomial.mapAlgHom ψ).comp ψ = comul.comp ψ

/-- The scaling of the `B`-point `φ` of `Spec S` by the scalar `b : B`, for a coaction `ψ`. -/
noncomputable def scale (ψ : S →ₐ[R] Polynomial S) (φ : S →ₐ[R] B) (b : B) : S →ₐ[R] B :=
  (evalHom φ b).comp ψ

/-- Scaling is natural in the test algebra. -/
theorem comp_scale (ψ : S →ₐ[R] Polynomial S) (g : B →ₐ[R] C) (φ : S →ₐ[R] B) (b : B) :
    g.comp (scale ψ φ b) = scale ψ (g.comp φ) (g b) := by
  rw [scale, scale, ← AlgHom.comp_assoc, comp_evalHom]

/-- Unit law: scaling a point by `1` does nothing. -/
theorem IsConeCoaction.scale_one {ψ : S →ₐ[R] Polynomial S} (h : IsConeCoaction ψ)
    (φ : S →ₐ[R] B) : scale ψ φ (1 : B) = φ := by
  have h1 : φ.comp (evalHom (AlgHom.id R S) (1 : S)) = evalHom φ (1 : B) := by
    rw [comp_evalHom, AlgHom.comp_id, map_one]
  rw [scale, ← h1, AlgHom.comp_assoc, h.counit, AlgHom.comp_id]

/-- Associativity law: scaling by `b` and then by `c` is scaling by `b * c`. -/
theorem IsConeCoaction.scale_scale {ψ : S →ₐ[R] Polynomial S} (h : IsConeCoaction ψ)
    (φ : S →ₐ[R] B) (b c : B) : scale ψ (scale ψ φ b) c = scale ψ φ (b * c) := by
  have key : (evalHom (evalHom φ b) c).comp comul = evalHom φ (b * c) :=
    evalHom_unique _ (fun s => by simp [comul]) (by simp [comul])
  have hL : (evalHom (evalHom φ b) c).comp ((Polynomial.mapAlgHom ψ).comp ψ) =
      scale ψ (scale ψ φ b) c := by
    rw [← AlgHom.comp_assoc, evalHom_comp_mapAlgHom]
    rfl
  rw [← hL, h.coassoc, ← AlgHom.comp_assoc, key]
  rfl

/-- The contraction of the cone by a scalar `r : R` of the base. -/
noncomputable def contraction (ψ : S →ₐ[R] Polynomial S) (r : R) : S →ₐ[R] S :=
  scale ψ (AlgHom.id R S) (algebraMap R S r)

/-- The contraction operators fix the base ring. -/
@[simp]
theorem contraction_algebraMap (ψ : S →ₐ[R] Polynomial S) (r r' : R) :
    contraction ψ r (algebraMap R S r') = algebraMap R S r' :=
  AlgHom.commutes _ _

/-- Contraction by `1` is the identity. -/
theorem contraction_one {ψ : S →ₐ[R] Polynomial S} (h : IsConeCoaction ψ) :
    contraction ψ (1 : R) = AlgHom.id R S := by
  rw [contraction, map_one, h.scale_one]

/-- Contraction by a product is the composition of the contractions. -/
theorem contraction_mul {ψ : S →ₐ[R] Polynomial S} (h : IsConeCoaction ψ) (r r' : R) :
    contraction ψ (r * r') = (contraction ψ r).comp (contraction ψ r') := by
  have e1 : (contraction ψ r).comp (contraction ψ r') =
      scale ψ (contraction ψ r) (algebraMap R S r') := by
    have e := comp_scale ψ (contraction ψ r) (AlgHom.id R S) (algebraMap R S r')
    rw [AlgHom.comp_id, contraction_algebraMap] at e
    exact e
  rw [e1, contraction, map_mul, ← h.scale_scale]
  rfl

/-- A vertex (augmentation) for a coaction: an `R`-algebra retraction `ε : S →ₐ[R] R` whose
associated closed point of every fibre is the fixed point of the contraction by `0`. -/
def IsConeVertex (ψ : S →ₐ[R] Polynomial S) (ε : S →ₐ[R] R) : Prop :=
  contraction ψ (0 : R) = (Algebra.ofId R S).comp ε

/-- A vertex is a section of the projection to the base. -/
theorem vertex_comp_ofId (ε : S →ₐ[R] R) : ε.comp (Algebra.ofId R S) = AlgHom.id R R :=
  AlgHom.ext fun r => ε.commutes r

/-- The structure map of a cone with a vertex is injective. -/
theorem injective_algebraMap_of_vertex {ε : S →ₐ[R] R} :
    Function.Injective (algebraMap R S) :=
  Function.LeftInverse.injective (g := ε) fun r => ε.commutes r

/-- The vertex is a fixed point of every contraction. -/
theorem IsConeVertex.comp_contraction {ψ : S →ₐ[R] Polynomial S} {ε : S →ₐ[R] R}
    (hψ : IsConeCoaction ψ) (h : IsConeVertex ψ ε) (r : R) :
    ε.comp (contraction ψ r) = ε := by
  have hinj : Function.Injective (Algebra.ofId R S) :=
    injective_algebraMap_of_vertex (ε := ε)
  refine AlgHom.ext fun s => hinj ?_
  have h0 : contraction ψ (0 * r) = (contraction ψ 0).comp (contraction ψ r) :=
    contraction_mul hψ 0 r
  rw [zero_mul, h] at h0
  simpa using (DFunLike.congr_fun h0 s).symm

end Coaction

section Homogeneous

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The degree-`n` part of a cone, read off from its contraction coaction as the set of `s` with
`ψ s = s · tⁿ`.  For the coaction of a graded algebra this is exactly the `n`-th graded piece,
see `GradedCone.homogeneous_gradedCoaction`. -/
noncomputable def homogeneous (ψ : S →ₐ[R] Polynomial S) (n : ℕ) : Submodule R S :=
  LinearMap.ker (ψ.toLinearMap -
    (LinearMap.mulRight R ((Polynomial.X : Polynomial S) ^ n)).comp
      (Polynomial.CAlgHom : S →ₐ[R] Polynomial S).toLinearMap)

@[simp]
theorem mem_homogeneous {ψ : S →ₐ[R] Polynomial S} {n : ℕ} {s : S} :
    s ∈ homogeneous ψ n ↔ ψ s = Polynomial.C s * Polynomial.X ^ n := by
  rw [homogeneous, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  rfl

/-- The base ring sits in degree zero. -/
theorem algebraMap_mem_homogeneous (ψ : S →ₐ[R] Polynomial S) (r : R) :
    algebraMap R S r ∈ homogeneous ψ 0 := by
  rw [mem_homogeneous, AlgHom.commutes, pow_zero, mul_one, Polynomial.algebraMap_apply]

/-- `1` is homogeneous of degree zero. -/
theorem one_mem_homogeneous (ψ : S →ₐ[R] Polynomial S) : (1 : S) ∈ homogeneous ψ 0 := by
  simp

/-- Products of homogeneous elements are homogeneous, with degrees adding. -/
theorem mul_mem_homogeneous {ψ : S →ₐ[R] Polynomial S} {m n : ℕ} {a b : S}
    (ha : a ∈ homogeneous ψ m) (hb : b ∈ homogeneous ψ n) :
    a * b ∈ homogeneous ψ (m + n) := by
  rw [mem_homogeneous] at ha hb ⊢
  rw [map_mul, ha, hb, map_mul, pow_add]
  ring

/-- A cone is generated in degree one when its coordinate algebra is generated over the base by
the degree-one part. -/
def IsGeneratedInDegreeOne (ψ : S →ₐ[R] Polynomial S) : Prop :=
  Algebra.adjoin R (homogeneous ψ 1 : Set S) = ⊤

/-- Contraction acts on a homogeneous element of degree `n` by the `n`-th power of the scalar. -/
theorem contraction_of_mem_homogeneous {ψ : S →ₐ[R] Polynomial S} {n : ℕ} {s : S}
    (hs : s ∈ homogeneous ψ n) (r : R) :
    contraction ψ r s = algebraMap R S r ^ n * s := by
  rw [mem_homogeneous] at hs
  change (evalHom (AlgHom.id R S) (algebraMap R S r)) (ψ s) = _
  rw [hs, map_mul, map_pow, evalHom_C, evalHom_X]
  simp [mul_comm]

end Homogeneous

section Decomposition

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The coefficients of the comultiplication. -/
theorem comul_coeff (p : Polynomial S) (n : ℕ) :
    (comul (R := R) p).coeff n = Polynomial.C (p.coeff n) * Polynomial.X ^ n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_mul]
  | monomial k a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, comul_C, comul_X, mul_pow,
      ← Polynomial.C_pow, ← mul_assoc, ← map_mul, Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.coeff_monomial, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
    split_ifs with hk
    · rw [hk, Polynomial.C_mul_X_pow_eq_monomial]
    · simp

/-- The projection of a cone onto its degree-`n` part: the coefficient of `tⁿ` in the
coaction. -/
noncomputable def proj (ψ : S →ₐ[R] Polynomial S) (n : ℕ) : S →ₗ[R] S :=
  ((Polynomial.lcoeff S n).restrictScalars R).comp ψ.toLinearMap

@[simp]
theorem proj_apply (ψ : S →ₐ[R] Polynomial S) (n : ℕ) (s : S) :
    proj ψ n s = (ψ s).coeff n := rfl

/-- On a homogeneous element of degree `n` the projections are the identity in degree `n` and
zero in the other degrees. -/
theorem proj_of_mem_homogeneous {ψ : S →ₐ[R] Polynomial S} {n : ℕ} {s : S}
    (hs : s ∈ homogeneous ψ n) (m : ℕ) : proj ψ m s = if m = n then s else 0 := by
  rw [mem_homogeneous] at hs
  rw [proj_apply, hs, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
  split_ifs with h1 h2 h3
  · rfl
  · exact absurd h1.symm h2
  · exact absurd h3.symm h1
  · rfl

/-- A homogeneous element of degree `n` is its own degree-`n` component. -/
theorem proj_eq_self {ψ : S →ₐ[R] Polynomial S} {n : ℕ} {s : S}
    (hs : s ∈ homogeneous ψ n) : proj ψ n s = s := by
  simpa using proj_of_mem_homogeneous hs n

/-- Every homogeneous component of an element of a cone is homogeneous.  This is where
coassociativity of the contraction action is used. -/
theorem proj_mem_homogeneous {ψ : S →ₐ[R] Polynomial S} (h : IsConeCoaction ψ) (n : ℕ) (s : S) :
    proj ψ n s ∈ homogeneous ψ n := by
  have h1 := congrArg (fun p => Polynomial.coeff p n) (DFunLike.congr_fun h.coassoc s)
  simp only [AlgHom.comp_apply, Polynomial.coe_mapAlgHom, Polynomial.coeff_map,
    RingHom.coe_coe, comul_coeff] at h1
  rw [mem_homogeneous]
  exact h1

/-- Every element of a cone is the sum of its homogeneous components. -/
theorem sum_proj {ψ : S →ₐ[R] Polynomial S} (h : IsConeCoaction ψ) (s : S) :
    ∑ n ∈ (ψ s).support, proj ψ n s = s := by
  calc ∑ n ∈ (ψ s).support, proj ψ n s
      = evalHom (AlgHom.id R S) (1 : S) (ψ s) := by
        rw [evalHom, Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
        exact (Finset.sum_congr rfl fun n _ => by simp).symm
    _ = s := DFunLike.congr_fun h.counit s

/-- The degree-one components of a cone generate the same submodule as the image of the
degree-one projection. -/
theorem proj_mem_span_homogeneous {ψ : S →ₐ[R] Polynomial S} (h : IsConeCoaction ψ) (s : S) :
    s ∈ Submodule.span R (⋃ n : ℕ, (homogeneous ψ n : Set S)) := by
  rw [← sum_proj h s]
  refine Submodule.sum_mem _ fun n _ => Submodule.subset_span ?_
  exact Set.mem_iUnion.2 ⟨n, proj_mem_homogeneous h n s⟩

end Decomposition

section GradedAlgebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (𝒮 : ℕ → Submodule R S) [GradedAlgebra 𝒮]

/-- Two `R`-linear maps out of an internally graded algebra agree once they agree on
homogeneous elements. -/
theorem linearMap_ext_of_graded {M : Type*} [AddCommMonoid M] [Module R M] {f g : S →ₗ[R] M}
    (h : ∀ (n : ℕ) (x : 𝒮 n), f (x : S) = g (x : S)) : f = g := by
  classical
  refine LinearMap.ext fun s => ?_
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒮 s]
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒮 s]
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun n _ => h n _

/-- Two `R`-algebra maps out of an internally graded algebra agree once they agree on
homogeneous elements. -/
theorem algHom_ext_of_graded {T : Type*} [Semiring T] [Algebra R T] {f g : S →ₐ[R] T}
    (h : ∀ (n : ℕ) (x : 𝒮 n), f (x : S) = g (x : S)) : f = g :=
  AlgHom.toLinearMap_injective (linearMap_ext_of_graded 𝒮 h)

/-- The contraction coaction attached to an internal `ℕ`-grading of an `R`-algebra: it scales a
homogeneous element of degree `n` by `tⁿ`. -/
noncomputable def gradedCoaction : S →ₐ[R] Polynomial S :=
  (DirectSum.toAlgebra R (fun n => 𝒮 n)
    (fun n => (LinearMap.mulRight R ((Polynomial.X : Polynomial S) ^ n)).comp
      ((Polynomial.CAlgHom : S →ₐ[R] Polynomial S).toLinearMap.comp (𝒮 n).subtype))
    (by simp) (by
      intro i j ai aj
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        AlgHom.toLinearMap_apply, Polynomial.CAlgHom_apply, LinearMap.mulRight_apply]
      rw [SetLike.coe_gMul, map_mul, pow_add]
      ring)).comp
    (DirectSum.decomposeAlgEquiv 𝒮).toAlgHom

/-- The coaction of a graded algebra scales homogeneous elements by the corresponding power. -/
theorem gradedCoaction_of_mem {n : ℕ} {s : S} (hs : s ∈ 𝒮 n) :
    gradedCoaction 𝒮 s = Polynomial.C s * Polynomial.X ^ n := by
  rw [gradedCoaction, AlgHom.comp_apply]
  change DirectSum.toAlgebra R (fun n => 𝒮 n) _ _ _ (DirectSum.decompose 𝒮 s) = _
  rw [DirectSum.decompose_of_mem 𝒮 hs, DirectSum.toAlgebra_apply]
  exact DirectSum.toSemiring_of _ _ _ _ _

/-- Homogeneous elements for the grading are homogeneous for the coaction. -/
theorem mem_homogeneous_gradedCoaction {n : ℕ} {s : S} (hs : s ∈ 𝒮 n) :
    s ∈ homogeneous (gradedCoaction 𝒮) n :=
  mem_homogeneous.2 (gradedCoaction_of_mem 𝒮 hs)

/-- The coaction of a graded algebra satisfies the cone axioms. -/
theorem isConeCoaction_gradedCoaction : IsConeCoaction (gradedCoaction 𝒮) where
  counit := by
    refine algHom_ext_of_graded 𝒮 fun n x => ?_
    rw [AlgHom.comp_apply, gradedCoaction_of_mem 𝒮 x.2, map_mul, map_pow, evalHom_C, evalHom_X]
    simp
  coassoc := by
    refine algHom_ext_of_graded 𝒮 fun n x => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, gradedCoaction_of_mem 𝒮 x.2]
    simp only [map_mul, map_pow, Polynomial.coe_mapAlgHom, Polynomial.map_C, Polynomial.map_X,
      comul_C, comul_X, RingHom.coe_coe, gradedCoaction_of_mem 𝒮 x.2]
    ring

/-- The degree-`n` coefficient of the coaction is the degree-`n` graded projection. -/
theorem gradedCoaction_coeff (n : ℕ) (s : S) :
    (gradedCoaction 𝒮 s).coeff n = GradedAlgebra.proj 𝒮 n s := by
  have key : ((Polynomial.lcoeff S n).restrictScalars R).comp
      (gradedCoaction 𝒮).toLinearMap = GradedAlgebra.proj 𝒮 n := by
    refine linearMap_ext_of_graded 𝒮 fun m x => ?_
    change (gradedCoaction 𝒮 (x : S)).coeff n = GradedAlgebra.proj 𝒮 n (x : S)
    rw [gradedCoaction_of_mem 𝒮 x.2, Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.coeff_monomial, GradedAlgebra.proj_apply]
    by_cases hmn : m = n
    · subst hmn
      rw [if_pos rfl, DirectSum.decompose_of_mem_same 𝒮 x.2]
    · rw [if_neg hmn, DirectSum.decompose_of_mem_ne 𝒮 x.2 hmn]
  exact LinearMap.congr_fun key s

/-- The degree-`n` part of the cone of a graded algebra is the degree-`n` graded piece. -/
theorem homogeneous_gradedCoaction (n : ℕ) :
    homogeneous (gradedCoaction 𝒮) n = 𝒮 n := by
  refine le_antisymm (fun s hs => ?_) fun s hs => mem_homogeneous_gradedCoaction 𝒮 hs
  have h1 : GradedAlgebra.proj 𝒮 n s = s := by
    rw [← gradedCoaction_coeff]
    exact proj_eq_self hs
  rw [← h1, GradedAlgebra.proj_apply]
  exact SetLike.coe_mem _

end GradedAlgebra

section SymmetricAlgebra

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]

/-- The contraction coaction of the affine cone `Spec Sym(M)`: it scales the degree-one
generators by the variable `t`. -/
noncomputable def symCoaction :
    SymmetricAlgebra R M →ₐ[R] Polynomial (SymmetricAlgebra R M) :=
  SymmetricAlgebra.lift
    ((LinearMap.mulRight R (Polynomial.X : Polynomial (SymmetricAlgebra R M))).comp
      ((Polynomial.CAlgHom :
          SymmetricAlgebra R M →ₐ[R] Polynomial (SymmetricAlgebra R M)).toLinearMap.comp
        (SymmetricAlgebra.ι R M)))

@[simp]
theorem symCoaction_ι (m : M) :
    symCoaction R M (SymmetricAlgebra.ι R M m) =
      Polynomial.C (SymmetricAlgebra.ι R M m) * Polynomial.X :=
  SymmetricAlgebra.lift_ι_apply _ _

/-- The generators of the symmetric algebra are homogeneous of degree one. -/
theorem ι_mem_homogeneous_one (m : M) :
    SymmetricAlgebra.ι R M m ∈ homogeneous (symCoaction R M) 1 := by
  rw [mem_homogeneous, symCoaction_ι, pow_one]

/-- The coaction of the affine cone `Spec Sym(M)` satisfies the cone axioms. -/
theorem isConeCoaction_symCoaction : IsConeCoaction (symCoaction R M) where
  counit := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
    simp
  coassoc := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
    change Polynomial.mapAlgHom (symCoaction R M)
        (symCoaction R M (SymmetricAlgebra.ι R M m)) =
      comul (symCoaction R M (SymmetricAlgebra.ι R M m))
    simp only [symCoaction_ι, map_mul, Polynomial.coe_mapAlgHom, Polynomial.map_C,
      Polynomial.map_X, comul_C, comul_X, RingHom.coe_coe]
    ring

/-- The augmentation of the symmetric algebra is the vertex of the affine cone. -/
theorem isConeVertex_symCoaction :
    IsConeVertex (symCoaction R M) (SymmetricAlgebra.algebraMapInv (R := R) (M := M)) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
  change contraction (symCoaction R M) 0 (SymmetricAlgebra.ι R M m) =
    algebraMap R (SymmetricAlgebra R M)
      (SymmetricAlgebra.algebraMapInv (SymmetricAlgebra.ι R M m))
  rw [contraction_of_mem_homogeneous (ι_mem_homogeneous_one R M m),
    SymmetricAlgebra.algebraMapInv_ι]
  simp

/-- The abstract contraction of `Spec Sym(M)` agrees with the contraction constructed in
`GromovWitten.AlgebraicGeometry.AffineCone`. -/
theorem contraction_symCoaction (r : R) :
    contraction (symCoaction R M) r = AffineCone.contraction R M r := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
  change contraction (symCoaction R M) r (SymmetricAlgebra.ι R M m) =
    AffineCone.contraction R M r (SymmetricAlgebra.ι R M m)
  rw [contraction_of_mem_homogeneous (ι_mem_homogeneous_one R M m),
    AffineCone.contraction_generator, pow_one, Algebra.smul_def]

/-- The symmetric algebra is generated in degree one. -/
theorem isGeneratedInDegreeOne_symCoaction :
    IsGeneratedInDegreeOne (symCoaction R M) := by
  rw [IsGeneratedInDegreeOne, eq_top_iff]
  rintro x -
  induction x using SymmetricAlgebra.induction with
  | algebraMap r => exact Subalgebra.algebraMap_mem _ r
  | ι m => exact Algebra.subset_adjoin (ι_mem_homogeneous_one R M m)
  | mul a b ha hb => exact Subalgebra.mul_mem _ ha hb
  | add a b ha hb => exact Subalgebra.add_mem _ ha hb

end SymmetricAlgebra

section SymmetricDegreeOne

variable (R : Type u) [CommRing R] (F : Type u) [AddCommGroup F] [Module R F]

/-- A left inverse of `ι`, built from the square-zero extension `R ⊕ F`. -/
noncomputable def symIInv : SymmetricAlgebra R F →ₗ[R] F := by
  letI : Module Rᵐᵒᵖ F := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  haveI : IsCentralScalar R F := ⟨fun _ _ => rfl⟩
  exact (TrivSqZeroExt.sndHom R F).comp
    (SymmetricAlgebra.lift (TrivSqZeroExt.inrHom R F)).toLinearMap

/-- `symIInv` is a left inverse of the canonical map `F → Sym(F)`. -/
theorem symIInv_ι (m : F) : symIInv R F (SymmetricAlgebra.ι R F m) = m := by
  simp [symIInv]

/-- The canonical map `F → Sym(F)` is injective. -/
theorem ι_injective : Function.Injective (SymmetricAlgebra.ι R F) :=
  Function.LeftInverse.injective (symIInv_ι R F)

/-- The symmetric algebra is generated by the image of `ι`. -/
theorem adjoin_range_ι : Algebra.adjoin R (Set.range (SymmetricAlgebra.ι R F)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using SymmetricAlgebra.induction with
  | algebraMap r => exact Subalgebra.algebraMap_mem _ r
  | ι m => exact Algebra.subset_adjoin ⟨m, rfl⟩
  | mul a b ha hb => exact Subalgebra.mul_mem _ ha hb
  | add a b ha hb => exact Subalgebra.add_mem _ ha hb

/-- The monomials in the generators span the symmetric algebra. -/
theorem span_closure_range_ι :
    Submodule.span R
      (Submonoid.closure (Set.range (SymmetricAlgebra.ι R F)) : Set (SymmetricAlgebra R F)) =
      ⊤ := by
  have h := Algebra.adjoin_eq_span (R := R) (Set.range (SymmetricAlgebra.ι R F))
  rw [adjoin_range_ι, Algebra.top_toSubmodule] at h
  exact h.symm

/-- A monomial in the generators of `Sym(F)` is homogeneous of some degree, is a scalar if that
degree is zero, and is a generator if that degree is one. -/
theorem exists_degree_of_mem_closure {x : SymmetricAlgebra R F}
    (hx : x ∈ Submonoid.closure (Set.range (SymmetricAlgebra.ι R F))) :
    ∃ n : ℕ, x ∈ homogeneous (symCoaction R F) n ∧
      (n = 0 → ∃ r : R, x = algebraMap R (SymmetricAlgebra R F) r) ∧
      (n = 1 → x ∈ LinearMap.range (SymmetricAlgebra.ι R F)) := by
  induction hx using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact ⟨1, ι_mem_homogeneous_one R F m, by omega, fun _ => ⟨m, rfl⟩⟩
  | one => exact ⟨0, one_mem_homogeneous _, fun _ => ⟨1, (map_one _).symm⟩, by omega⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨nx, hx, hx0, hx1⟩ := ihx
    obtain ⟨ny, hy, hy0, hy1⟩ := ihy
    refine ⟨nx + ny, mul_mem_homogeneous hx hy, fun h => ?_, fun h => ?_⟩
    · obtain ⟨r, hr⟩ := hx0 (by omega)
      obtain ⟨r', hr'⟩ := hy0 (by omega)
      exact ⟨r * r', by rw [hr, hr', map_mul]⟩
    · have hcase : nx = 0 ∧ ny = 1 ∨ nx = 1 ∧ ny = 0 := by omega
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨r, hr⟩ := hx0 h1
        obtain ⟨m, hm⟩ := hy1 h2
        exact ⟨r • m, by rw [map_smul, hm, hr, Algebra.smul_def]⟩
      · obtain ⟨m, hm⟩ := hx1 h1
        obtain ⟨r, hr⟩ := hy0 h2
        exact ⟨r • m, by rw [map_smul, hm, hr, Algebra.smul_def, mul_comm]⟩

/-- The degree-one component of any element of `Sym(F)` comes from `F`. -/
theorem proj_one_mem_range (s : SymmetricAlgebra R F) :
    proj (symCoaction R F) 1 s ∈ LinearMap.range (SymmetricAlgebra.ι R F) := by
  have hspan : s ∈ Submodule.span R
      (Submonoid.closure (Set.range (SymmetricAlgebra.ι R F)) :
        Set (SymmetricAlgebra R F)) := by
    rw [span_closure_range_ι]
    trivial
  induction hspan using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, hn, -, h1⟩ := exists_degree_of_mem_closure R F hx
    rw [proj_of_mem_homogeneous hn]
    split_ifs with h
    · exact h1 h.symm
    · exact zero_mem _
  | zero => simp
  | add x y _ _ ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | smul a x _ ih =>
    rw [map_smul]
    exact Submodule.smul_mem _ a ih

/-- The degree-one part of the cone `C(F) = Spec Sym(F)` is exactly the image of `F`. -/
theorem homogeneous_one_symCoaction :
    homogeneous (symCoaction R F) 1 = LinearMap.range (SymmetricAlgebra.ι R F) := by
  refine le_antisymm (fun s hs => ?_) ?_
  · rw [← proj_eq_self hs]
    exact proj_one_mem_range R F s
  · rintro _ ⟨m, rfl⟩
    exact ι_mem_homogeneous_one R F m

/-- The degree-one part of the vector bundle `C(F)` is canonically `F`. -/
noncomputable def degreeOneEquiv : F ≃ₗ[R] homogeneous (symCoaction R F) 1 :=
  LinearEquiv.ofBijective
    ((SymmetricAlgebra.ι R F).codRestrict _ (ι_mem_homogeneous_one R F))
    ⟨fun x y h => ι_injective R F (congrArg Subtype.val h), fun x => by
      obtain ⟨m, hm⟩ := (homogeneous_one_symCoaction R F).le x.2
      exact ⟨m, Subtype.ext hm⟩⟩

/-- The rank of the degree-one part of a vector bundle is the rank of the module. -/
theorem rank_homogeneous_one :
    Module.rank R (homogeneous (symCoaction R F) 1) = Module.rank R F :=
  (degreeOneEquiv R F).symm.rank_eq

/-- The finite rank of the degree-one part of a vector bundle is the rank of the module. -/
theorem finrank_homogeneous_one :
    Module.finrank R (homogeneous (symCoaction R F) 1) = Module.finrank R F :=
  (degreeOneEquiv R F).symm.finrank_eq

end SymmetricDegreeOne

section Morphisms

variable {R S S' S'' : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [CommRing S'] [Algebra R S'] [CommRing S''] [Algebra R S'']

/-- Coefficientwise maps on polynomials compose. -/
theorem mapAlgHom_comp (f : S' →ₐ[R] S'') (g : S →ₐ[R] S') :
    (Polynomial.mapAlgHom f).comp (Polynomial.mapAlgHom g) = Polynomial.mapAlgHom (f.comp g) :=
  Polynomial.algHom_ext' (AlgHom.ext fun s => by simp) (by simp)

/-- The comultiplication is natural in the coefficient algebra. -/
theorem comul_comp_mapAlgHom (φ : S →ₐ[R] S') :
    comul.comp (Polynomial.mapAlgHom φ) =
      (Polynomial.mapAlgHom (Polynomial.mapAlgHom φ)).comp comul :=
  Polynomial.algHom_ext' (AlgHom.ext fun s => by simp) (by simp)

/-- A morphism of cones over `Spec R`: an `R`-algebra map intertwining the two contraction
coactions.  On spectra this is a morphism over the base commuting with the contractions. -/
def IsConeHom (ψ : S →ₐ[R] Polynomial S) (ψ' : S' →ₐ[R] Polynomial S')
    (φ : S →ₐ[R] S') : Prop :=
  (Polynomial.mapAlgHom φ).comp ψ = ψ'.comp φ

/-- The identity is a morphism of cones. -/
theorem isConeHom_id (ψ : S →ₐ[R] Polynomial S) : IsConeHom ψ ψ (AlgHom.id R S) := by
  have hid : Polynomial.mapAlgHom (AlgHom.id R S) = AlgHom.id R (Polynomial S) :=
    Polynomial.algHom_ext' (AlgHom.ext fun s => by simp) (by simp)
  rw [IsConeHom, hid, AlgHom.id_comp, AlgHom.comp_id]

/-- Morphisms of cones compose. -/
theorem IsConeHom.comp {ψ : S →ₐ[R] Polynomial S} {ψ' : S' →ₐ[R] Polynomial S'}
    {ψ'' : S'' →ₐ[R] Polynomial S''} {φ : S →ₐ[R] S'} {φ' : S' →ₐ[R] S''}
    (h : IsConeHom ψ ψ' φ) (h' : IsConeHom ψ' ψ'' φ') : IsConeHom ψ ψ'' (φ'.comp φ) := by
  rw [IsConeHom, ← mapAlgHom_comp, AlgHom.comp_assoc, h, ← AlgHom.comp_assoc, h',
    AlgHom.comp_assoc]

/-- A morphism of cones commutes with every contraction. -/
theorem IsConeHom.comp_contraction {ψ : S →ₐ[R] Polynomial S} {ψ' : S' →ₐ[R] Polynomial S'}
    {φ : S →ₐ[R] S'} (h : IsConeHom ψ ψ' φ) (r : R) :
    φ.comp (contraction ψ r) = (contraction ψ' r).comp φ := by
  have hL : φ.comp (contraction ψ r) = (evalHom φ (algebraMap R S' r)).comp ψ := by
    rw [contraction, scale, ← AlgHom.comp_assoc, comp_evalHom, AlgHom.comp_id, AlgHom.commutes]
  have hR : (contraction ψ' r).comp φ = (evalHom φ (algebraMap R S' r)).comp ψ := by
    rw [contraction, scale, AlgHom.comp_assoc, ← h, ← AlgHom.comp_assoc,
      evalHom_comp_mapAlgHom, AlgHom.id_comp]
  rw [hL, hR]

/-- A morphism of cones carries the vertex to the vertex. -/
theorem IsConeHom.comp_vertex {ψ : S →ₐ[R] Polynomial S} {ψ' : S' →ₐ[R] Polynomial S'}
    {φ : S →ₐ[R] S'} {ε : S →ₐ[R] R} {ε' : S' →ₐ[R] R} (h : IsConeHom ψ ψ' φ)
    (hv : IsConeVertex ψ ε) (hv' : IsConeVertex ψ' ε') : ε'.comp φ = ε := by
  refine AlgHom.ext fun s => injective_algebraMap_of_vertex (ε := ε') ?_
  have h1 := DFunLike.congr_fun (h.comp_contraction (0 : R)) s
  rw [hv, hv'] at h1
  simpa using h1.symm

end Morphisms

section SchemeLevel

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The projection from an affine cone to its base. -/
noncomputable def projection (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- The vertex section of a cone, determined by its augmentation. -/
noncomputable def vertexSection (ε : S →ₐ[R] R) :
    Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom ε.toRingHom)

/-- The contraction of a cone by a scalar, as an endomorphism of the total space. -/
noncomputable def contractionMap (ψ : S →ₐ[R] Polynomial S) (r : R) :
    Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (contraction ψ r).toRingHom)

/-- The vertex is a section of the projection. -/
theorem vertexSection_comp_projection (ε : S →ₐ[R] R) :
    vertexSection ε ≫ projection R S = 𝟙 _ := by
  rw [vertexSection, projection, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun r => ε.commutes r)

/-- Contracting by `1` is the identity morphism. -/
theorem contractionMap_one {ψ : S →ₐ[R] Polynomial S} (h : IsConeCoaction ψ) :
    contractionMap ψ (1 : R) = 𝟙 _ := by
  rw [contractionMap, contraction_one h, ← Spec.map_id]
  rfl

/-- Contracting by a product is the composition of the two contractions. -/
theorem contractionMap_mul {ψ : S →ₐ[R] Polynomial S} (h : IsConeCoaction ψ) (r r' : R) :
    contractionMap ψ (r * r') = contractionMap ψ r ≫ contractionMap ψ r' := by
  rw [contractionMap, contractionMap, contractionMap, contraction_mul h, ← Spec.map_comp]
  rfl

/-- Contracting by `0` is the projection followed by the vertex. -/
theorem contractionMap_zero {ψ : S →ₐ[R] Polynomial S} {ε : S →ₐ[R] R} (h : IsConeVertex ψ ε) :
    contractionMap ψ (0 : R) = projection R S ≫ vertexSection ε := by
  rw [contractionMap, h, projection, vertexSection, ← Spec.map_comp]
  rfl

/-- The vertex is a fixed point of every contraction. -/
theorem vertexSection_comp_contractionMap {ψ : S →ₐ[R] Polynomial S} {ε : S →ₐ[R] R}
    (hψ : IsConeCoaction ψ) (h : IsConeVertex ψ ε) (r : R) :
    vertexSection ε ≫ contractionMap ψ r = vertexSection ε := by
  rw [vertexSection, contractionMap, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (h.comp_contraction hψ r))

end SchemeLevel

section ConeHomTransport

variable {R S S' : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']

/-- The counit law for a coaction transported along a morphism of cones. -/
theorem IsConeHom.comp_counit {ψ : S →ₐ[R] Polynomial S} {ψ' : S' →ₐ[R] Polynomial S'}
    {φ : S →ₐ[R] S'} (h : IsConeHom ψ ψ' φ) (hψ : IsConeCoaction ψ) :
    ((evalHom (AlgHom.id R S') (1 : S')).comp ψ').comp φ = φ := by
  rw [AlgHom.comp_assoc, ← h, ← AlgHom.comp_assoc, evalHom_comp_mapAlgHom, AlgHom.id_comp]
  exact hψ.scale_one φ

/-- The coassociativity law for a coaction transported along a morphism of cones. -/
theorem IsConeHom.comp_coassoc {ψ : S →ₐ[R] Polynomial S} {ψ' : S' →ₐ[R] Polynomial S'}
    {φ : S →ₐ[R] S'} (h : IsConeHom ψ ψ' φ) (hψ : IsConeCoaction ψ) :
    ((Polynomial.mapAlgHom ψ').comp ψ').comp φ = (comul.comp ψ').comp φ := by
  have e1 : ((Polynomial.mapAlgHom ψ').comp ψ').comp φ =
      (Polynomial.mapAlgHom (Polynomial.mapAlgHom φ)).comp (comul.comp ψ) := by
    rw [AlgHom.comp_assoc, ← h, ← AlgHom.comp_assoc, mapAlgHom_comp, ← h, ← mapAlgHom_comp,
      AlgHom.comp_assoc, hψ.coassoc]
  have e2 : (comul.comp ψ').comp φ =
      (Polynomial.mapAlgHom (Polynomial.mapAlgHom φ)).comp (comul.comp ψ) := by
    rw [AlgHom.comp_assoc, ← h, ← AlgHom.comp_assoc, comul_comp_mapAlgHom, AlgHom.comp_assoc]
  rw [e1, e2]

/-- A coaction admitting an injective morphism to a cone is itself a cone: a subalgebra of a
cone stable under the contraction action is again a cone. -/
theorem isConeCoaction_of_injective {ψ : S →ₐ[R] Polynomial S} {ψ' : S' →ₐ[R] Polynomial S'}
    {φ : S →ₐ[R] S'} (h : IsConeHom ψ ψ' φ) (hφ : Function.Injective φ)
    (h' : IsConeCoaction ψ') : IsConeCoaction ψ where
  counit := by
    refine AlgHom.ext fun s => hφ ?_
    have e1 : φ.comp (evalHom (AlgHom.id R S) (1 : S)) = evalHom φ (1 : S') := by
      rw [comp_evalHom, AlgHom.comp_id, map_one]
    have e2 : (evalHom (AlgHom.id R S') (1 : S')).comp (Polynomial.mapAlgHom φ) =
        evalHom φ (1 : S') := by
      rw [evalHom_comp_mapAlgHom, AlgHom.id_comp]
    calc φ (evalHom (AlgHom.id R S) (1 : S) (ψ s))
        = evalHom φ (1 : S') (ψ s) := AlgHom.congr_fun e1 _
      _ = evalHom (AlgHom.id R S') (1 : S') (Polynomial.mapAlgHom φ (ψ s)) :=
          (AlgHom.congr_fun e2 _).symm
      _ = evalHom (AlgHom.id R S') (1 : S') (ψ' (φ s)) := by
          rw [show Polynomial.mapAlgHom φ (ψ s) = ψ' (φ s) from AlgHom.congr_fun h s]
      _ = φ s := AlgHom.congr_fun h'.counit (φ s)
  coassoc := by
    have hL : (Polynomial.mapAlgHom (Polynomial.mapAlgHom φ)).comp
        ((Polynomial.mapAlgHom ψ).comp ψ) = (comul.comp ψ').comp φ := by
      rw [← AlgHom.comp_assoc, mapAlgHom_comp, h, ← mapAlgHom_comp, AlgHom.comp_assoc, h,
        ← AlgHom.comp_assoc, h'.coassoc]
    have hR : (Polynomial.mapAlgHom (Polynomial.mapAlgHom φ)).comp (comul.comp ψ) =
        (comul.comp ψ').comp φ := by
      rw [← AlgHom.comp_assoc, ← comul_comp_mapAlgHom, AlgHom.comp_assoc, h,
        ← AlgHom.comp_assoc]
    have hinj : Function.Injective
        (Polynomial.mapAlgHom (Polynomial.mapAlgHom φ)) := fun _ _ hpq =>
      Polynomial.map_injective _
        (Polynomial.map_injective (φ : S →+* S') hφ) hpq
    refine AlgHom.ext fun s => hinj ?_
    exact (AlgHom.congr_fun hL s).trans (AlgHom.congr_fun hR s).symm

end ConeHomTransport

section Product

open scoped TensorProduct

variable {R S S' : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']

/-- Two algebra maps out of a tensor product agree as soon as they agree on both factors. -/
theorem tensor_ext {C : Type*} [CommRing C] [Algebra R C] {f g : (S ⊗[R] S') →ₐ[R] C}
    (hL : f.comp Algebra.TensorProduct.includeLeft =
      g.comp Algebra.TensorProduct.includeLeft)
    (hR : f.comp Algebra.TensorProduct.includeRight =
      g.comp Algebra.TensorProduct.includeRight) : f = g := by
  refine Algebra.TensorProduct.ext' fun a b => ?_
  have ha := AlgHom.congr_fun hL a
  have hb := AlgHom.congr_fun hR b
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply] at ha hb
  have h1 : (a ⊗ₜ[R] b : S ⊗[R] S') = (a ⊗ₜ[R] (1 : S')) * ((1 : S) ⊗ₜ[R] b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h1, map_mul, map_mul, ha, hb]

/-- The contraction coaction on the product of two cones over the same base: the coordinate
algebra is the tensor product `S ⊗[R] S'` with the total grading. -/
noncomputable def tensorCoaction (ψ : S →ₐ[R] Polynomial S) (ψ' : S' →ₐ[R] Polynomial S') :
    (S ⊗[R] S') →ₐ[R] Polynomial (S ⊗[R] S') :=
  Algebra.TensorProduct.lift
    ((Polynomial.mapAlgHom
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S')).comp ψ)
    ((Polynomial.mapAlgHom
      (Algebra.TensorProduct.includeRight : S' →ₐ[R] S ⊗[R] S')).comp ψ')
    fun _ _ => Commute.all _ _

/-- The first projection of a product of cones is a morphism of cones. -/
theorem isConeHom_includeLeft (ψ : S →ₐ[R] Polynomial S) (ψ' : S' →ₐ[R] Polynomial S') :
    IsConeHom ψ (tensorCoaction ψ ψ')
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S') :=
  (Algebra.TensorProduct.lift_comp_includeLeft _ _ _).symm

/-- The second projection of a product of cones is a morphism of cones. -/
theorem isConeHom_includeRight (ψ : S →ₐ[R] Polynomial S) (ψ' : S' →ₐ[R] Polynomial S') :
    IsConeHom ψ' (tensorCoaction ψ ψ')
      (Algebra.TensorProduct.includeRight : S' →ₐ[R] S ⊗[R] S') :=
  (Algebra.TensorProduct.lift_comp_includeRight' _ _ _).symm

/-- The product of two cones is a cone. -/
theorem isConeCoaction_tensorCoaction {ψ : S →ₐ[R] Polynomial S} {ψ' : S' →ₐ[R] Polynomial S'}
    (h : IsConeCoaction ψ) (h' : IsConeCoaction ψ') : IsConeCoaction (tensorCoaction ψ ψ') where
  counit := by
    refine tensor_ext ?_ ?_
    · rw [AlgHom.id_comp]
      exact (isConeHom_includeLeft ψ ψ').comp_counit h
    · rw [AlgHom.id_comp]
      exact (isConeHom_includeRight ψ ψ').comp_counit h'
  coassoc := by
    refine tensor_ext ?_ ?_
    · exact (isConeHom_includeLeft ψ ψ').comp_coassoc h
    · exact (isConeHom_includeRight ψ ψ').comp_coassoc h'

/-- The vertex of a product of cones is the product of the vertices. -/
theorem isConeVertex_tensorCoaction {ψ : S →ₐ[R] Polynomial S} {ψ' : S' →ₐ[R] Polynomial S'}
    {ε : S →ₐ[R] R} {ε' : S' →ₐ[R] R} (hv : IsConeVertex ψ ε) (hv' : IsConeVertex ψ' ε') :
    IsConeVertex (tensorCoaction ψ ψ')
      (Algebra.TensorProduct.lift ε ε' fun _ _ => Commute.all _ _) := by
  refine tensor_ext ?_ ?_
  · rw [← (isConeHom_includeLeft ψ ψ').comp_contraction, hv, AlgHom.comp_assoc,
      Algebra.TensorProduct.lift_comp_includeLeft, ← AlgHom.comp_assoc]
    rfl
  · rw [← (isConeHom_includeRight ψ ψ').comp_contraction, hv', AlgHom.comp_assoc,
      Algebra.TensorProduct.lift_comp_includeRight', ← AlgHom.comp_assoc]
    congr 1
    exact AlgHom.ext fun r =>
      (Algebra.TensorProduct.includeRight : S' →ₐ[R] S ⊗[R] S').commutes r

end Product

section ClosedSubcone

variable {R S S' : Type u} [CommRing R] [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']

/-- A surjective morphism of cones realises the target as a closed subcone of the source. -/
theorem isClosedImmersion_of_surjective (φ : S →ₐ[R] S') (hφ : Function.Surjective φ) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
  IsClosedImmersion.spec_of_surjective _ hφ

end ClosedSubcone

section AbelianHull

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (ψ : S →ₐ[R] Polynomial S)

/-- The abelian hull of a cone: the abelian cone `Spec Sym(S₁)` on the degree-one part,
together with the canonical map of coordinate algebras `Sym(S₁) → S`. -/
noncomputable def abelianHull : SymmetricAlgebra R (homogeneous ψ 1) →ₐ[R] S :=
  SymmetricAlgebra.lift (homogeneous ψ 1).subtype

@[simp]
theorem abelianHull_ι (x : homogeneous ψ 1) :
    abelianHull ψ (SymmetricAlgebra.ι R (homogeneous ψ 1) x) = (x : S) :=
  SymmetricAlgebra.lift_ι_apply _ _

/-- The abelian hull map is a morphism of cones. -/
theorem isConeHom_abelianHull :
    IsConeHom (symCoaction R (homogeneous ψ 1)) ψ (abelianHull ψ) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
  change Polynomial.mapAlgHom (abelianHull ψ)
      (symCoaction R (homogeneous ψ 1) (SymmetricAlgebra.ι R (homogeneous ψ 1) x)) =
    ψ (abelianHull ψ (SymmetricAlgebra.ι R (homogeneous ψ 1) x))
  have hx : ψ (x : S) = Polynomial.C (x : S) * Polynomial.X ^ 1 := mem_homogeneous.mp x.2
  rw [symCoaction_ι, abelianHull_ι, hx, pow_one]
  simp

/-- A cone generated in degree one is a quotient of its abelian hull. -/
theorem abelianHull_surjective (h : IsGeneratedInDegreeOne ψ) :
    Function.Surjective (abelianHull ψ) := by
  rw [← AlgHom.range_eq_top, eq_top_iff, ← h]
  refine Algebra.adjoin_le ?_
  rintro s hs
  exact ⟨SymmetricAlgebra.ι R (homogeneous ψ 1) ⟨s, hs⟩, by simp⟩

/-- A cone generated in degree one is a closed subcone of its abelian hull. -/
theorem isClosedImmersion_abelianHull (h : IsGeneratedInDegreeOne ψ) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (abelianHull ψ).toRingHom)) :=
  isClosedImmersion_of_surjective _ (abelianHull_surjective ψ h)

end AbelianHull

section Quotient

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The coaction induced on a quotient of a cone by an ideal which is homogeneous, in the sense
that the coaction of each of its elements dies in the quotient.  Geometrically this is a closed
subcone of `Spec S`. -/
noncomputable def quotientCoaction (ψ : S →ₐ[R] Polynomial S) (J : Ideal S)
    (hJ : ∀ x ∈ J,
      (Polynomial.mapAlgHom (Ideal.Quotient.mkₐ R J)).comp ψ x = 0) :
    (S ⧸ J) →ₐ[R] Polynomial (S ⧸ J) :=
  Ideal.Quotient.liftₐ J ((Polynomial.mapAlgHom (Ideal.Quotient.mkₐ R J)).comp ψ) hJ

/-- The quotient map is a morphism of cones. -/
theorem isConeHom_quotientCoaction (ψ : S →ₐ[R] Polynomial S) (J : Ideal S)
    (hJ : ∀ x ∈ J, (Polynomial.mapAlgHom (Ideal.Quotient.mkₐ R J)).comp ψ x = 0) :
    IsConeHom ψ (quotientCoaction ψ J hJ) (Ideal.Quotient.mkₐ R J) :=
  (Ideal.Quotient.liftₐ_comp J _ hJ).symm

/-- A homogeneous quotient of a cone is a cone. -/
theorem isConeCoaction_quotientCoaction {ψ : S →ₐ[R] Polynomial S} (h : IsConeCoaction ψ)
    (J : Ideal S)
    (hJ : ∀ x ∈ J, (Polynomial.mapAlgHom (Ideal.Quotient.mkₐ R J)).comp ψ x = 0) :
    IsConeCoaction (quotientCoaction ψ J hJ) where
  counit := by
    refine AlgHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact AlgHom.congr_fun ((isConeHom_quotientCoaction ψ J hJ).comp_counit h) y
  coassoc := by
    refine AlgHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact AlgHom.congr_fun ((isConeHom_quotientCoaction ψ J hJ).comp_coassoc h) y

end Quotient

section AffineLine

variable (R : Type*) [CommRing R]

/-- The comultiplication is itself the contraction coaction of the affine line `Spec R[t]`,
graded by the degree. -/
theorem isConeCoaction_comul :
    IsConeCoaction (comul : Polynomial R →ₐ[R] Polynomial (Polynomial R)) where
  counit := Polynomial.algHom_ext' (AlgHom.ext fun a => by simp) (by simp)
  coassoc := by
    refine Polynomial.algHom_ext' (AlgHom.ext fun a => by simp) ?_
    simp only [AlgHom.comp_apply, comul_X, map_mul, Polynomial.coe_mapAlgHom, Polynomial.map_C,
      Polynomial.map_X, comul_C, RingHom.coe_coe]
    ring

/-- The variable `t` is homogeneous of degree one for the affine line. -/
theorem X_mem_homogeneous_one :
    (Polynomial.X : Polynomial R) ∈ homogeneous (comul : Polynomial R →ₐ[R] _) 1 := by
  rw [mem_homogeneous, comul_X, pow_one]

end AffineLine

section MvPolynomialCone

variable (R : Type*) [CommRing R] (σ : Type*)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Affine space `𝔸^σ` over `Spec R`, with the grading by total degree, is a cone. -/
theorem isConeCoaction_mvPolynomial :
    IsConeCoaction (gradedCoaction (MvPolynomial.homogeneousSubmodule σ R)) :=
  isConeCoaction_gradedCoaction _

/-- The degree-`n` part of affine space is the space of homogeneous polynomials of degree `n`. -/
theorem homogeneous_mvPolynomial (n : ℕ) :
    homogeneous (gradedCoaction (MvPolynomial.homogeneousSubmodule σ R)) n =
      MvPolynomial.homogeneousSubmodule σ R n :=
  homogeneous_gradedCoaction _ n

end MvPolynomialCone

section ReesNormalCone

variable (R : Type u) [CommRing R] (I : Ideal R)

/-- The inclusion of the Rees algebra into `R[t]`, coefficientwise on polynomials, is
injective. -/
theorem mapAlgHom_reesVal_injective :
    Function.Injective
      (Polynomial.mapAlgHom ((reesAlgebra I).val : reesAlgebra I →ₐ[R] Polynomial R)) :=
  fun _ _ hpq =>
    Polynomial.map_injective ((reesAlgebra I).val : reesAlgebra I →+* Polynomial R)
      Subtype.val_injective hpq

/-- The comultiplication of `R[t]` preserves the Rees algebra coefficientwise: the degree-`n`
coefficient of `q` is multiplied by `tⁿ`, and `Iⁿ tⁿ` lies in the Rees algebra. -/
theorem comul_mem_range_rees (q : reesAlgebra I) :
    comul (R := R) (q : Polynomial R) ∈
      AlgHom.range
        (Polynomial.mapAlgHom ((reesAlgebra I).val : reesAlgebra I →ₐ[R] Polynomial R)) := by
  have hl : comul (R := R) (q : Polynomial R) ∈
      Polynomial.lifts ((reesAlgebra I).val : reesAlgebra I →+* Polynomial R) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [comul_coeff, Polynomial.C_mul_X_pow_eq_monomial]
    refine ⟨⟨Polynomial.monomial n ((q : Polynomial R).coeff n), ?_⟩, rfl⟩
    rw [mem_reesAlgebra_iff]
    intro k
    rw [Polynomial.coeff_monomial]
    split_ifs with hk
    · subst hk
      exact (mem_reesAlgebra_iff I (q : Polynomial R)).mp q.2 n
    · exact zero_mem _
  obtain ⟨P, hP⟩ := (Polynomial.mem_lifts _).mp hl
  exact ⟨P, hP⟩

/-- The contraction coaction of the Rees cone `Spec Rees_I(R)`: the degree-`n` part `Iⁿ tⁿ` is
scaled by the `n`-th power of the contraction parameter. -/
noncomputable def reesCoaction : reesAlgebra I →ₐ[R] Polynomial (reesAlgebra I) :=
  (AlgEquiv.ofInjective _ (mapAlgHom_reesVal_injective R I)).symm.toAlgHom.comp
    (AlgHom.codRestrict (comul.comp ((reesAlgebra I).val : reesAlgebra I →ₐ[R] Polynomial R))
      _ (comul_mem_range_rees R I))

/-- The Rees coaction is the restriction of the comultiplication of `R[t]`; equivalently, the
inclusion of the Rees algebra into the affine line cone is a morphism of cones. -/
theorem isConeHom_reesVal :
    IsConeHom (reesCoaction R I) (comul : Polynomial R →ₐ[R] Polynomial (Polynomial R))
      ((reesAlgebra I).val : reesAlgebra I →ₐ[R] Polynomial R) :=
  AlgHom.ext fun q =>
    congrArg Subtype.val
      ((AlgEquiv.ofInjective _ (mapAlgHom_reesVal_injective R I)).apply_symm_apply
        ⟨comul (q : Polynomial R), comul_mem_range_rees R I q⟩)

/-- The Rees cone is a cone. -/
theorem isConeCoaction_reesCoaction : IsConeCoaction (reesCoaction R I) :=
  isConeCoaction_of_injective (isConeHom_reesVal R I) Subtype.val_injective
    (isConeCoaction_comul R)

/-- The ideal `I · Rees_I(R)` defining the associated graded ring is homogeneous: the coaction
of each of its elements vanishes in the quotient. -/
theorem reesCoaction_mem_ker (x : reesAlgebra I)
    (hx : x ∈ Ideal.map (algebraMap R (reesAlgebra I)) I) :
    (Polynomial.mapAlgHom
        (Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R (reesAlgebra I)) I))).comp
      (reesCoaction R I) x = 0 := by
  have hle : Ideal.map (algebraMap R (reesAlgebra I)) I ≤
      RingHom.ker (((Polynomial.mapAlgHom
        (Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R (reesAlgebra I)) I))).comp
        (reesCoaction R I)) : reesAlgebra I →+*
          Polynomial (reesAlgebra I ⧸ Ideal.map (algebraMap R (reesAlgebra I)) I)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change ((Polynomial.mapAlgHom
      (Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R (reesAlgebra I)) I))).comp
      (reesCoaction R I)) (algebraMap R (reesAlgebra I) s) = 0
    rw [AlgHom.comp_apply, AlgHom.commutes, AlgHom.commutes, Polynomial.algebraMap_apply]
    have hzero : algebraMap R
        (reesAlgebra I ⧸ Ideal.map (algebraMap R (reesAlgebra I)) I) s = 0 := by
      rw [IsScalarTower.algebraMap_apply R (reesAlgebra I)
        (reesAlgebra I ⧸ Ideal.map (algebraMap R (reesAlgebra I)) I),
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hs
    rw [hzero, map_zero]
  exact hle hx

/-- The contraction coaction of the affine normal cone `Spec gr_I(R)`, obtained from the Rees
cone by passing to the quotient by the homogeneous ideal `I · Rees_I(R)`.  Its carrier is
definitionally `AffineNormalCone.associatedGradedRing R I`. -/
noncomputable def normalConeCoaction :=
  quotientCoaction (reesCoaction R I) (Ideal.map (algebraMap R (reesAlgebra I)) I)
    (reesCoaction_mem_ker R I)

/-- The affine normal cone `Spec gr_I(R)` is a cone. -/
theorem isConeCoaction_normalConeCoaction : IsConeCoaction (normalConeCoaction R I) :=
  isConeCoaction_quotientCoaction (isConeCoaction_reesCoaction R I) _ _

/-- The quotient map from the Rees cone to the affine normal cone is a morphism of cones. -/
theorem isConeHom_normalConeCoaction :
    IsConeHom (reesCoaction R I) (normalConeCoaction R I)
      (Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R (reesAlgebra I)) I)) :=
  isConeHom_quotientCoaction _ _ _

/-- Contracting the affine line by `r` is substitution of `r t` for `t`, i.e. the scaling map
used to build the Rees contraction in `Cones/Affine.lean`. -/
theorem evalHom_comp_comul (r : R) :
    (evalHom (AlgHom.id R (Polynomial R)) (Polynomial.C r)).comp comul =
      AffineNormalCone.reesScaleAux R r := by
  refine Polynomial.algHom_ext' (AlgHom.ext fun a => ?_) ?_
  · change evalHom (AlgHom.id R (Polynomial R)) (Polynomial.C r)
      (comul (Polynomial.C a)) = AffineNormalCone.reesScaleAux R r (Polynomial.C a)
    rw [comul_C, evalHom_C, AffineNormalCone.reesScaleAux]
    simp
  · change evalHom (AlgHom.id R (Polynomial R)) (Polynomial.C r)
      (comul (Polynomial.X : Polynomial R)) =
      AffineNormalCone.reesScaleAux R r (Polynomial.X : Polynomial R)
    rw [comul_X, map_mul, evalHom_C, evalHom_X, AffineNormalCone.reesScaleAux,
      Polynomial.aeval_X, mul_comm]
    rfl

/-- The abstract contraction of the Rees cone is the scaling action constructed in
`Cones/Affine.lean`. -/
theorem contraction_reesCoaction (r : R) :
    contraction (reesCoaction R I) r = AffineNormalCone.reesScale R I r := by
  refine AlgHom.ext fun q => Subtype.val_injective ?_
  have e1 : ((reesAlgebra I).val : reesAlgebra I →ₐ[R] Polynomial R).comp
      (evalHom (AlgHom.id R (reesAlgebra I)) (algebraMap R (reesAlgebra I) r)) =
      evalHom ((reesAlgebra I).val : reesAlgebra I →ₐ[R] Polynomial R) (Polynomial.C r) := by
    rw [comp_evalHom, AlgHom.comp_id]
    rfl
  have e2 : (evalHom (AlgHom.id R (Polynomial R)) (Polynomial.C r)).comp
      (Polynomial.mapAlgHom ((reesAlgebra I).val : reesAlgebra I →ₐ[R] Polynomial R)) =
      evalHom ((reesAlgebra I).val : reesAlgebra I →ₐ[R] Polynomial R) (Polynomial.C r) := by
    rw [evalHom_comp_mapAlgHom, AlgHom.id_comp]
  calc ((reesAlgebra I).val : reesAlgebra I →ₐ[R] Polynomial R) (contraction (reesCoaction R I) r q)
      = evalHom ((reesAlgebra I).val : reesAlgebra I →ₐ[R] Polynomial R) (Polynomial.C r)
          (reesCoaction R I q) := AlgHom.congr_fun e1 _
    _ = evalHom (AlgHom.id R (Polynomial R)) (Polynomial.C r)
          (Polynomial.mapAlgHom ((reesAlgebra I).val : reesAlgebra I →ₐ[R] Polynomial R)
            (reesCoaction R I q)) := (AlgHom.congr_fun e2 _).symm
    _ = evalHom (AlgHom.id R (Polynomial R)) (Polynomial.C r) (comul (q : Polynomial R)) := by
          rw [show Polynomial.mapAlgHom
              ((reesAlgebra I).val : reesAlgebra I →ₐ[R] Polynomial R) (reesCoaction R I q) =
              comul (q : Polynomial R) from AlgHom.congr_fun (isConeHom_reesVal R I) q]
    _ = AffineNormalCone.reesScaleAux R r (q : Polynomial R) :=
          AlgHom.congr_fun (evalHom_comp_comul R r) _
    _ = ((reesAlgebra I).val : reesAlgebra I →ₐ[R] Polynomial R)
          (AffineNormalCone.reesScale R I r q) := rfl

/-- The abstract contraction of the affine normal cone is the scaling action on the associated
graded ring constructed in `Cones/Affine.lean`. -/
theorem contraction_normalConeCoaction (r : R)
    (x : AffineNormalCone.associatedGradedRing R I) :
    contraction (normalConeCoaction R I) r x = AffineNormalCone.associatedGradedScale R I r x := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hcomm := AlgHom.congr_fun
    ((isConeHom_normalConeCoaction R I).comp_contraction r) q
  rw [AffineNormalCone.associatedGradedScale_mk, ← contraction_reesCoaction]
  exact hcomm.symm

end ReesNormalCone

section VectorBundle

open scoped TensorProduct

variable (R : Type u) [CommRing R] (F : Type u) [AddCommGroup F] [Module R F]

/-- The functor of points of the vector bundle `C(F) = Spec Sym(F)`: for every `R`-algebra `B`,
the `B`-points of `C(F)` are the `R`-linear maps `F →ₗ[R] B`.  This is the universal property of
the symmetric algebra. -/
noncomputable def pointsEquiv (B : Type*) [CommRing B] [Algebra R B] :
    (SymmetricAlgebra R F →ₐ[R] B) ≃ (F →ₗ[R] B) :=
  SymmetricAlgebra.lift.symm

@[simp]
theorem pointsEquiv_symm_apply {B : Type*} [CommRing B] [Algebra R B] (l : F →ₗ[R] B) (m : F) :
    (pointsEquiv R F B).symm l (SymmetricAlgebra.ι R F m) = l m :=
  SymmetricAlgebra.lift_ι_apply _ _

/-- Under the functor of points, the contraction action on `C(F)` is scalar multiplication on
linear maps. -/
theorem scale_symCoaction {B : Type*} [CommRing B] [Algebra R B] (l : F →ₗ[R] B) (b : B) :
    scale (symCoaction R F) ((pointsEquiv R F B).symm l) b =
      (pointsEquiv R F B).symm (b • l) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
  change scale (symCoaction R F) ((pointsEquiv R F B).symm l) b (SymmetricAlgebra.ι R F m) =
    (pointsEquiv R F B).symm (b • l) (SymmetricAlgebra.ι R F m)
  rw [scale, AlgHom.comp_apply, symCoaction_ι, map_mul, evalHom_C, evalHom_X,
    pointsEquiv_symm_apply, pointsEquiv_symm_apply, LinearMap.smul_apply, smul_eq_mul, mul_comm]

/-- The coordinate ring of the vector bundle attached to a module with a finite basis is a
smooth `R`-algebra, because it is a polynomial algebra. -/
theorem smooth_symmetricAlgebra_of_basis {κ : Type u} [Finite κ] (b : Module.Basis κ R F) :
    Algebra.Smooth R (SymmetricAlgebra R F) := by
  have hpoly : Algebra.Smooth R (MvPolynomial κ R) :=
    { formallySmooth := inferInstance, finitePresentation := inferInstance }
  exact hpoly.of_equiv (SymmetricAlgebra.equivMvPolynomial b).symm

/-- The coordinate ring of the vector bundle on a finite free module is a smooth algebra. -/
theorem smooth_symmetricAlgebra [Module.Free R F] [Module.Finite R F] :
    Algebra.Smooth R (SymmetricAlgebra R F) :=
  smooth_symmetricAlgebra_of_basis R F (Module.Free.chooseBasis R F)

/-- The vector bundle `C(F) = Spec Sym(F)` is smooth over its base when `F` is finite free. -/
theorem smooth_projection [Module.Free R F] [Module.Finite R F] :
    AlgebraicGeometry.Smooth (projection R (SymmetricAlgebra R F)) := by
  refine AlgebraicGeometry.HasRingHomProperty.Spec_iff.2 ?_
  exact RingHom.smooth_algebraMap.2 (smooth_symmetricAlgebra R F)

variable (B : Type u) [CommRing B] [Algebra R B]

/-- The `R`-linear map sending `m` to the generator `1 ⊗ m` of the base changed bundle. -/
noncomputable def baseChangeGen :
    F →ₗ[R] SymmetricAlgebra B (B ⊗[R] F) :=
  ((SymmetricAlgebra.ι B (B ⊗[R] F)).restrictScalars R).comp (TensorProduct.mk R B F 1)

/-- The comparison map from the base changed bundle to the base change of the bundle. -/
noncomputable def baseChangeForward :
    SymmetricAlgebra B (B ⊗[R] F) →ₐ[B] B ⊗[R] SymmetricAlgebra R F :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι R F).baseChange B)

/-- The comparison map from the base change of the bundle to the base changed bundle. -/
noncomputable def baseChangeBackward :
    B ⊗[R] SymmetricAlgebra R F →ₐ[B] SymmetricAlgebra B (B ⊗[R] F) :=
  Algebra.TensorProduct.lift (Algebra.ofId B (SymmetricAlgebra B (B ⊗[R] F)))
    (SymmetricAlgebra.lift (baseChangeGen R F B)) fun _ _ => Commute.all _ _

/-- Base change of vector bundles: `C(F) ×_{Spec R} Spec B` is the vector bundle attached to
the base changed module `B ⊗[R] F`. -/
noncomputable def baseChangeEquiv :
    SymmetricAlgebra B (B ⊗[R] F) ≃ₐ[B] B ⊗[R] SymmetricAlgebra R F := by
  refine AlgEquiv.ofAlgHom (baseChangeForward R F B) (baseChangeBackward R F B) ?_ ?_
  · refine Algebra.TensorProduct.ext' fun b s => ?_
    have key : ((baseChangeForward R F B).restrictScalars R).comp
        (SymmetricAlgebra.lift (baseChangeGen R F B)) =
        (Algebra.TensorProduct.includeRight : SymmetricAlgebra R F →ₐ[R] _) := by
      refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
      change baseChangeForward R F B
          (SymmetricAlgebra.lift (baseChangeGen R F B) (SymmetricAlgebra.ι R F m)) = _
      rw [SymmetricAlgebra.lift_ι_apply]
      change baseChangeForward R F B
          (SymmetricAlgebra.ι B (B ⊗[R] F) (1 ⊗ₜ[R] m)) = (1 : B) ⊗ₜ[R] _
      rw [baseChangeForward, SymmetricAlgebra.lift_ι_apply, LinearMap.baseChange_tmul]
    have hs : baseChangeForward R F B (SymmetricAlgebra.lift (baseChangeGen R F B) s) =
        (1 : B) ⊗ₜ[R] s := AlgHom.congr_fun key s
    change baseChangeForward R F B (baseChangeBackward R F B (b ⊗ₜ[R] s)) = _
    rw [baseChangeBackward, Algebra.TensorProduct.lift_tmul, map_mul, hs]
    simp only [Algebra.ofId_apply, AlgHom.commutes, AlgHom.id_apply,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul, Algebra.algebraMap_self, RingHom.id_apply]
  · refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    change baseChangeBackward R F B (baseChangeForward R F B
      (SymmetricAlgebra.ι B (B ⊗[R] F) x)) = SymmetricAlgebra.ι B (B ⊗[R] F) x
    rw [baseChangeForward, SymmetricAlgebra.lift_ι_apply]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
      rw [LinearMap.baseChange_tmul, baseChangeBackward, Algebra.TensorProduct.lift_tmul,
        SymmetricAlgebra.lift_ι_apply]
      change (algebraMap B (SymmetricAlgebra B (B ⊗[R] F))) b *
        SymmetricAlgebra.ι B (B ⊗[R] F) (1 ⊗ₜ[R] m) = _
      rw [← Algebra.smul_def, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

end VectorBundle

end GradedCone

end GromovWitten.AlgebraicGeometry
