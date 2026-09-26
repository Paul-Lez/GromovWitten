/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import GromovWitten.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# The affine-linear stabilizer of a polynomial map

For a nonconstant polynomial `f : k[T]`, this file constructs the coordinate algebra of
the affine-linear substitutions `T ↦ aT+b` preserving `f`.  The presentation is by three
coordinates `a,b,c`, with `ac=1` recording the inverse of `a`; coefficient equations for
`f(aT+b)-f(T)` cut out the stabilizer.  The construction is fibrewise over a field and
retains nilpotents in positive characteristic.
-/

namespace GromovWitten.AlgebraicGeometry
namespace PolynomialAutomorphisms

open Polynomial

universe u v

variable {k : Type u} [Field k]

noncomputable section

private abbrev Variable : Type := Fin 3

private abbrev coefficientRing (k : Type u) [CommSemiring k] := MvPolynomial (Variable) k

private def aVar (k : Type u) [CommSemiring k] : MvPolynomial Variable k := MvPolynomial.X 0
private def bVar (k : Type u) [CommSemiring k] : MvPolynomial Variable k := MvPolynomial.X 1
private def cVar (k : Type u) [CommSemiring k] : MvPolynomial Variable k := MvPolynomial.X 2

private def mappedPolynomial (f : k[X]) : (coefficientRing k)[X] :=
  f.map (algebraMap k (coefficientRing k))

private def substitutedPolynomial (f : k[X]) : (coefficientRing k)[X] :=
  (mappedPolynomial f).comp (C (aVar k) * X + C (bVar k))

private def coefficientRelation (f : k[X]) (i : ℕ) : coefficientRing k :=
  (substitutedPolynomial f - mappedPolynomial f).coeff i

private def relationSet (f : k[X]) : Set (coefficientRing k) :=
  insert (aVar k * cVar k - 1) (Set.range (coefficientRelation f))

def relationIdeal (f : k[X]) : Ideal (coefficientRing k) :=
  Ideal.span (relationSet f)

/-- The affine coordinate algebra of the affine-linear stabilizer of `f`. -/
def CoordinateRing (f : k[X]) : Type u := coefficientRing k ⧸ relationIdeal f

instance (f : k[X]) : CommRing (CoordinateRing f) :=
  Ideal.Quotient.commRing (relationIdeal f)
instance (f : k[X]) : Algebra k (CoordinateRing f) :=
  Ideal.Quotient.algebra k

def coord (f : k[X]) (i : Variable) : CoordinateRing f :=
  Ideal.Quotient.mk (relationIdeal f) (MvPolynomial.X i)

def coordA (f : k[X]) : CoordinateRing f := coord f 0
def coordB (f : k[X]) : CoordinateRing f := coord f 1
def coordC (f : k[X]) : CoordinateRing f := coord f 2

/-- A point of the stabilizer over a commutative `k`-algebra. -/
structure Point (f : k[X]) (S : Type v) [CommRing S] [Algebra k S] where
  scale : Sˣ
  translate : S
  preserves :
    (f.map (algebraMap k S)) =
      (f.map (algebraMap k S)).comp (C (scale : S) * X + C translate)

private def pointEval (f : k[X]) {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) : (coefficientRing k) →+* S :=
  MvPolynomial.eval₂Hom (algebraMap k S)
    (fun i => Fin.cases (p.scale : S)
      (fun i => Fin.cases p.translate (fun _ => (↑p.scale⁻¹ : S)) i) i)

private theorem pointEval_a (f : k[X]) {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) : pointEval f p (aVar k) = (p.scale : S) := by
  simp only [pointEval, aVar, MvPolynomial.eval₂Hom_X']
  rfl

private theorem pointEval_b (f : k[X]) {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) : pointEval f p (bVar k) = p.translate := by
  simp only [pointEval, bVar, MvPolynomial.eval₂Hom_X']
  rfl

private theorem pointEval_c (f : k[X]) {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) : pointEval f p (cVar k) = (↑p.scale⁻¹ : S) := by
  simp only [pointEval, cVar, MvPolynomial.eval₂Hom_X']
  rfl

private theorem pointEval_ac (f : k[X]) {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) : pointEval f p (aVar k * cVar k - 1) = 0 := by
  rw [map_sub, map_mul, pointEval_a, pointEval_c]
  simp

private theorem pointEval_substitution (f : k[X]) {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) :
    Polynomial.map (pointEval f p) (substitutedPolynomial f) =
      (f.map (algebraMap k S)).comp (C (p.scale : S) * X + C p.translate) := by
  rw [substitutedPolynomial, Polynomial.map_comp]
  rw [mappedPolynomial]
  have hC : (pointEval f p).comp (algebraMap k (coefficientRing k)) =
      algebraMap k S := by
    ext r
    simp [pointEval]
  rw [Polynomial.map_map, hC]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    pointEval_a, pointEval_b]

private theorem pointEval_mapped (f : k[X]) {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) :
    Polynomial.map (pointEval f p) (mappedPolynomial f) = f.map (algebraMap k S) := by
  rw [mappedPolynomial, Polynomial.map_map]
  have hC : (pointEval f p).comp (algebraMap k (coefficientRing k)) =
      algebraMap k S := by
    ext r
    simp [pointEval]
  rw [hC]

private theorem pointEval_rel (f : k[X]) {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) (i : ℕ) : pointEval f p (coefficientRelation f i) = 0 := by
  change pointEval f p ((substitutedPolynomial f - mappedPolynomial f).coeff i) = 0
  rw [← Polynomial.coeff_map]
  rw [Polynomial.map_sub]
  rw [pointEval_substitution, pointEval_mapped]
  exact congrArg (fun q : (S[X]) => q.coeff i) (sub_eq_zero.mpr p.preserves.symm)

private theorem pointEval_mem (f : k[X]) {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) : ∀ x ∈ relationIdeal f, pointEval f p x = 0 := by
  intro x hx
  refine (Ideal.mem_span x).mp hx (Ideal.comap (pointEval f p) ⊥) ?_
  intro x hx
  rcases hx with (rfl | ⟨i, rfl⟩)
  · exact pointEval_ac f p
  · exact pointEval_rel f p i

private def pointToAlgHom (f : k[X]) {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) : CoordinateRing f →ₐ[k] S :=
  { Ideal.Quotient.lift (relationIdeal f) (pointEval f p) (pointEval_mem f p) with
    commutes' := fun r => by
      change Ideal.Quotient.lift (relationIdeal f) (pointEval f p) (pointEval_mem f p)
        ((algebraMap k (CoordinateRing f)) r) = _
      change Ideal.Quotient.lift (relationIdeal f) (pointEval f p) (pointEval_mem f p)
        ((Ideal.Quotient.mk (relationIdeal f)) (MvPolynomial.C r)) = _
      rw [Ideal.Quotient.lift_mk]
      simp [pointEval] }

private theorem pointToAlgHom_coordA (f : k[X]) {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) : pointToAlgHom f p (coordA f) = p.scale := by
  change (Ideal.Quotient.lift (relationIdeal f) (pointEval f p) (pointEval_mem f p))
      ((Ideal.Quotient.mk (relationIdeal f)) (MvPolynomial.X 0)) = _
  rw [Ideal.Quotient.lift_mk]
  exact pointEval_a f p

private theorem pointToAlgHom_coordB (f : k[X]) {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) : pointToAlgHom f p (coordB f) = p.translate := by
  change (Ideal.Quotient.lift (relationIdeal f) (pointEval f p) (pointEval_mem f p))
      ((Ideal.Quotient.mk (relationIdeal f)) (MvPolynomial.X 1)) = _
  rw [Ideal.Quotient.lift_mk]
  exact pointEval_b f p

private theorem pointToAlgHom_coordC (f : k[X]) {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) : pointToAlgHom f p (coordC f) = (↑p.scale⁻¹ : S) := by
  change (Ideal.Quotient.lift (relationIdeal f) (pointEval f p) (pointEval_mem f p))
      ((Ideal.Quotient.mk (relationIdeal f)) (MvPolynomial.X 2)) = _
  rw [Ideal.Quotient.lift_mk]
  exact pointEval_c f p

/-- The coordinate algebra maps naturally to the stabilizer points. -/
def pointOfAlgHom (f : k[X]) {S : Type v} [CommRing S] [Algebra k S]
    (φ : CoordinateRing f →ₐ[k] S) : Point f S where
  scale := Units.mkOfMulEqOne (φ (coordA f)) (φ (coordC f)) (by
    have hrel : coordA f * coordC f - 1 = 0 := by
      change (Ideal.Quotient.mk (relationIdeal f))
        (aVar k * cVar k - 1) = 0
      apply (Ideal.Quotient.eq_zero_iff_mem).2
      apply Ideal.subset_span
      exact Set.mem_insert _ _
    have hrel' := congrArg φ hrel
    have hrel'' : φ (coordA f) * φ (coordC f) - 1 = 0 := by simpa using hrel'
    exact sub_eq_zero.mp hrel'')
  translate := φ (coordB f)
  preserves := by
    apply Polynomial.ext
    intro i
    let e : coefficientRing k →+* S := φ.toRingHom.comp (Ideal.Quotient.mk (relationIdeal f))
    have hcoeff : ∀ j, e (coefficientRelation f j) = 0 := by
      intro j
      have hm : coefficientRelation f j ∈ relationIdeal f := by
        apply Ideal.subset_span
        exact Set.mem_insert_of_mem
          _ (Set.mem_range_self j)
      have hz := (Ideal.Quotient.eq_zero_iff_mem (I := relationIdeal f)
        (a := coefficientRelation f j)).2 hm
      change φ ((Ideal.Quotient.mk (relationIdeal f)) (coefficientRelation f j)) = 0
      have hz' := congrArg φ hz
      change φ ((Ideal.Quotient.mk (relationIdeal f)) (coefficientRelation f j)) = φ 0 at hz'
      rw [map_zero] at hz'
      exact hz'
    have hpoly : Polynomial.map e
        (substitutedPolynomial f - mappedPolynomial f) = 0 := by
      apply Polynomial.ext
      intro j
      rw [Polynomial.coeff_map]
      simpa [coefficientRelation] using hcoeff j
    have hC : e.comp (algebraMap k (coefficientRing k)) = algebraMap k S := by
      ext r
      change φ ((algebraMap k (CoordinateRing f)) r) = (algebraMap k S) r
      exact φ.commutes r
    have hsub : Polynomial.map e (substitutedPolynomial f) =
        (f.map (algebraMap k S)).comp
          (C (φ (coordA f)) * X + C (φ (coordB f))) := by
      rw [substitutedPolynomial, Polynomial.map_comp, mappedPolynomial,
        Polynomial.map_map, hC]
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
      rfl
    have hmap : Polynomial.map e (mappedPolynomial f) = f.map (algebraMap k S) := by
      rw [mappedPolynomial, Polynomial.map_map, hC]
    rw [Polynomial.map_sub, hsub, hmap] at hpoly
    have heq := sub_eq_zero.mp hpoly
    have hcoeffeq := congrArg (fun q : S[X] => q.coeff i) heq
    change (f.map (algebraMap k S)).coeff i =
      ((f.map (algebraMap k S)).comp
        (C (φ (coordA f)) * X + C (φ (coordB f)))).coeff i
    exact hcoeffeq.symm

/-! ## Actual affine substitutions -/

private noncomputable instance unitInvertible {S : Type v} [CommRing S] (a : Sˣ) :
    Invertible (a : S) := a.invertible

/-- The polynomial-algebra automorphism `T ↦ aT+b` attached to a unit and a translation. -/
noncomputable def substitutionAlgEquiv {S : Type v} [CommRing S] (a : Sˣ) (b : S) :
    S[X] ≃ₐ[S] S[X] := by
  exact Polynomial.algEquivCMulXAddC (a : S) b

@[simp]
theorem substitutionAlgEquiv_apply_X {S : Type v} [CommRing S] (a : Sˣ) (b : S) :
    substitutionAlgEquiv a b X = C (a : S) * X + C b := by
  simp [substitutionAlgEquiv]

@[simp]
theorem substitutionAlgEquiv_symm_apply_X {S : Type v} [CommRing S] (a : Sˣ) (b : S) :
    (substitutionAlgEquiv a b).symm X = C (↑(a⁻¹) : S) * X - C ((↑(a⁻¹) : S) * b) := by
  change (Polynomial.algEquivCMulXAddC (a : S) b).symm X = _
  rw [Polynomial.algEquivCMulXAddC_symm_eq]
  simp [sub_eq_add_neg]

theorem substitution_composition_formula {S : Type v} [CommRing S]
    (a a' : Sˣ) (b b' : S) :
    (C (a' : S) * X + C b').comp (C (a : S) * X + C b) =
      C ((a' : S) * (a : S)) * X + C ((a' : S) * b + b') := by
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.X_comp]
  rw [mul_add, ← mul_assoc, ← Polynomial.C_mul, ← Polynomial.C_mul,
    add_assoc, ← Polynomial.C_add]

theorem substitution_composition_identity {S : Type v} [CommRing S]
    (a : Sˣ) (b : S) :
    (C (a : S) * X + C b).comp
        (C (↑(a⁻¹) : S) * X - C ((↑(a⁻¹) : S) * b)) = X := by
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.X_comp]
  rw [mul_sub, ← mul_assoc, ← Polynomial.C_mul]
  rw [← Polynomial.C_mul]
  simp

end
end PolynomialAutomorphisms
end GromovWitten.AlgebraicGeometry
