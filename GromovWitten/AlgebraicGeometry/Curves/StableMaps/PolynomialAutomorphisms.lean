/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import GromovWitten.Basic
import GromovWitten.AlgebraicGeometry.Curves.StableMaps.PolynomialAffineIntegral
import GromovWitten.AlgebraicGeometry.Curves.StableMaps.PolynomialAffineRigidity
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Unramified.Basic

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
open _root_.AlgebraicGeometry

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

@[ext]
theorem Point.ext {f : k[X]} {S : Type v} [CommRing S] [Algebra k S]
    {p q : Point f S} (hscale : p.scale = q.scale)
    (htranslate : p.translate = q.translate) : p = q := by
  cases p with
  | mk pscale ptranslate pp =>
    cases q with
    | mk qscale qtranslate qq =>
      simp_all

/-! A point is functorial for arbitrary maps of test algebras.  The map is
deliberately bundled as a `k`-algebra homomorphism: no scalar-tower instance
between the source and target test algebras is needed. -/

def Point.map (f : k[X]) {S T : Type*} [CommRing S] [CommRing T]
    [Algebra k S] [Algebra k T] (g : S →ₐ[k] T) (p : Point f S) : Point f T where
  scale := Units.map g.toRingHom p.scale
  translate := g p.translate
  preserves := by
    have h := congrArg (Polynomial.map g.toRingHom) p.preserves
    have hcomm : g.toRingHom.comp (algebraMap k S) = algebraMap k T := by
      ext r
      exact g.commutes r
    rw [Polynomial.map_map, Polynomial.map_comp, Polynomial.map_map] at h
    rw [hcomm] at h
    have hq : Polynomial.map g.toRingHom (C (p.scale : S) * X + C p.translate) =
        C (↑((Units.map (g.toRingHom : S →* T)) p.scale) : T) * X +
          C (g p.translate) := by
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_X, Polynomial.map_C, Units.coe_map]
      rfl
    rw [hq] at h
    exact h

def Point.one (f : k[X]) {S : Type v} [CommRing S] [Algebra k S] : Point f S where
  scale := 1
  translate := 0
  preserves := by simp

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

def pointToAlgHom (f : k[X]) {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) : CoordinateRing f →ₐ[k] S :=
  { Ideal.Quotient.lift (relationIdeal f) (pointEval f p) (pointEval_mem f p) with
    commutes' := fun r => by
      change Ideal.Quotient.lift (relationIdeal f) (pointEval f p) (pointEval_mem f p)
        ((algebraMap k (CoordinateRing f)) r) = _
      change Ideal.Quotient.lift (relationIdeal f) (pointEval f p) (pointEval_mem f p)
        ((Ideal.Quotient.mk (relationIdeal f)) (MvPolynomial.C r)) = _
      rw [Ideal.Quotient.lift_mk]
      simp [pointEval] }

@[simp] theorem pointToAlgHom_coordA (f : k[X]) {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) : pointToAlgHom f p (coordA f) = p.scale := by
  change (Ideal.Quotient.lift (relationIdeal f) (pointEval f p) (pointEval_mem f p))
      ((Ideal.Quotient.mk (relationIdeal f)) (MvPolynomial.X 0)) = _
  rw [Ideal.Quotient.lift_mk]
  exact pointEval_a f p

@[simp] theorem pointToAlgHom_coordB (f : k[X]) {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) : pointToAlgHom f p (coordB f) = p.translate := by
  change (Ideal.Quotient.lift (relationIdeal f) (pointEval f p) (pointEval_mem f p))
      ((Ideal.Quotient.mk (relationIdeal f)) (MvPolynomial.X 1)) = _
  rw [Ideal.Quotient.lift_mk]
  exact pointEval_b f p

@[simp] theorem pointToAlgHom_coordC (f : k[X]) {S : Type v} [CommRing S] [Algebra k S]
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

/-! ## The represented point functor -/

theorem pointOfAlgHom_pointToAlgHom (f : k[X]) {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) : pointOfAlgHom f (pointToAlgHom f p) = p := by
  have hscale : (pointOfAlgHom f (pointToAlgHom f p)).scale = p.scale := by
    apply Units.ext
    exact pointToAlgHom_coordA f p
  have htranslate : (pointOfAlgHom f (pointToAlgHom f p)).translate = p.translate :=
    pointToAlgHom_coordB f p
  exact Point.ext hscale htranslate

theorem pointToAlgHom_pointOfAlgHom (f : k[X]) {S : Type v} [CommRing S] [Algebra k S]
    (φ : CoordinateRing f →ₐ[k] S) : pointToAlgHom f (pointOfAlgHom f φ) = φ := by
  apply AlgHom.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro q
  have h : (pointToAlgHom f (pointOfAlgHom f φ)).toRingHom.comp
      (Ideal.Quotient.mk (relationIdeal f)) =
      φ.toRingHom.comp (Ideal.Quotient.mk (relationIdeal f)) := by
    apply MvPolynomial.ringHom_ext'
    · ext r
      change pointToAlgHom f (pointOfAlgHom f φ)
          (algebraMap k (CoordinateRing f) r) =
        φ (algebraMap k (CoordinateRing f) r)
      rw [(pointToAlgHom f (pointOfAlgHom f φ)).commutes, φ.commutes]
    · intro i
      fin_cases i
      · change pointToAlgHom f (pointOfAlgHom f φ) (coordA f) = φ (coordA f)
        simpa [coordA, pointOfAlgHom] using
          pointToAlgHom_coordA f (pointOfAlgHom f φ)
      · change pointToAlgHom f (pointOfAlgHom f φ) (coordB f) = φ (coordB f)
        simpa [coordB, pointOfAlgHom] using pointToAlgHom_coordB f (pointOfAlgHom f φ)
      · change pointToAlgHom f (pointOfAlgHom f φ) (coordC f) = φ (coordC f)
        rw [pointToAlgHom_coordC]
        rfl
  exact RingHom.congr_fun h q

/-- The coordinate algebra represents `Point` over arbitrary commutative test algebras. -/
def pointEquiv (f : k[X]) {S : Type v} [CommRing S] [Algebra k S] :
    Point f S ≃ (CoordinateRing f →ₐ[k] S) where
  toFun := pointToAlgHom f
  invFun := pointOfAlgHom f
  left_inv := pointOfAlgHom_pointToAlgHom f
  right_inv := pointToAlgHom_pointOfAlgHom f

theorem pointToAlgHom_map (f : k[X]) {S T : Type*} [CommRing S] [CommRing T]
    [Algebra k S] [Algebra k T] (g : S →ₐ[k] T) (p : Point f S) :
    pointToAlgHom f (Point.map f g p) = g.comp (pointToAlgHom f p) := by
  apply AlgHom.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro q
  have h : (pointToAlgHom f (Point.map f g p)).toRingHom.comp
      (Ideal.Quotient.mk (relationIdeal f)) =
      (g.comp (pointToAlgHom f p)).toRingHom.comp
        (Ideal.Quotient.mk (relationIdeal f)) := by
    apply MvPolynomial.ringHom_ext'
    · ext r
      change pointToAlgHom f (Point.map f g p)
          (algebraMap k (CoordinateRing f) r) =
        (g.comp (pointToAlgHom f p)) (algebraMap k (CoordinateRing f) r)
      rw [(pointToAlgHom f (Point.map f g p)).commutes,
        (g.comp (pointToAlgHom f p)).commutes]
    · intro i
      fin_cases i
      · change pointToAlgHom f (Point.map f g p) (coordA f) =
          g (pointToAlgHom f p (coordA f))
        rw [pointToAlgHom_coordA, pointToAlgHom_coordA]
        rfl
      · change pointToAlgHom f (Point.map f g p) (coordB f) =
          g (pointToAlgHom f p (coordB f))
        rw [pointToAlgHom_coordB, pointToAlgHom_coordB]
        rfl
      · change pointToAlgHom f (Point.map f g p) (coordC f) =
          g (pointToAlgHom f p (coordC f))
        rw [pointToAlgHom_coordC, pointToAlgHom_coordC]
        rfl
  exact RingHom.congr_fun h q

theorem pointOfAlgHom_map (f : k[X]) {S T : Type*} [CommRing S] [CommRing T]
    [Algebra k S] [Algebra k T] (g : S →ₐ[k] T) (φ : CoordinateRing f →ₐ[k] S) :
    Point.map f g (pointOfAlgHom f φ) = pointOfAlgHom f (g.comp φ) := by
  apply (pointEquiv f).injective
  change pointToAlgHom f (Point.map f g (pointOfAlgHom f φ)) =
    pointToAlgHom f (pointOfAlgHom f (g.comp φ))
  calc
    pointToAlgHom f (Point.map f g (pointOfAlgHom f φ)) =
        g.comp (pointToAlgHom f (pointOfAlgHom f φ)) :=
      pointToAlgHom_map f g (pointOfAlgHom f φ)
    _ = g.comp φ := congrArg (fun ψ => g.comp ψ)
      (pointToAlgHom_pointOfAlgHom f φ)
    _ = pointToAlgHom f (pointOfAlgHom f (g.comp φ)) :=
      (pointToAlgHom_pointOfAlgHom f (g.comp φ)).symm

/-! ## Finiteness of the coordinate algebra -/

instance coordinateRing_nontrivial (f : k[X]) : Nontrivial (CoordinateRing f) := by
  let e : CoordinateRing f →ₐ[k] k := pointToAlgHom f (Point.one f)
  refine ⟨0, 1, ?_⟩
  intro h
  have h' := congrArg e h
  simp only [map_zero, map_one] at h'
  exact zero_ne_one h'

private theorem coordinateRing_adjoin_eq_top (f : k[X]) :
    Algebra.adjoin k ({coordA f, coordB f, coordC f} : Set (CoordinateRing f)) = ⊤ := by
  apply top_unique
  intro x hx
  refine Quotient.inductionOn' x ?_
  intro q
  have hAgen : coordA f ∈
      Algebra.adjoin k ({coordA f, coordB f, coordC f} : Set (CoordinateRing f)) :=
    Algebra.subset_adjoin (by simp)
  have hBgen : coordB f ∈
      Algebra.adjoin k ({coordA f, coordB f, coordC f} : Set (CoordinateRing f)) :=
    Algebra.subset_adjoin (by simp)
  have hCgen : coordC f ∈
      Algebra.adjoin k ({coordA f, coordB f, coordC f} : Set (CoordinateRing f)) :=
    Algebra.subset_adjoin (by simp)
  induction q using MvPolynomial.induction_on with
  | C r =>
      change algebraMap k (CoordinateRing f) r ∈
        Algebra.adjoin k ({coordA f, coordB f, coordC f} : Set (CoordinateRing f))
      exact Subalgebra.algebraMap_mem _ r
  | add p q hp hq =>
      change Ideal.Quotient.mk (relationIdeal f) (p + q) ∈ _
      rw [map_add]
      exact add_mem hp hq
  | mul_X p i hp =>
      fin_cases i
      · change Ideal.Quotient.mk (relationIdeal f) (p * MvPolynomial.X 0) ∈ _
        rw [map_mul]
        exact mul_mem hp hAgen
      · change Ideal.Quotient.mk (relationIdeal f) (p * MvPolynomial.X 1) ∈ _
        rw [map_mul]
        exact mul_mem hp hBgen
      · change Ideal.Quotient.mk (relationIdeal f) (p * MvPolynomial.X 2) ∈ _
        rw [map_mul]
        exact mul_mem hp hCgen

theorem coordinateRing_moduleFinite {f : k[X]} (hf : 0 < f.natDegree) :
    Module.Finite k (CoordinateRing f) := by
  let p : Point f (CoordinateRing f) :=
    pointOfAlgHom f (AlgHom.id k (CoordinateRing f))
  have hA : IsIntegral k (coordA f) := by
    simpa [p, pointOfAlgHom, coordA] using
      (isIntegral_scale_of_preserves hf p.scale p.translate p.preserves.symm)
  have hB : IsIntegral k (coordB f) := by
    simpa [p, pointOfAlgHom, coordB] using
      (isIntegral_translate_of_preserves hf p.scale p.translate p.preserves.symm)
  have hC : IsIntegral k (coordC f) := by
    have h := isIntegral_inverse_scale_of_preserves hf p.scale p.translate p.preserves.symm
    rw [show (↑(p.scale⁻¹) : CoordinateRing f) = coordC f by
      change ↑((Units.mkOfMulEqOne (coordA f) (coordC f) _)⁻¹) = coordC f
      rfl] at h
    exact h
  let s : Set (CoordinateRing f) := {coordA f, coordB f, coordC f}
  have hs : s.Finite := by simp [s]
  have hi : ∀ x ∈ s, IsIntegral k x := by
    intro x hx
    rcases hx with (rfl | rfl | rfl | hfalse) <;> try contradiction
    · exact hA
    · exact hB
    · exact hC
  have hadj : Algebra.adjoin k s = ⊤ := by
    simpa [s] using coordinateRing_adjoin_eq_top f
  have hsub : (Algebra.adjoin k s).toSubmodule = (⊤ : Submodule k (CoordinateRing f)) := by
    rw [hadj]
    rfl
  rw [Module.finite_def]
  simpa only [hsub] using
    (fg_adjoin_of_finite hs hi)

theorem coordinateRing_specMap_isFinite {f : k[X]} (hf : 0 < f.natDegree) :
    _root_.AlgebraicGeometry.IsFinite (_root_.AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap k (CoordinateRing f)))) := by
  rw [IsFinite.SpecMap_iff]
  change (algebraMap k (CoordinateRing f)).Finite
  rw [RingHom.finite_algebraMap]
  exact coordinateRing_moduleFinite hf

theorem coordinateRing_formallyUnramified {f : k[X]} (hf : f.derivative ≠ 0) :
    Algebra.FormallyUnramified k (CoordinateRing f) := by
  refine Algebra.FormallyUnramified.iff_comp_injective.mpr ?_
  intro S _ _ I hI φ ψ hφψ
  let P : Point f S := pointOfAlgHom f φ
  let Q : Point f S := pointOfAlgHom f ψ
  have hA : Ideal.Quotient.mk I (φ (coordA f)) =
      Ideal.Quotient.mk I (ψ (coordA f)) := by
    have h := DFunLike.congr_fun hφψ (coordA f)
    simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] using h
  have hB : Ideal.Quotient.mk I (φ (coordB f)) =
      Ideal.Quotient.mk I (ψ (coordB f)) := by
    have h := DFunLike.congr_fun hφψ (coordB f)
    simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] using h
  have ha : (Q.scale : S) - (P.scale : S) ∈ I := by
    apply (Ideal.Quotient.eq.mp ?_)
    simpa [P, Q, pointOfAlgHom] using hA.symm
  have hb : Q.translate - P.translate ∈ I := by
    apply (Ideal.Quotient.eq.mp ?_)
    simpa [P, Q, pointOfAlgHom] using hB.symm
  have hPQ := affine_substitutions_eq_of_sq_zero hf I hI P.scale Q.scale
    P.translate Q.translate ha hb P.preserves.symm Q.preserves.symm
  have hP : P = Q := Point.ext hPQ.1.symm hPQ.2.symm
  calc
    φ = pointToAlgHom f P := (pointToAlgHom_pointOfAlgHom f φ).symm
    _ = pointToAlgHom f Q := congrArg (pointToAlgHom f) hP
    _ = ψ := pointToAlgHom_pointOfAlgHom f ψ

theorem coordinateRing_specMap_formallyUnramified {f : k[X]} (hf : f.derivative ≠ 0) :
    _root_.AlgebraicGeometry.FormallyUnramified (_root_.AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap k (CoordinateRing f)))) := by
  rw [_root_.AlgebraicGeometry.HasRingHomProperty.Spec_iff
    (P := @_root_.AlgebraicGeometry.FormallyUnramified)]
  change (algebraMap k (CoordinateRing f)).FormallyUnramified
  rw [RingHom.formallyUnramified_algebraMap]
  exact coordinateRing_formallyUnramified hf

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

/-! The represented points carry the expected affine-substitution group law.
The first argument is the outer substitution, so `p.comp q` represents
`p ∘ q`. -/

def Point.comp {f : k[X]} {S : Type v} [CommRing S] [Algebra k S]
    (p q : Point f S) : Point f S where
  scale := p.scale * q.scale
  translate := (p.scale : S) * q.translate + p.translate
  preserves := by
    have hp := p.preserves
    have hq := q.preserves
    have hcomp := substitution_composition_formula q.scale p.scale q.translate p.translate
    calc
      (f.map (algebraMap k S)) =
          (f.map (algebraMap k S)).comp
            (C (q.scale : S) * X + C q.translate) := hq
      _ = ((f.map (algebraMap k S)).comp
          (C (p.scale : S) * X + C p.translate)).comp
            (C (q.scale : S) * X + C q.translate) :=
        congrArg (fun r : S[X] => r.comp (C (q.scale : S) * X + C q.translate)) hp
      _ = (f.map (algebraMap k S)).comp
          ((C (p.scale : S) * X + C p.translate).comp
            (C (q.scale : S) * X + C q.translate)) :=
        Polynomial.comp_assoc _ _ _
      _ = (f.map (algebraMap k S)).comp
          (C ((p.scale : S) * (q.scale : S)) * X +
            C ((p.scale : S) * q.translate + p.translate)) := by
        rw [hcomp]

def Point.inv {f : k[X]} {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) : Point f S where
  scale := p.scale⁻¹
  translate := (-(↑p.scale⁻¹ : S)) * p.translate
  preserves := by
    have hp := p.preserves
    have hi := substitution_composition_identity p.scale p.translate
    have hi' : (C (p.scale : S) * X + C p.translate).comp
        (C (↑p.scale⁻¹ : S) * X + C ((-(↑p.scale⁻¹ : S)) * p.translate)) = X := by
      simpa [sub_eq_add_neg] using hi
    have hinv : (f.map (algebraMap k S)).comp
        (C (↑p.scale⁻¹ : S) * X + C ((-(↑p.scale⁻¹ : S)) * p.translate)) =
        f.map (algebraMap k S) := by
      calc
        _ = ((f.map (algebraMap k S)).comp
            (C (p.scale : S) * X + C p.translate)).comp
              (C (↑p.scale⁻¹ : S) * X + C ((-(↑p.scale⁻¹ : S)) * p.translate)) :=
          congrArg (fun r : S[X] => r.comp
            (C (↑p.scale⁻¹ : S) * X + C ((-(↑p.scale⁻¹ : S)) * p.translate))) hp
        _ = (f.map (algebraMap k S)).comp
            ((C (p.scale : S) * X + C p.translate).comp
              (C (↑p.scale⁻¹ : S) * X + C ((-(↑p.scale⁻¹ : S)) * p.translate))) :=
          Polynomial.comp_assoc _ _ _
        _ = (f.map (algebraMap k S)).comp X := by rw [hi']
        _ = f.map (algebraMap k S) := Polynomial.comp_X
    simpa only [neg_mul] using hinv.symm

theorem Point.comp_assoc {f : k[X]} {S : Type v} [CommRing S] [Algebra k S]
    (p q r : Point f S) : (p.comp q).comp r = p.comp (q.comp r) := by
  apply Point.ext
  · simp [Point.comp, mul_assoc]
  · simp [Point.comp, mul_add, add_assoc, mul_assoc]

theorem Point.map_id {f : k[X]} {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) : Point.map f (AlgHom.id k S) p = p := by
  apply Point.ext
  · apply Units.ext
    rfl
  · rfl

theorem Point.map_comp {f : k[X]} {S T U : Type*}
    [CommRing S] [CommRing T] [CommRing U]
    [Algebra k S] [Algebra k T] [Algebra k U]
    (g : S →ₐ[k] T) (h : T →ₐ[k] U) (p : Point f S) :
    Point.map f (h.comp g) p = Point.map f h (Point.map f g p) := by
  apply Point.ext
  · apply Units.ext
    rfl
  · rfl

@[simp] theorem Point.comp_scale {f : k[X]} {S : Type v} [CommRing S] [Algebra k S]
    (p q : Point f S) :
    (p.comp q).scale = p.scale * q.scale := rfl

@[simp] theorem Point.comp_translate {f : k[X]} {S : Type v} [CommRing S] [Algebra k S]
    (p q : Point f S) :
    (p.comp q).translate = (p.scale : S) * q.translate + p.translate := rfl

@[simp] theorem Point.inv_scale {f : k[X]} {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) : (p.inv).scale = p.scale⁻¹ := rfl

@[simp] theorem Point.inv_translate {f : k[X]} {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) :
    (p.inv).translate = (-(↑p.scale⁻¹ : S)) * p.translate := rfl

theorem Point.comp_one {f : k[X]} {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) : p.comp (Point.one f) = p := by
  apply Point.ext <;> simp [Point.one]

theorem Point.one_comp {f : k[X]} {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) : (Point.one f).comp p = p := by
  apply Point.ext <;> simp [Point.one]

theorem Point.comp_inv {f : k[X]} {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) : p.comp p.inv = Point.one f := by
  apply Point.ext
  · simp [Point.one, Point.comp, Point.inv]
  · change (p.scale : S) * ((-(↑p.scale⁻¹ : S)) * p.translate) + p.translate = 0
    simp

theorem Point.inv_comp {f : k[X]} {S : Type v} [CommRing S] [Algebra k S]
    (p : Point f S) : p.inv.comp p = Point.one f := by
  apply Point.ext
  · simp [Point.one, Point.comp, Point.inv]
  · simp only [Point.comp_translate, Point.inv_scale, Point.inv_translate, Point.one]
    simp

theorem Point.map_mul {f : k[X]} {S T : Type*} [CommRing S] [CommRing T]
    [Algebra k S] [Algebra k T] (g : S →ₐ[k] T) (p q : Point f S) :
    Point.map f g (p.comp q) = (Point.map f g p).comp (Point.map f g q) := by
  apply Point.ext
  · apply Units.ext
    simp [Point.map, Point.comp]
  · simp [Point.map, Point.comp]

noncomputable instance pointGroup {f : k[X]} {S : Type v} [CommRing S] [Algebra k S] :
    Group (Point f S) where
  mul := Point.comp
  one := Point.one f
  inv := Point.inv
  mul_assoc := Point.comp_assoc
  one_mul := Point.one_comp
  mul_one := Point.comp_one
  inv_mul_cancel := Point.inv_comp

def Point.mapMonoidHom {f : k[X]} {S T : Type*} [CommRing S] [CommRing T]
    [Algebra k S] [Algebra k T] (g : S →ₐ[k] T) : Point f S →* Point f T where
  toFun := Point.map f g
  map_one' := by
    apply Point.ext
    · apply Units.ext
      change g (1 : S) = (1 : T)
      exact g.map_one
    · change g (0 : S) = (0 : T)
      exact g.map_zero
  map_mul' := Point.map_mul g

end
end PolynomialAutomorphisms
end GromovWitten.AlgebraicGeometry
