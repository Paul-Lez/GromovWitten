/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import GromovWitten.AlgebraicGeometry.Cones.NormalConeRegular
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Smooth quotients of polynomial rings are quasi-regular

Let `k` be a commutative ring, `P = MvPolynomial σ k` a polynomial ring, `I : Ideal P` and
`S = P ⧸ I`.  This file proves the "formally smooth ⇒ quasi-regular embedding" theorem
(EGA 0_IV 19.5.4 / Stacks-project style): if `S` is *formally smooth* over `k`
(`Algebra.FormallySmooth k S`, `Mathlib/RingTheory/Smooth/Basic.lean`), then the canonical
comparison map

`normalSheafCoordinateMap P I : Sym_S(I/I²) ⟶ gr_I(P)`

of `GromovWitten.AlgebraicGeometry.Cones.Affine` is injective (hence, together with the
surjectivity already proved there, bijective).  Together with `Cones/NormalConeRegular.lean`
this feeds the identity `C_{U/M} = N_{U/M}` for smooth `U ⊆ 𝔸ⁿ` (issue #64), and is exactly the
smooth case of the intrinsic-normal-cone / lci virtual-class formula (issue #66).

## Proof sketch

Formal smoothness of `S`, applied to the surjection `P →ₐ[k] S` and its square-zero kernel
extension `P ⧸ I² ↠ S`, produces a `k`-algebra section `g : S →ₐ[k] P ⧸ I²`
(`Algebra.FormallySmooth.iff_split_surjection`).  Writing `π : P ⧸ I² →ₐ[k] S` for the quotient
map, for every `p : P` the difference `mk(I²) p - g (mk I p)` lies in the square-zero ideal
`I.cotangentIdeal`, defining a map `snd : P → I.Cotangent` (`AffineNormalCone.snd`) which records
the "first-order defect" of the section.  Using `aeval`, this yields a `k`-algebra map

`θ : P →ₐ[k] Σ`,  `θ (X j) = algebraMap S Σ (mk I (X j)) + ι (snd (X j))`

into `Σ := normalSheafCoordinateRing P I = Sym_S(I/I²)`.  Composing `θ` with the *coaction*
`c : Σ →ₐ[S] Polynomial Σ` (`GradedCone.symCoaction`, which extracts a formal grading of `Σ`
without needing a `GradedAlgebra` instance) lets us read off, by induction on `p`, the degree-`0`
and degree-`1` parts of `θ p`: they are `algebraMap S Σ (mk I p)` and `ι (snd p)`.  A further
induction on powers of `I` shows every `a ∈ I ^ i` has `c (θ a)` divisible by `X ^ i`, which makes
the "diagonal extraction" `q ↦ ∑ₙ (c (θ (q.coeff n))).coeff n` a *ring homomorphism* on the Rees
algebra of `I`, descending to a left inverse `η` of `normalSheafCoordinateMap P I` on the
associated graded ring; a ring homomorphism admitting a left inverse is injective.
-/

open CategoryTheory AlgebraicGeometry MvPolynomial Polynomial

namespace GromovWitten.AlgebraicGeometry

namespace AffineNormalCone

universe u

section PolynomialCoeff

/-- If `F` vanishes in every degree below `i` and `G` vanishes in degree `0`, then `F * G`
vanishes in every degree below `i + 1`.  A Cauchy-product coefficient of `F * G` at some `j <
i + 1` pairs an index `a` with `b = j - a`: either `a < i` (so `F.coeff a = 0`) or `a ≥ i`, which
forces `b = 0` since `a + b = j ≤ i`. -/
theorem coeff_mul_eq_zero_of_lt {R : Type*} [Semiring R] {F G : Polynomial R} {i : ℕ}
    (hF : ∀ a < i, F.coeff a = 0) (hG : G.coeff 0 = 0) :
    ∀ j < i + 1, (F * G).coeff j = 0 := by
  intro j hj
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  obtain ⟨a, b⟩ := x
  rw [Finset.mem_antidiagonal] at hx
  rcases lt_or_ge a i with ha | ha
  · rw [hF a ha, zero_mul]
  · have hb : b = 0 := by omega
    rw [hb, hG, mul_zero]

/-- If `F` vanishes below degree `a` and `G` vanishes below degree `b`, the degree-`(a + b)`
coefficient of `F * G` is exactly the product of the degree-`a` and degree-`b` coefficients: every
other pair `(a', b')` in the antidiagonal of `a + b` has either `a' < a` or `b' < b`. -/
theorem coeff_mul_eq_of_ge {R : Type*} [CommSemiring R] {F G : Polynomial R} {a b : ℕ}
    (hF : ∀ a' < a, F.coeff a' = 0) (hG : ∀ b' < b, G.coeff b' = 0) :
    (F * G).coeff (a + b) = F.coeff a * G.coeff b := by
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_single (a, b) ?_ ?_
  · rintro ⟨a', b'⟩ hx hne
    rw [Finset.mem_antidiagonal] at hx
    rcases lt_trichotomy a' a with ha' | ha' | ha'
    · rw [hF a' ha', zero_mul]
    · exact absurd (by simp only [Prod.mk.injEq]; omega) hne
    · have hb' : b' < b := by omega
      rw [hG b' hb', mul_zero]
  · intro h
    exact (h (Finset.mem_antidiagonal.mpr rfl)).elim

end PolynomialCoeff

variable {k : Type u} [CommRing k] {σ : Type u}

section FormallySmooth

variable (I : Ideal (MvPolynomial σ k))

/-- The canonical `k`-algebra quotient map `P →ₐ[k] P ⧸ I`. -/
noncomputable abbrev quotientMap : MvPolynomial σ k →ₐ[k] MvPolynomial σ k ⧸ I :=
  Ideal.Quotient.mkₐ k I

/-- `quotientMap` is (as any `Ideal.Quotient.mk`) surjective. -/
theorem quotientMap_surjective : Function.Surjective (quotientMap I) :=
  Ideal.Quotient.mk_surjective

/-- The ideal `RingHom.ker (quotientMap I).toRingHom`, which is equal to `I`
(`kernelIdeal_eq`) but appears with this shape in `AlgHom.kerSquareLift`. -/
noncomputable abbrev kernelIdeal : Ideal (MvPolynomial σ k) :=
  RingHom.ker (quotientMap I).toRingHom

/-- `kernelIdeal I` is literally `I`, presented as a kernel to match `AlgHom.kerSquareLift`. -/
theorem kernelIdeal_eq : kernelIdeal I = I :=
  Ideal.ext fun p => by
    simp only [kernelIdeal, RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem

/-- The `k`-algebra equivalence identifying the abstract kernel-square quotient with
`P ⧸ I ^ 2`. -/
noncomputable def kernelSqEquiv :
    (MvPolynomial σ k ⧸ (kernelIdeal I) ^ 2) ≃ₐ[k] (MvPolynomial σ k ⧸ I ^ 2) :=
  Ideal.quotientEquivAlgOfEq k (h := by rw [kernelIdeal_eq])

/-- The normal-sheaf coordinate ring `Sym_{P⧸I}(I/I²)` is a `k`-algebra through `P ⧸ I`, compatibly
with the tower `k → P ⧸ I → Σ` (needed to apply `MvPolynomial.aeval` over `k`). -/
noncomputable instance instAlgebraBase :
    Algebra k (normalSheafCoordinateRing (MvPolynomial σ k) I) :=
  Algebra.compHom _ (algebraMap k (MvPolynomial σ k ⧸ I))

/-- The `k`-algebra structure on `Σ` is compatible with `Σ`'s existing `(P ⧸ I)`-algebra
structure, forming a scalar tower `k → P ⧸ I → Σ`. -/
instance instIsScalarTowerBase :
    IsScalarTower k (MvPolynomial σ k ⧸ I) (normalSheafCoordinateRing (MvPolynomial σ k) I) :=
  IsScalarTower.of_algebraMap_eq'
    (Algebra.compHom_algebraMap_eq _ (algebraMap k (MvPolynomial σ k ⧸ I)))

variable [Algebra.FormallySmooth k (MvPolynomial σ k ⧸ I)]

/-- The section of the square-zero thickening `P ⧸ I ² ↠ P ⧸ I` produced by formal smoothness of
`P ⧸ I`. -/
noncomputable def sectionHom : (MvPolynomial σ k ⧸ I) →ₐ[k] MvPolynomial σ k ⧸ I ^ 2 :=
  (kernelSqEquiv I).toAlgHom.comp
    (((Algebra.FormallySmooth.iff_split_surjection (quotientMap I)
      (quotientMap_surjective I)).mp ‹_›).choose)

/-- The quotient map `P ⧸ I ² →ₐ[k] P ⧸ I`, obtained by transporting `AlgHom.kerSquareLift`
along `kernelSqEquiv`. -/
noncomputable def projSq : MvPolynomial σ k ⧸ I ^ 2 →ₐ[k] MvPolynomial σ k ⧸ I :=
  (quotientMap I).kerSquareLift.comp (kernelSqEquiv I).symm.toAlgHom

/-- `sectionHom` is a genuine section of `projSq`: this is the content of formal smoothness. -/
theorem projSq_comp_sectionHom : (projSq I).comp (sectionHom I) = AlgHom.id k _ := by
  have hspec := (((Algebra.FormallySmooth.iff_split_surjection (quotientMap I)
      (quotientMap_surjective I)).mp ‹_›)).choose_spec
  ext x
  simp only [projSq, sectionHom, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply, AlgHom.id_apply]
  exact AlgHom.congr_fun hspec x

omit [Algebra.FormallySmooth k (MvPolynomial σ k ⧸ I)] in
/-- `projSq` restricts to the actual quotient map `P ⧸ I ² → P ⧸ I` on representatives. -/
theorem projSq_mk (p : MvPolynomial σ k) :
    projSq I (Ideal.Quotient.mk (I ^ 2) p) = Ideal.Quotient.mk I p := by
  unfold projSq
  have h2 : (kernelSqEquiv I).symm (Ideal.Quotient.mk (I ^ 2) p) =
      Ideal.Quotient.mk ((kernelIdeal I) ^ 2) p := by
    unfold kernelSqEquiv
    rw [Ideal.quotientEquivAlgOfEq_symm]
    exact Ideal.quotientEquivAlgOfEq_mk k _ p
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, h2, AlgHom.kerSquareLift_mk]
  rfl

/-- Pointwise form of `projSq_comp_sectionHom`. -/
theorem projSq_sectionHom (x : MvPolynomial σ k ⧸ I) : projSq I (sectionHom I x) = x :=
  AlgHom.congr_fun (projSq_comp_sectionHom I) x

/-- The defect `mk (I ^ 2) p - sectionHom I (mk I p)` used to define `snd` always lands in the
square-zero ideal `I.cotangentIdeal`. -/
theorem sectionHom_mk_mem_cotangentIdeal (p : MvPolynomial σ k) :
    Ideal.Quotient.mk (I ^ 2) p - sectionHom I (Ideal.Quotient.mk I p) ∈ I.cotangentIdeal := by
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (sectionHom I (Ideal.Quotient.mk I p))
  rw [← hw, ← map_sub, Ideal.mk_mem_cotangentIdeal, ← Ideal.Quotient.eq_zero_iff_mem, map_sub,
    sub_eq_zero]
  have := congrArg (projSq I) hw
  rw [projSq_mk, projSq_sectionHom] at this
  exact this.symm

/-- The "first-order defect" of the section `sectionHom I`: for `p : P`, the class in `I.Cotangent`
of `mk (I ^ 2) p - sectionHom I (mk I p) ∈ I.cotangentIdeal`.  It records the failure of `p` to be
the chosen lift of its own image, to first order; `snd_of_mem` shows it restricts to
`I.toCotangent` on `I`, and `theta_coeff` (below) shows it is the degree-one part of `theta I p`. -/
noncomputable def snd (p : MvPolynomial σ k) : I.Cotangent :=
  I.cotangentEquivIdeal.symm
    ⟨Ideal.Quotient.mk (I ^ 2) p - sectionHom I (Ideal.Quotient.mk I p),
      sectionHom_mk_mem_cotangentIdeal I p⟩

theorem snd_of_mem (z : MvPolynomial σ k) (hz : z ∈ I) :
    snd I z = I.toCotangent ⟨z, hz⟩ := by
  have h0 : Ideal.Quotient.mk I z = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hz
  have he : Ideal.Quotient.mk (I ^ 2) z - sectionHom I (Ideal.Quotient.mk I z) =
      Ideal.Quotient.mk (I ^ 2) z := by rw [h0, map_zero, sub_zero]
  change I.cotangentEquivIdeal.symm
      ⟨Ideal.Quotient.mk (I ^ 2) z - sectionHom I (Ideal.Quotient.mk I z), _⟩ = _
  rw [show (⟨Ideal.Quotient.mk (I ^ 2) z - sectionHom I (Ideal.Quotient.mk I z),
      sectionHom_mk_mem_cotangentIdeal I z⟩ : I.cotangentIdeal) =
      ⟨Ideal.Quotient.mk (I ^ 2) z, Submodule.mem_map_of_mem hz⟩ from Subtype.ext he]
  exact I.cotangentEquivIdeal_symm_apply z hz

/-- Constants have no defect: `sectionHom` is a `k`-algebra map, so it agrees with `mk (I ^ 2)` on
the image of `k`. -/
theorem snd_C (a : k) : snd I (MvPolynomial.C a) = 0 := by
  have e1 : Ideal.Quotient.mk (I ^ 2) (MvPolynomial.C a) =
      algebraMap k (MvPolynomial σ k ⧸ I ^ 2) a := by
    change Ideal.Quotient.mkₐ k (I ^ 2) (MvPolynomial.C a) = _
    rw [MvPolynomial.C_eq_algebraMap]
    exact (Ideal.Quotient.mkₐ k (I ^ 2)).commutes a
  have e2 : sectionHom I (Ideal.Quotient.mk I (MvPolynomial.C a)) =
      algebraMap k (MvPolynomial σ k ⧸ I ^ 2) a := by
    have e0 : Ideal.Quotient.mk I (MvPolynomial.C a) = algebraMap k (MvPolynomial σ k ⧸ I) a := by
      change Ideal.Quotient.mkₐ k I (MvPolynomial.C a) = _
      rw [MvPolynomial.C_eq_algebraMap]
      exact (Ideal.Quotient.mkₐ k I).commutes a
    rw [e0]
    exact (sectionHom I).commutes a
  have hzero_val : Ideal.Quotient.mk (I ^ 2) (MvPolynomial.C a) -
      sectionHom I (Ideal.Quotient.mk I (MvPolynomial.C a)) = 0 := by rw [e1, e2, sub_self]
  change I.cotangentEquivIdeal.symm
      ⟨Ideal.Quotient.mk (I ^ 2) (MvPolynomial.C a) -
        sectionHom I (Ideal.Quotient.mk I (MvPolynomial.C a)), _⟩ = 0
  rw [show (⟨Ideal.Quotient.mk (I ^ 2) (MvPolynomial.C a) -
        sectionHom I (Ideal.Quotient.mk I (MvPolynomial.C a)),
      sectionHom_mk_mem_cotangentIdeal I (MvPolynomial.C a)⟩ : I.cotangentIdeal) = 0 from
    Subtype.ext hzero_val]
  exact map_zero _

/-- `snd` is additive. -/
theorem snd_add (p q : MvPolynomial σ k) : snd I (p + q) = snd I p + snd I q := by
  change I.cotangentEquivIdeal.symm ⟨_, _⟩ = I.cotangentEquivIdeal.symm ⟨_, _⟩ +
    I.cotangentEquivIdeal.symm ⟨_, _⟩
  rw [← map_add]
  congr 1
  ext
  push_cast
  simp only [map_add]
  ring

/-- The Leibniz rule for `snd`: it records the first-order defect of a *ring homomorphism*
`P → P ⧸ I ²` twisted by the section, so the defect of a product is the sum of the two
"one-sided" defects, weighted by the images in `S = P ⧸ I`.  The proof uses that
`I.cotangentIdeal ^ 2 = ⊥` to eliminate the cross term in `(a - a') * (b - b')`. -/
theorem snd_mul (p q : MvPolynomial σ k) :
    snd I (p * q) = Ideal.Quotient.mk I p • snd I q + Ideal.Quotient.mk I q • snd I p := by
  have h1 := sectionHom_mk_mem_cotangentIdeal I p
  have h2 := sectionHom_mk_mem_cotangentIdeal I q
  have hzsq : (Ideal.Quotient.mk (I ^ 2) p - sectionHom I (Ideal.Quotient.mk I p)) *
      (Ideal.Quotient.mk (I ^ 2) q - sectionHom I (Ideal.Quotient.mk I q)) = 0 := by
    have hmem := Ideal.mul_mem_mul h1 h2
    rwa [← pow_two, Ideal.cotangentIdeal_square, Ideal.mem_bot] at hmem
  have hmkp : Ideal.Quotient.mk I p • snd I q = p • snd I q :=
    IsScalarTower.algebraMap_smul (A := MvPolynomial σ k ⧸ I) p (snd I q)
  have hmkq : Ideal.Quotient.mk I q • snd I p = q • snd I p :=
    IsScalarTower.algebraMap_smul (A := MvPolynomial σ k ⧸ I) q (snd I p)
  rw [hmkp, hmkq]
  unfold snd
  rw [← map_smul, ← map_smul, ← map_add]
  congr 1
  ext
  push_cast
  simp only [map_mul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  linear_combination -hzsq

/-- The formal grading of `Σ = Sym_{P⧸I}(I/I²)`, as the coefficients of the scaling coaction
`Σ →ₐ[P⧸I] Σ[t]` (`GradedCone.symCoaction`); this does not need a `GradedAlgebra` instance. -/
noncomputable abbrev coaction :
    normalSheafCoordinateRing (MvPolynomial σ k) I →ₐ[MvPolynomial σ k ⧸ I]
      Polynomial (normalSheafCoordinateRing (MvPolynomial σ k) I) :=
  GradedCone.symCoaction (MvPolynomial σ k ⧸ I) I.Cotangent

/-- The `k`-algebra map `P →ₐ[k] Σ` built from `sectionHom`, sending a variable `X j` to
`algebraMap (mk I (X j)) + ι (snd (X j))`.  By `theta_coeff` its degree-zero and degree-one parts
(read off through `coaction`) are `algebraMap ∘ mk I` and `ι ∘ snd` on *all* of `P`, not just the
variables. -/
noncomputable def theta :
    MvPolynomial σ k →ₐ[k] normalSheafCoordinateRing (MvPolynomial σ k) I :=
  MvPolynomial.aeval fun j : σ =>
    algebraMap (MvPolynomial σ k ⧸ I) (normalSheafCoordinateRing (MvPolynomial σ k) I)
        (Ideal.Quotient.mk I (MvPolynomial.X j)) +
      SymmetricAlgebra.ι (MvPolynomial σ k ⧸ I) I.Cotangent (snd I (MvPolynomial.X j))

/-- `theta` on a variable is, by definition, the sum of the base term and the `ι`-term. -/
theorem theta_X (j : σ) :
    theta I (MvPolynomial.X j) =
      algebraMap (MvPolynomial σ k ⧸ I) (normalSheafCoordinateRing (MvPolynomial σ k) I)
          (Ideal.Quotient.mk I (MvPolynomial.X j)) +
        SymmetricAlgebra.ι (MvPolynomial σ k ⧸ I) I.Cotangent (snd I (MvPolynomial.X j)) :=
  MvPolynomial.aeval_X _ _

/-- `theta` sends a constant to the corresponding base-ring element of `Σ`; unlike the general
`theta_coeff` this is an honest equality in `Σ`, not merely of degree-zero/one parts. -/
theorem theta_C (a : k) :
    theta I (MvPolynomial.C a) =
      algebraMap (MvPolynomial σ k ⧸ I) (normalSheafCoordinateRing (MvPolynomial σ k) I)
        (Ideal.Quotient.mk I (MvPolynomial.C a)) := by
  have e0 : Ideal.Quotient.mk I (MvPolynomial.C a) = algebraMap k (MvPolynomial σ k ⧸ I) a := by
    change Ideal.Quotient.mkₐ k I (MvPolynomial.C a) = _
    rw [MvPolynomial.C_eq_algebraMap]
    exact (Ideal.Quotient.mkₐ k I).commutes a
  rw [e0, ← IsScalarTower.algebraMap_apply]
  exact MvPolynomial.aeval_C _ a

omit [Algebra.FormallySmooth k (MvPolynomial σ k ⧸ I)] in
/-- The degree-zero part of `coaction I (algebraMap _ _ x)` is `algebraMap _ _ x` itself, for any
`x : P ⧸ I`, the base ring sitting in degree zero. -/
theorem coaction_algebraMap_coeff (x : MvPolynomial σ k ⧸ I) (n : ℕ) :
    (coaction I (algebraMap (MvPolynomial σ k ⧸ I)
        (normalSheafCoordinateRing (MvPolynomial σ k) I) x)).coeff n =
      if n = 0 then algebraMap (MvPolynomial σ k ⧸ I)
        (normalSheafCoordinateRing (MvPolynomial σ k) I) x else 0 := by
  have h0 := GradedCone.algebraMap_mem_homogeneous (coaction I) x
  rw [GradedCone.mem_homogeneous, pow_zero, mul_one] at h0
  rw [h0, Polynomial.coeff_C]

/-- The **key induction**: for every `p : P`, the degree-zero and degree-one parts of `theta I p`
(read off through `coaction I`) are `algebraMap ∘ mk I` and `ι ∘ snd`.  This is proved by
`MvPolynomial.induction_on`, using that `theta`, `coaction` are ring homomorphisms and the
Leibniz rule `snd_mul`. -/
theorem theta_coeff (p : MvPolynomial σ k) :
    (coaction I (theta I p)).coeff 0 =
      algebraMap (MvPolynomial σ k ⧸ I) (normalSheafCoordinateRing (MvPolynomial σ k) I)
        (Ideal.Quotient.mk I p) ∧
    (coaction I (theta I p)).coeff 1 =
      SymmetricAlgebra.ι (MvPolynomial σ k ⧸ I) I.Cotangent (snd I p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [theta_C]
    refine ⟨by rw [coaction_algebraMap_coeff, if_pos rfl], ?_⟩
    rw [coaction_algebraMap_coeff, if_neg one_ne_zero, snd_C, map_zero]
  | add p q hp hq =>
    obtain ⟨hp0, hp1⟩ := hp
    obtain ⟨hq0, hq1⟩ := hq
    refine ⟨?_, ?_⟩
    · rw [map_add, map_add, Polynomial.coeff_add, hp0, hq0, ← map_add, ← map_add]
    · rw [map_add, map_add, Polynomial.coeff_add, hp1, hq1, ← map_add, ← snd_add]
  | mul_X p j hp =>
    obtain ⟨hp0, hp1⟩ := hp
    have hX0 : (coaction I (theta I (MvPolynomial.X j))).coeff 0 =
        algebraMap (MvPolynomial σ k ⧸ I) (normalSheafCoordinateRing (MvPolynomial σ k) I)
          (Ideal.Quotient.mk I (MvPolynomial.X j)) := by
      rw [theta_X, map_add, Polynomial.coeff_add, coaction_algebraMap_coeff, if_pos rfl,
        GradedCone.symCoaction_ι]
      simp
    have hX1 : (coaction I (theta I (MvPolynomial.X j))).coeff 1 =
        SymmetricAlgebra.ι (MvPolynomial σ k ⧸ I) I.Cotangent (snd I (MvPolynomial.X j)) := by
      rw [theta_X, map_add, Polynomial.coeff_add, coaction_algebraMap_coeff, if_neg one_ne_zero,
        GradedCone.symCoaction_ι]
      simp
    refine ⟨?_, ?_⟩
    · rw [map_mul, map_mul, Polynomial.mul_coeff_zero, hp0, hX0, ← map_mul, ← map_mul]
    · rw [map_mul, map_mul, Polynomial.mul_coeff_one, hp0, hp1, hX0, hX1, snd_mul, map_add,
        map_smul, map_smul, Algebra.smul_def, Algebra.smul_def]
      ring

/-- **The valuation estimate.**  Every `a ∈ I ^ i` has `coaction I (theta I a)` vanishing in every
degree below `i`: by induction on `i`, using that `I ^ (i + 1) = I ^ i * I` and that elements of
`I` already vanish in degree `0` (`theta_coeff`). -/
theorem theta_coeff_lt : ∀ (i : ℕ) (a : MvPolynomial σ k), a ∈ I ^ i →
    ∀ j < i, (coaction I (theta I a)).coeff j = 0 := by
  intro i
  induction i with
  | zero => intro a _ j hj; omega
  | succ i ih =>
    intro a ha j hj
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha (fun b hb c hc => ?_) (fun x y hx hy => ?_)
    · have hGc0 : (coaction I (theta I c)).coeff 0 = 0 := by
        rw [(theta_coeff I c).1, Ideal.Quotient.eq_zero_iff_mem.mpr hc, map_zero]
      rw [map_mul, map_mul]
      exact coeff_mul_eq_zero_of_lt (ih b hb) hGc0 j hj
    · rw [map_add, map_add, Polynomial.coeff_add, hx, hy, add_zero]

/-- The "diagonal extraction" `q ↦ ∑ₙ (coaction I (theta I (q.coeff n))).coeff n`, as an additive
map on all of `Polynomial P` (not yet restricted to the Rees algebra: additivity holds always,
multiplicativity only on `reesAlgebra I`, see `etaAdd_mul_of_mem`). -/
noncomputable def etaAdd :
    Polynomial (MvPolynomial σ k) →+ normalSheafCoordinateRing (MvPolynomial σ k) I where
  toFun p := p.sum fun n a => (coaction I (theta I a)).coeff n
  map_zero' := Polynomial.sum_zero_index _
  map_add' p q := Polynomial.sum_add_index p q _ (fun n => by simp) (fun n a b => by simp [map_add])

/-- Unfolding lemma for `etaAdd`. -/
theorem etaAdd_apply (p : Polynomial (MvPolynomial σ k)) :
    etaAdd I p = p.sum fun n a => (coaction I (theta I a)).coeff n := rfl

/-- `etaAdd` picks out a single coefficient on a monomial. -/
theorem etaAdd_monomial (n : ℕ) (c : MvPolynomial σ k) :
    etaAdd I (Polynomial.monomial n c) = (coaction I (theta I c)).coeff n := by
  rw [etaAdd_apply]
  exact Polynomial.sum_monomial_index c _ (by simp)

/-- `etaAdd` sends the constant polynomial `1` to `1`. -/
theorem etaAdd_one : etaAdd I 1 = 1 := by
  rw [← Polynomial.C_1, etaAdd_apply, Polynomial.sum_C_index (by simp)]
  rw [map_one, map_one, Polynomial.coeff_one, if_pos rfl]

/-- **Multiplicativity of `etaAdd` on the Rees algebra.**  Uses `Polynomial.mul_eq_sum_sum` to
expand `p * q` as a double sum of monomials, `theta_coeff_lt` for the valuation of each factor,
and `coeff_mul_eq_of_ge` to identify the resulting coefficients. -/
theorem etaAdd_mul_of_mem {p q : Polynomial (MvPolynomial σ k)}
    (hp : ∀ n, p.coeff n ∈ I ^ n) (hq : ∀ n, q.coeff n ∈ I ^ n) :
    etaAdd I (p * q) = etaAdd I p * etaAdd I q := by
  rw [Polynomial.mul_eq_sum_sum, map_sum]
  have hstep : ∀ i ∈ p.support,
      etaAdd I (q.sum fun j a => Polynomial.monomial (i + j) (p.coeff i * a)) =
      (coaction I (theta I (p.coeff i))).coeff i * etaAdd I q := by
    intro i _
    rw [Polynomial.sum_def, map_sum]
    simp_rw [etaAdd_monomial]
    rw [etaAdd_apply, Polynomial.sum_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul]
    exact coeff_mul_eq_of_ge (theta_coeff_lt I i _ (hp i)) (theta_coeff_lt I j _ (hq j))
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul]
  congr 1

/-- `etaAdd`, bundled as a ring homomorphism on the Rees algebra of `I`. -/
noncomputable def eta0 :
    reesAlgebra I →+* normalSheafCoordinateRing (MvPolynomial σ k) I where
  toFun q := etaAdd I q.1
  map_zero' := map_zero _
  map_one' := etaAdd_one I
  map_add' _ _ := map_add _ _ _
  map_mul' p q := etaAdd_mul_of_mem I ((mem_reesAlgebra_iff I p.1).mp p.2)
    ((mem_reesAlgebra_iff I q.1).mp q.2)

theorem eta0_algebraMap_eq_zero (x : MvPolynomial σ k) (hx : x ∈ I) :
    eta0 I (algebraMap (MvPolynomial σ k) (reesAlgebra I) x) = 0 := by
  have hcoe : (algebraMap (MvPolynomial σ k) (reesAlgebra I) x : Polynomial (MvPolynomial σ k)) =
      Polynomial.C x := rfl
  change etaAdd I _ = 0
  rw [hcoe, etaAdd_apply, Polynomial.sum_C_index (by simp), (theta_coeff I x).1,
    Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

theorem eta0_ker_mem :
    ∀ x ∈ Ideal.map (algebraMap (MvPolynomial σ k) (reesAlgebra I)) I, eta0 I x = 0 := by
  have hle : Ideal.map (algebraMap (MvPolynomial σ k) (reesAlgebra I)) I ≤
      RingHom.ker (eta0 I) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact eta0_algebraMap_eq_zero I x hx
  exact fun x hx => RingHom.mem_ker.mp (hle hx)

/-- The **left inverse of `normalSheafCoordinateMap`**: the ring homomorphism
`gr_I(P) →+* Σ` obtained by descending `eta0` along the Rees-algebra presentation of the
associated graded ring. -/
noncomputable def eta :
    associatedGradedRing (MvPolynomial σ k) I →+* normalSheafCoordinateRing (MvPolynomial σ k) I :=
  Ideal.Quotient.lift _ (eta0 I) (eta0_ker_mem I)

/-- Unfolding lemma for `eta` on a class coming from the Rees algebra. -/
theorem eta_mk (q : reesAlgebra I) :
    eta I (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial σ k) (reesAlgebra I)) I) q) =
      eta0 I q :=
  Ideal.Quotient.lift_mk _ _ _

/-- `eta` is a left inverse of `normalSheafCoordinateMap` on the base-ring generators of `Σ`. -/
theorem eta_normalSheafCoordinateMap_algebraMap (r : MvPolynomial σ k ⧸ I) :
    eta I (normalSheafCoordinateMap (MvPolynomial σ k) I
        (algebraMap (MvPolynomial σ k ⧸ I) (normalSheafCoordinateRing (MvPolynomial σ k) I) r)) =
      algebraMap (MvPolynomial σ k ⧸ I) (normalSheafCoordinateRing (MvPolynomial σ k) I) r := by
  rw [normalSheafCoordinateMap_base]
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [associatedGradedBaseRingHom]
  rw [Ideal.Quotient.lift_mk, RingHom.comp_apply, eta_mk]
  have hcoe : (algebraMap (MvPolynomial σ k) (reesAlgebra I) x : Polynomial (MvPolynomial σ k)) =
      Polynomial.C x := rfl
  change etaAdd I _ = _
  rw [hcoe, etaAdd_apply, Polynomial.sum_C_index (by simp)]
  exact (theta_coeff I x).1

/-- `eta` is a left inverse of `normalSheafCoordinateMap` on the degree-one generators `ι m` of
`Σ`. -/
theorem eta_normalSheafCoordinateMap_ι (m : I.Cotangent) :
    eta I (normalSheafCoordinateMap (MvPolynomial σ k) I
        (SymmetricAlgebra.ι (MvPolynomial σ k ⧸ I) I.Cotangent m)) =
      SymmetricAlgebra.ι (MvPolynomial σ k ⧸ I) I.Cotangent m := by
  rw [normalSheafCoordinateMap_ι]
  obtain ⟨z, rfl⟩ := I.toCotangent_surjective m
  rw [conormalToAssociatedGraded_toCotangent, eta_mk]
  change etaAdd I _ = _
  have hcoe : ((degreeOneRees (MvPolynomial σ k) I z : reesAlgebra I) :
      Polynomial (MvPolynomial σ k)) = Polynomial.monomial 1 (z : MvPolynomial σ k) :=
    degreeOneRees_coe _ _ z
  rw [hcoe, etaAdd_monomial, (theta_coeff I (z : MvPolynomial σ k)).2,
    snd_of_mem I (z : MvPolynomial σ k) z.2]

/-- **The formally-smooth ⇒ quasi-regular embedding theorem** (EGA `0_IV` 19.5.4 /
Stacks-project style): if `S = P ⧸ I` is formally smooth over `k` for `P = MvPolynomial σ k`,
the canonical comparison map `Sym_S(I/I²) ⟶ gr_I(P)` is injective, hence (with
`normalSheafCoordinateMap_surjective`) bijective.  This feeds `C_{U/M} = N_{U/M}` for smooth
`U ⊆ 𝔸ⁿ` (issue #64) and the smooth case of the lci virtual-class formula (issue #66). -/
theorem normalSheafCoordinateMap_injective_of_formallySmooth :
    Function.Injective (normalSheafCoordinateMap (MvPolynomial σ k) I) := by
  have hleft : Function.LeftInverse (eta I) (normalSheafCoordinateMap (MvPolynomial σ k) I) := by
    intro w
    induction w using SymmetricAlgebra.induction with
    | algebraMap r => exact eta_normalSheafCoordinateMap_algebraMap I r
    | ι m => exact eta_normalSheafCoordinateMap_ι I m
    | mul a b ha hb => rw [map_mul, map_mul, ha, hb]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  exact hleft.injective

/-- Together with the already available surjectivity, the canonical comparison map is
bijective for a formally smooth quotient. -/
theorem normalSheafCoordinateMap_bijective_of_formallySmooth :
    Function.Bijective (normalSheafCoordinateMap (MvPolynomial σ k) I) :=
  ⟨normalSheafCoordinateMap_injective_of_formallySmooth I,
    normalSheafCoordinateMap_surjective (MvPolynomial σ k) I⟩

/-- **The affine normal cone of a formally smooth quotient is its normal sheaf**: the affine
closed immersion of `Cones/Affine.lean` is an isomorphism, matching
`QuasiregularGenerators.coneToNormalSheaf_isIso` from `Cones/NormalConeRegular.lean` but under the
hypothesis `Algebra.FormallySmooth k (P ⧸ I)` instead of an explicit quasi-regular sequence. -/
theorem coneToNormalSheaf_isIso_of_formallySmooth :
    IsIso (coneToNormalSheaf (MvPolynomial σ k) I) := by
  have hiso : IsIso
      (Spec.map (CommRingCat.ofHom (normalSheafCoordinateMap (MvPolynomial σ k) I))) := by
    rw [isIso_SpecMap_iff]
    exact normalSheafCoordinateMap_bijective_of_formallySmooth I
  exact hiso

end FormallySmooth

end AffineNormalCone

end GromovWitten.AlgebraicGeometry
