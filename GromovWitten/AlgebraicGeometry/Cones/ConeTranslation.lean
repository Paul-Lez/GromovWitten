/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Cones.DeformationSpace
import GromovWitten.AlgebraicGeometry.Cones.NormalConeGlobal
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# The tangent translation action on the affine normal cone (Vistoli's lemma, polynomial model)

Let `M = 𝔸^σ_A = Spec R` with `R = A[x_i]_{i ∈ σ}`, let `I ⊆ R` be an ideal and `U = Spec (R/I)`.
The tangent bundle of `M` is trivial, `T_M = M × 𝔸^σ`, and it acts on `M` by translation
`x ↦ x + ε`.  The translation action of `T_M|_U = U × 𝔸^σ` on the normal *sheaf*
`N_{U/M} = Spec Sym_{R/I}(I/I²)` is the derivative of this action, `[f] ↦ [f] + Σ_i ε_i ∂_i f`;
the content of Vistoli's lemma (Behrend–Fantechi, the input to the intrinsic normal cone) is that
it preserves the closed subcone `C_{U/M} = Spec gr_I(R)`.

This file constructs that action on the cone itself.  The translation `x ↦ x + ε t⁻¹` of
Laurent polynomials (`translateLaurent`) preserves the extended Rees algebra `R[It, t⁻¹]`
(`translateLaurent_mem_extendedRees`), by the Taylor expansion
`f(x + ε t⁻¹) = f + t⁻¹·Df + t⁻²·(…)` (`exists_translateLaurent_eq`), hence descends to the special
fibre `t⁻¹ = 0`, which is `gr_I(R)`; flat base change of the associated graded ring along
`R → R[ε]` (`grTensorEquiv`) then produces the coaction

`coaction : gr_I(R) →ₐ[R] gr_I(R)[ε_σ]`, `[f t] ↦ [f t] + Σ_i ε_i [∂_i f]`

(`coaction_degreeOne`).  The counit and coassociativity laws are proved
(`coaction_counit`, `coaction_coassoc`), the action on `B`-points is `translatePoint` with its
unit and additivity laws, and the closed immersion `C_{U/M} → N_{U/M}` is proved equivariant: the
coaction is compatible with the translation coaction of the normal sheaf through the surjection
`Sym(I)/I·Sym(I) ↠ gr_I(R)` (`coaction_comp_nsToGr`).  Finally the action is packaged as a
morphism of schemes `T_M|_U ×_U C_{U/M} → C_{U/M}` (`actionMap`).
-/

open LaurentPolynomial

namespace GromovWitten.AlgebraicGeometry

namespace ConeTranslation

universe u

noncomputable section

variable (A : Type u) [CommRing A] (σ : Type u)

/-- The ambient polynomial ring `R = A[x_i]`. -/
abbrev Amb : Type u := MvPolynomial σ A

/-- The coordinate ring `R[ε_i]` of `T_M = M × 𝔸^σ`. -/
abbrev Ext : Type u := MvPolynomial σ (Amb A σ)

/-! ### The Taylor derivation -/

/-- The universal derivation `D f = Σ_i ε_i ∂_i f` from `R` to `R[ε]`. -/
def taylor : Derivation A (Amb A σ) (Ext A σ) :=
  MvPolynomial.mkDerivation A fun i ↦ MvPolynomial.X i

@[simp] theorem taylor_X (i : σ) : taylor A σ (MvPolynomial.X i) = MvPolynomial.X i :=
  MvPolynomial.mkDerivation_X _ _ _

@[simp] theorem taylor_C (a : A) : taylor A σ (MvPolynomial.C a) = 0 := by
  rw [← MvPolynomial.algebraMap_eq]
  exact Derivation.map_algebraMap _ _

theorem taylor_mul (f g : Amb A σ) :
    taylor A σ (f * g) = MvPolynomial.C f * taylor A σ g + MvPolynomial.C g * taylor A σ f := by
  rw [Derivation.leibniz, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]

/-- The Taylor derivation has no constant term. -/
theorem constantCoeff_taylor (f : Amb A σ) : MvPolynomial.constantCoeff (taylor A σ f) = 0 := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f i hf => simp [hf]

/-! ### Translation of Laurent polynomials -/

/-- The translation `x_i ↦ x_i + ε_i t⁻¹` from `R` to `R[ε][t, t⁻¹]`. -/
def translateLaurent : Amb A σ →ₐ[A] (Ext A σ)[T;T⁻¹] :=
  MvPolynomial.aeval fun i ↦
    LaurentPolynomial.C (MvPolynomial.C (MvPolynomial.X i)) +
      LaurentPolynomial.C (MvPolynomial.X i) * T (-1)

theorem translateLaurent_X (i : σ) :
    translateLaurent A σ (MvPolynomial.X i) =
      LaurentPolynomial.C (MvPolynomial.C (MvPolynomial.X i)) +
        LaurentPolynomial.C (MvPolynomial.X i) * T (-1) :=
  MvPolynomial.aeval_X _ _

theorem translateLaurent_C (a : A) :
    translateLaurent A σ (MvPolynomial.C a) =
      LaurentPolynomial.C (MvPolynomial.C (MvPolynomial.C a)) := by
  rw [translateLaurent, MvPolynomial.aeval_C]
  rfl

variable {A σ}

/-- The Taylor expansion of a translated polynomial: `f(x + ε t⁻¹) = f + t⁻¹ Df + t⁻² g` with
`g` in the extended Rees algebra of any ideal. -/
theorem exists_translateLaurent_eq (J : Ideal (Ext A σ)) (f : Amb A σ) :
    ∃ g ∈ AffineDeformationSpace.extendedRees (Ext A σ) J,
      translateLaurent A σ f = LaurentPolynomial.C (MvPolynomial.C f) +
        LaurentPolynomial.C (taylor A σ f) * T (-1) + g * T (-2) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, zero_mem _, ?_⟩
    rw [translateLaurent_C, taylor_C]
    simp
  | add f g hf hg =>
    obtain ⟨u, hu, hu'⟩ := hf
    obtain ⟨v, hv, hv'⟩ := hg
    refine ⟨u + v, add_mem hu hv, ?_⟩
    simp only [map_add, hu', hv']
    ring
  | mul_X f i hf =>
    obtain ⟨u, hu, hu'⟩ := hf
    have hC : ∀ r : Ext A σ, LaurentPolynomial.C r ∈
        AffineDeformationSpace.extendedRees (Ext A σ) J := fun r ↦
      AffineDeformationSpace.isExtendedRees_C _ _ r
    have hT : T (-1) ∈ AffineDeformationSpace.extendedRees (Ext A σ) J :=
      (AffineDeformationSpace.parameter (Ext A σ) J).2
    refine ⟨u * LaurentPolynomial.C (MvPolynomial.C (MvPolynomial.X i)) +
      LaurentPolynomial.C (taylor A σ f * MvPolynomial.X i) +
      u * LaurentPolynomial.C (MvPolynomial.X i) * T (-1),
      add_mem (add_mem (mul_mem hu (hC _)) (hC _)) (mul_mem (mul_mem hu (hC _)) hT), ?_⟩
    rw [map_mul, hu', translateLaurent_X, taylor_mul, taylor_X]
    simp only [map_add, map_mul]
    have h1 : (T (-1) : (Ext A σ)[T;T⁻¹]) * T (-1) = T (-2) := by
      rw [← T_add]; norm_num
    have h2 : (T (-2) : (Ext A σ)[T;T⁻¹]) * T (-1) = T (-3) := by
      rw [← T_add]; norm_num
    have h3 : (T (-1) : (Ext A σ)[T;T⁻¹]) * T (-2) = T (-3) := by
      rw [← T_add]; norm_num
    linear_combination (LaurentPolynomial.C (MvPolynomial.X i) *
      LaurentPolynomial.C (taylor A σ f)) * h1 + u * LaurentPolynomial.C (MvPolynomial.X i) * h2
      - u * LaurentPolynomial.C (MvPolynomial.X i) * h3

/-! ### The translation of the extended Rees algebra -/

variable (A σ)

/-- The unit `t` of the Laurent polynomial ring. -/
def tUnit : (Ext A σ)[T;T⁻¹]ˣ := (isUnit_T 1).unit

theorem tUnit_zpow (n : ℤ) :
    ((tUnit A σ ^ n : (Ext A σ)[T;T⁻¹]ˣ) : (Ext A σ)[T;T⁻¹]) = T n := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast, Units.val_pow_eq_pow_val]
    change T 1 ^ k = _
    rw [T_pow, mul_one]
  · rw [zpow_neg, zpow_natCast]
    apply Units.inv_eq_of_mul_eq_one_right
    rw [Units.val_pow_eq_pow_val]
    change T 1 ^ k * T (-k) = 1
    rw [T_pow, mul_one, ← T_add, add_neg_cancel, T_zero]

/-- The translation `x ↦ x + ε t⁻¹`, `t ↦ t` of Laurent polynomials. -/
def translate : (Amb A σ)[T;T⁻¹] →+* (Ext A σ)[T;T⁻¹] :=
  LaurentPolynomial.eval₂ (translateLaurent A σ).toRingHom (tUnit A σ)

theorem translate_C (a : Amb A σ) :
    translate A σ (LaurentPolynomial.C a) = translateLaurent A σ a := by
  rw [translate, eval₂_C]
  rfl

theorem translate_T (n : ℤ) : translate A σ (T n) = T n := by
  rw [translate, eval₂_T, tUnit_zpow]

theorem translate_C_mul_T (a : Amb A σ) (n : ℤ) :
    translate A σ (LaurentPolynomial.C a * T n) = translateLaurent A σ a * T n := by
  rw [map_mul, translate_C, translate_T]

variable {A σ} (I : Ideal (Amb A σ))

/-- The extended ideal `I·R[ε]`. -/
abbrev extIdeal : Ideal (Ext A σ) := I.map (algebraMap (Amb A σ) (Ext A σ))

theorem T_neg_mem (n : ℕ) :
    (T (-n) : (Ext A σ)[T;T⁻¹]) ∈ AffineDeformationSpace.extendedRees (Ext A σ) (extIdeal I) := by
  have h := AffineDeformationSpace.isExtendedRees_of_nonpos (Ext A σ) (extIdeal I)
    (a := (1 : Ext A σ)) (n := -n) (by omega)
  rwa [map_one, one_mul] at h

theorem translateLaurent_mem (f : Amb A σ) :
    translateLaurent A σ f ∈ AffineDeformationSpace.extendedRees (Ext A σ) (extIdeal I) := by
  obtain ⟨g, hg, h⟩ := exists_translateLaurent_eq (extIdeal I) f
  rw [h]
  refine add_mem (add_mem (AffineDeformationSpace.isExtendedRees_C _ _ _)
    (mul_mem (AffineDeformationSpace.isExtendedRees_C _ _ _) ?_)) (mul_mem hg ?_)
  · exact T_neg_mem I 1
  · exact T_neg_mem I 2

/-- For `f ∈ I`, the translate of `f t` lies in the extended Rees algebra of `I·R[ε]`. -/
theorem translateLaurent_mul_T_one_mem {f : Amb A σ} (hf : f ∈ I) :
    translateLaurent A σ f * T 1 ∈
      AffineDeformationSpace.extendedRees (Ext A σ) (extIdeal I) := by
  obtain ⟨g, hg, h⟩ := exists_translateLaurent_eq (extIdeal I) f
  have e : translateLaurent A σ f * T 1 = LaurentPolynomial.C (MvPolynomial.C f) * T 1 +
      LaurentPolynomial.C (taylor A σ f) + g * T (-1) := by
    rw [h, add_mul, add_mul, mul_assoc, mul_assoc, ← T_add, ← T_add]
    norm_num
  rw [e]
  refine add_mem (add_mem ?_ (AffineDeformationSpace.isExtendedRees_C _ _ _)) (mul_mem hg ?_)
  · apply AffineDeformationSpace.isExtendedRees_C_mul_T
    change MvPolynomial.C f ∈ extIdeal I ^ (1 : ℤ).toNat
    rw [Int.toNat_one, pow_one]
    exact Ideal.mem_map_of_mem (algebraMap (Amb A σ) (Ext A σ)) hf
  · exact T_neg_mem I 1

theorem translateLaurent_mul_T_mem {n : ℕ} {f : Amb A σ} (hf : f ∈ I ^ n) :
    translateLaurent A σ f * T n ∈
      AffineDeformationSpace.extendedRees (Ext A σ) (extIdeal I) := by
  refine Submodule.pow_induction_on_left' (M := I)
    (C := fun n f _ ↦ translateLaurent A σ f * T n ∈
      AffineDeformationSpace.extendedRees (Ext A σ) (extIdeal I)) ?_ ?_ ?_ hf
  · intro r
    simpa using translateLaurent_mem I r
  · intro x y i _ _ hx hy
    rw [map_add, add_mul]
    exact add_mem hx hy
  · intro m hm i x _ hx
    have e : translateLaurent A σ (m * x) * T ((i + 1 : ℕ) : ℤ) =
        (translateLaurent A σ m * T 1) * (translateLaurent A σ x * T i) := by
      rw [map_mul, mul_mul_mul_comm, ← T_add]
      push_cast
      ring_nf
    rw [e]
    exact mul_mem (translateLaurent_mul_T_one_mem I hm) hx

/-- The translation preserves the extended Rees algebra. -/
theorem translate_mem {f : (Amb A σ)[T;T⁻¹]}
    (hf : f ∈ AffineDeformationSpace.extendedRees (Amb A σ) I) :
    translate A σ f ∈ AffineDeformationSpace.extendedRees (Ext A σ) (extIdeal I) := by
  rw [AffineDeformationSpace.eq_sum_support (Amb A σ) f, map_sum]
  refine Subalgebra.sum_mem _ fun n _ ↦ ?_
  rw [translate_C_mul_T]
  rcases le_or_gt n 0 with hn | hn
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -k := ⟨(-n).toNat, by omega⟩
    rw [hk]
    exact mul_mem (translateLaurent_mem I _) (T_neg_mem I k)
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn.le
    have := hf k
    rw [Int.toNat_natCast] at this
    exact translateLaurent_mul_T_mem I this

/-- The translation restricted to the extended Rees algebras. -/
def translateRees : AffineDeformationSpace.extendedRees (Amb A σ) I →+*
    AffineDeformationSpace.extendedRees (Ext A σ) (extIdeal I) :=
  ((translate A σ).comp (AffineDeformationSpace.extendedRees (Amb A σ) I).val.toRingHom).codRestrict
    _ fun f ↦ translate_mem I f.2

@[simp] theorem coe_translateRees (f : AffineDeformationSpace.extendedRees (Amb A σ) I) :
    (translateRees I f : (Ext A σ)[T;T⁻¹]) = translate A σ f := rfl

theorem translateRees_parameter :
    translateRees I (AffineDeformationSpace.parameter (Amb A σ) I) =
      AffineDeformationSpace.parameter (Ext A σ) (extIdeal I) := by
  apply Subtype.ext
  rw [coe_translateRees, AffineDeformationSpace.coe_parameter,
    AffineDeformationSpace.coe_parameter, translate_T]

/-- The translation on the special fibre `t⁻¹ = 0` of the deformation space. -/
def translateFibre : AffineDeformationSpace.specialFibreRing (Amb A σ) I →+*
    AffineDeformationSpace.specialFibreRing (Ext A σ) (extIdeal I) :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (translateRees I)) (by
    intro a ha
    rw [Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [RingHom.comp_apply, map_mul, translateRees_parameter, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

theorem translateFibre_mk (f : AffineDeformationSpace.extendedRees (Amb A σ) I) :
    translateFibre I (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (translateRees I f) :=
  Ideal.Quotient.lift_mk _ _ _

/-- Degree-zero elements are fixed by the translation on the special fibre: the action is a
morphism over `U`. -/
theorem translateFibre_algebraMap (r : Amb A σ) :
    translateFibre I (Ideal.Quotient.mk _ (algebraMap _ _ r)) =
      Ideal.Quotient.mk _ (algebraMap (Ext A σ) _ (MvPolynomial.C r)) := by
  rw [translateFibre_mk, ← sub_eq_zero, ← map_sub]
  obtain ⟨g, hg, h⟩ := exists_translateLaurent_eq (extIdeal I) r
  refine AffineDeformationSpace.mk_eq_zero_of_eq_parameter_mul _ _
    (h := LaurentPolynomial.C (taylor A σ r) + g * T (-1))
    (add_mem (AffineDeformationSpace.isExtendedRees_C _ _ _) (mul_mem hg (T_neg_mem I 1))) ?_
  rw [Subalgebra.coe_sub, coe_translateRees, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap,
    ← C_eq_algebraMap, ← C_eq_algebraMap, translate_C, h, add_mul, mul_assoc, ← T_add]
  norm_num
  ring

/-- The translation of a degree-one element on the special fibre: `[f t] ↦ [f t] + [Df]`. -/
theorem translateFibre_degreeOne (x : I) :
    translateFibre I (Ideal.Quotient.mk _ (AffineDeformationSpace.degreeOne (Amb A σ) I x)) =
      Ideal.Quotient.mk _ (AffineDeformationSpace.degreeOne (Ext A σ) (extIdeal I)
        ⟨MvPolynomial.C (x : Amb A σ), Ideal.mem_map_of_mem _ x.2⟩) +
      Ideal.Quotient.mk _ (algebraMap (Ext A σ) _ (taylor A σ x)) := by
  rw [translateFibre_mk, ← map_add, ← sub_eq_zero, ← map_sub]
  obtain ⟨g, hg, h⟩ := exists_translateLaurent_eq (extIdeal I) x
  refine AffineDeformationSpace.mk_eq_zero_of_eq_parameter_mul _ _ (h := g) hg ?_
  rw [Subalgebra.coe_sub, Subalgebra.coe_add, coe_translateRees, Subalgebra.coe_algebraMap,
    ← C_eq_algebraMap, AffineDeformationSpace.coe_degreeOne, AffineDeformationSpace.coe_degreeOne,
    translate_C_mul_T, h]
  simp only [add_mul, mul_assoc, ← T_add]
  norm_num

/-! ### The coaction on the associated graded ring -/

/-- The associated graded ring `gr_I(R)`, the coordinate ring of the affine normal cone. -/
abbrev Gr : Type u := AffineNormalCone.associatedGradedRing (Amb A σ) I

/-- Shortcut instance: instance search fails to rebuild the ring structure of `gr_I(R)`, a
quotient of a subalgebra, inside nested searches. -/
instance instCommRingGr : CommRing (Gr I) := Ideal.Quotient.commRing _

/-- Shortcut instance for polynomials over `gr_I(R)`. -/
instance instCommRingPolyGr : CommRing (MvPolynomial σ (Gr I)) := AddMonoidAlgebra.commRing

/-- Shortcut instance for polynomials in two sets of variables over `gr_I(R)`. -/
instance instCommRingPolyPolyGr : CommRing (MvPolynomial σ (MvPolynomial σ (Gr I))) :=
  AddMonoidAlgebra.commRing

/-- The special fibre of the base-changed deformation space is `gr_I(R)[ε]`: the composite
`R[ε][I t, t⁻¹]/(t⁻¹) ≅ gr_{I R[ε]}(R[ε]) ≅ R[ε] ⊗_R gr_I(R) ≅ gr_I(R) ⊗_R R[ε] ≅ gr_I(R)[ε]`. -/
def fibreToPolynomial :
    AffineDeformationSpace.specialFibreRing (Ext A σ) (extIdeal I) →+* MvPolynomial σ (Gr I) :=
  (MvPolynomial.algebraTensorAlgEquiv (σ := σ) (Amb A σ) (Gr I)).toRingEquiv.toRingHom.comp <|
    (Algebra.TensorProduct.comm (Amb A σ) (Ext A σ) (Gr I)).toRingEquiv.toRingHom.comp <|
      (AffineNormalCone.grTensorEquiv (A := Amb A σ) (B := Ext A σ) I (extIdeal I)
        rfl).symm.toRingEquiv.toRingHom.comp
        (AffineDeformationSpace.specialFibreEquiv (Ext A σ) (extIdeal I)).symm.toRingEquiv.toRingHom

theorem fibreToPolynomial_apply (z) :
    fibreToPolynomial I z = MvPolynomial.algebraTensorAlgEquiv (σ := σ) (Amb A σ) (Gr I)
      (Algebra.TensorProduct.comm (Amb A σ) (Ext A σ) (Gr I)
        ((AffineNormalCone.grTensorEquiv (A := Amb A σ) (B := Ext A σ) I (extIdeal I) rfl).symm
          ((AffineDeformationSpace.specialFibreEquiv (Ext A σ) (extIdeal I)).symm z))) := rfl

theorem fibreToPolynomial_algebraMap (s : Ext A σ) :
    fibreToPolynomial I (Ideal.Quotient.mk _ (algebraMap (Ext A σ) _ s)) =
      MvPolynomial.map (algebraMap (Amb A σ) (Gr I)) s := by
  rw [fibreToPolynomial_apply]
  have h1 : (AffineDeformationSpace.specialFibreEquiv (Ext A σ) (extIdeal I)).symm
      (Ideal.Quotient.mk _ (algebraMap (Ext A σ) _ s)) = algebraMap (Ext A σ) _ s :=
    (AffineDeformationSpace.specialFibreEquiv (Ext A σ) (extIdeal I)).symm.commutes s
  have h2 : (AffineNormalCone.grTensorEquiv (A := Amb A σ) (B := Ext A σ) I (extIdeal I)
      rfl).symm (algebraMap (Ext A σ) _ s) = s ⊗ₜ[Amb A σ] (1 : Gr I) :=
    (AffineNormalCone.grTensorEquiv (A := Amb A σ) (B := Ext A σ) I (extIdeal I)
      rfl).symm.commutes s
  rw [h1, h2, Algebra.TensorProduct.comm_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]

theorem specialFibreEquiv_mk_degreeOneRees {S : Type u} [CommRing S] (J : Ideal S) (y : J) :
    AffineDeformationSpace.specialFibreEquiv S J
        (Ideal.Quotient.mk _ (AffineNormalCone.degreeOneRees S J y)) =
      Ideal.Quotient.mk _ (AffineDeformationSpace.degreeOne S J y) := by
  rw [AffineDeformationSpace.specialFibreEquiv_mk, AffineDeformationSpace.reesToSpecialFibre_apply]
  congr 1
  apply Subtype.ext
  rw [AffineDeformationSpace.coe_reesToExtended, AffineDeformationSpace.coe_degreeOne,
    AffineNormalCone.coe_degreeOneRees, Polynomial.toLaurent_C_mul_T]
  simp

theorem fibreToPolynomial_degreeOne (x : I) :
    fibreToPolynomial I (Ideal.Quotient.mk _
      (AffineDeformationSpace.degreeOne (Ext A σ) (extIdeal I)
        ⟨MvPolynomial.C (x : Amb A σ), Ideal.mem_map_of_mem _ x.2⟩)) =
      MvPolynomial.C (Ideal.Quotient.mk _ (AffineNormalCone.degreeOneRees (Amb A σ) I x)) := by
  rw [fibreToPolynomial_apply]
  have h1 : (AffineDeformationSpace.specialFibreEquiv (Ext A σ) (extIdeal I)).symm
      (Ideal.Quotient.mk _ (AffineDeformationSpace.degreeOne (Ext A σ) (extIdeal I)
        ⟨MvPolynomial.C (x : Amb A σ), Ideal.mem_map_of_mem _ x.2⟩)) =
      Ideal.Quotient.mk _ (AffineNormalCone.degreeOneRees (Ext A σ) (extIdeal I)
        ⟨MvPolynomial.C (x : Amb A σ), Ideal.mem_map_of_mem _ x.2⟩) := by
    rw [AlgEquiv.symm_apply_eq, specialFibreEquiv_mk_degreeOneRees]
  have h2 : (AffineNormalCone.grTensorEquiv (A := Amb A σ) (B := Ext A σ) I (extIdeal I)
      rfl).symm (Ideal.Quotient.mk _ (AffineNormalCone.degreeOneRees (Ext A σ) (extIdeal I)
        ⟨MvPolynomial.C (x : Amb A σ), Ideal.mem_map_of_mem _ x.2⟩)) =
      (1 : Ext A σ) ⊗ₜ[Amb A σ]
        Ideal.Quotient.mk _ (AffineNormalCone.degreeOneRees (Amb A σ) I x) := by
    rw [AlgEquiv.symm_apply_eq, AffineNormalCone.grTensorEquiv_one_tmul_mk,
      AffineNormalCone.grMapOfEq_mk, AffineNormalCone.reesMapOfEq_degreeOneRees]
    rfl
  rw [h1, h2, Algebra.TensorProduct.comm_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul, map_one,
    MvPolynomial.smul_eq_C_mul, mul_one]

/-- The coaction `gr_I(R) → gr_I(R)[ε]` of the tangent translation on the affine normal cone,
obtained from the translation of the deformation space on the special fibre.  It is `R`-linear:
the action is a morphism over `U = Spec (R/I)`. -/
def coaction : Gr I →ₐ[Amb A σ] MvPolynomial σ (Gr I) where
  toRingHom := (fibreToPolynomial I).comp ((translateFibre I).comp
    (AffineDeformationSpace.specialFibreEquiv (Amb A σ) I).toRingEquiv.toRingHom)
  commutes' r := by
    change fibreToPolynomial I (translateFibre I
      (AffineDeformationSpace.specialFibreEquiv (Amb A σ) I (algebraMap _ _ r))) = _
    rw [AlgEquiv.commutes]
    change fibreToPolynomial I (translateFibre I (Ideal.Quotient.mk _ (algebraMap _ _ r))) = _
    rw [translateFibre_algebraMap, fibreToPolynomial_algebraMap, MvPolynomial.map_C,
      MvPolynomial.algebraMap_apply]

theorem coaction_apply (z : Gr I) :
    coaction I z = fibreToPolynomial I (translateFibre I
      (AffineDeformationSpace.specialFibreEquiv (Amb A σ) I z)) := rfl

theorem coaction_algebraMap (r : Amb A σ) :
    coaction I (algebraMap (Amb A σ) (Gr I) r) =
      MvPolynomial.C (algebraMap (Amb A σ) (Gr I) r) := by
  rw [AlgHom.commutes, MvPolynomial.algebraMap_apply]

/-- The coaction on a degree-one element: `[f t] ↦ [f t] + Σ_i ε_i [∂_i f]`. -/
theorem coaction_degreeOne (x : I) :
    coaction I (Ideal.Quotient.mk _ (AffineNormalCone.degreeOneRees (Amb A σ) I x)) =
      MvPolynomial.C (Ideal.Quotient.mk _ (AffineNormalCone.degreeOneRees (Amb A σ) I x)) +
        MvPolynomial.map (algebraMap (Amb A σ) (Gr I)) (taylor A σ x) := by
  rw [coaction_apply, specialFibreEquiv_mk_degreeOneRees, translateFibre_degreeOne, map_add,
    fibreToPolynomial_degreeOne, fibreToPolynomial_algebraMap]

/-! ### Extensionality for maps out of `gr_I(R)` -/

/-- Two `R`-algebra maps out of `gr_I(R)` agreeing on the degree-one classes are equal. -/
theorem gr_algHom_ext {T : Type u} [CommSemiring T] [Algebra (Amb A σ) T] {f g : Gr I →ₐ[Amb A σ] T}
    (h : ∀ x : I, f (Ideal.Quotient.mk _ (AffineNormalCone.degreeOneRees (Amb A σ) I x)) =
      g (Ideal.Quotient.mk _ (AffineNormalCone.degreeOneRees (Amb A σ) I x))) : f = g := by
  have key : (f.comp (Ideal.Quotient.mkₐ (Amb A σ) _)).comp (AffineNormalCone.symToRees _ I) =
      (g.comp (Ideal.Quotient.mkₐ (Amb A σ) _)).comp (AffineNormalCone.symToRees _ I) := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x ↦ ?_)
    simpa [AffineNormalCone.symToRees_ι] using h x
  ext z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨s, rfl⟩ := AffineNormalCone.symToRees_surjective _ I p
  exact DFunLike.congr_fun key s

/-- Two ring maps out of `gr_I(R)` agreeing on degree zero and on the degree-one classes are
equal. -/
theorem gr_ringHom_ext {T : Type u} [CommSemiring T] {f g : Gr I →+* T}
    (h0 : ∀ r : Amb A σ, f (algebraMap _ _ r) = g (algebraMap _ _ r))
    (h1 : ∀ x : I, f (Ideal.Quotient.mk _ (AffineNormalCone.degreeOneRees (Amb A σ) I x)) =
      g (Ideal.Quotient.mk _ (AffineNormalCone.degreeOneRees (Amb A σ) I x))) : f = g := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun p ↦ ?_)
  obtain ⟨s, rfl⟩ := AffineNormalCone.symToRees_surjective _ I p
  induction s using SymmetricAlgebra.induction with
  | algebraMap r =>
    have e : (AffineNormalCone.symToRees (Amb A σ) I) (algebraMap _ _ r) = algebraMap _ _ r :=
      AlgHom.commutes _ r
    simpa [e] using h0 r
  | ι x => simpa [AffineNormalCone.symToRees_ι] using h1 x
  | mul a b ha hb => simp only [RingHom.comp_apply, map_mul] at ha hb ⊢; rw [ha, hb]
  | add a b ha hb => simp only [RingHom.comp_apply, map_add] at ha hb ⊢; rw [ha, hb]

/-! ### Linearity of the Taylor term in the tangent direction -/

variable {I}

theorem eval₂_taylor_add {B : Type u} [CommSemiring B] (ψ : Amb A σ →+* B) (v w : σ → B)
    (f : Amb A σ) :
    MvPolynomial.eval₂ ψ (v + w) (taylor A σ f) =
      MvPolynomial.eval₂ ψ v (taylor A σ f) + MvPolynomial.eval₂ ψ w (taylor A σ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp only [map_add, MvPolynomial.eval₂_add, hf, hg]; ring
  | mul_X f i hf =>
    simp only [taylor_mul, taylor_X, MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, hf, Pi.add_apply]
    ring

theorem eval₂_taylor_add' {B : Type u} [CommSemiring B] (ψ : Amb A σ →+* B) (v w : σ → B)
    (f : Amb A σ) :
    MvPolynomial.eval₂ ψ (fun i ↦ v i + w i) (taylor A σ f) =
      MvPolynomial.eval₂ ψ v (taylor A σ f) + MvPolynomial.eval₂ ψ w (taylor A σ f) :=
  eval₂_taylor_add ψ v w f

theorem eval₂_taylor_zero {B : Type u} [CommSemiring B] (ψ : Amb A σ →+* B) (f : Amb A σ) :
    MvPolynomial.eval₂ ψ 0 (taylor A σ f) = 0 := by
  change MvPolynomial.eval₂ ψ (fun _ ↦ 0) (taylor A σ f) = 0
  rw [MvPolynomial.eval₂_zero'_apply, constantCoeff_taylor, map_zero]

variable (I)

/-! ### The action on points -/

/-- Translating a `B`-point `φ` of the normal cone by a `B`-point `v` of `𝔸^σ`, the fibre of the
tangent bundle. -/
def translatePoint {B : Type u} [CommRing B] (φ : Gr I →+* B) (v : σ → B) : Gr I →+* B :=
  (MvPolynomial.eval₂Hom φ v).comp (coaction I).toRingHom

theorem translatePoint_algebraMap {B : Type u} [CommRing B] (φ : Gr I →+* B) (v : σ → B)
    (r : Amb A σ) : translatePoint I φ v (algebraMap (Amb A σ) (Gr I) r) =
      φ (algebraMap (Amb A σ) (Gr I) r) := by
  change MvPolynomial.eval₂Hom φ v (coaction I (algebraMap (Amb A σ) (Gr I) r)) = _
  rw [coaction_algebraMap, MvPolynomial.eval₂Hom_C]

theorem translatePoint_degreeOne {B : Type u} [CommRing B] (φ : Gr I →+* B) (v : σ → B)
    (x : I) :
    translatePoint I φ v (Ideal.Quotient.mk _ (AffineNormalCone.degreeOneRees (Amb A σ) I x)) =
      φ (Ideal.Quotient.mk _ (AffineNormalCone.degreeOneRees (Amb A σ) I x)) +
        MvPolynomial.eval₂ (φ.comp (algebraMap (Amb A σ) (Gr I))) v (taylor A σ x) := by
  change MvPolynomial.eval₂Hom φ v (coaction I _) = _
  rw [coaction_degreeOne, map_add, MvPolynomial.eval₂Hom_C, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_map]

/-- Translating by the zero section does nothing. -/
theorem translatePoint_zero {B : Type u} [CommRing B] (φ : Gr I →+* B) :
    translatePoint I φ 0 = φ := by
  refine gr_ringHom_ext I (fun r ↦ translatePoint_algebraMap I φ 0 r) fun x ↦ ?_
  rw [translatePoint_degreeOne, eval₂_taylor_zero, add_zero]

/-- Translating twice is translating by the sum. -/
theorem translatePoint_add {B : Type u} [CommRing B] (φ : Gr I →+* B) (v w : σ → B) :
    translatePoint I (translatePoint I φ v) w = translatePoint I φ (v + w) := by
  refine gr_ringHom_ext I (fun r ↦ ?_) fun x ↦ ?_
  · rw [translatePoint_algebraMap, translatePoint_algebraMap, translatePoint_algebraMap]
  · have e : (translatePoint I φ v).comp (algebraMap (Amb A σ) (Gr I)) =
        φ.comp (algebraMap (Amb A σ) (Gr I)) :=
      RingHom.ext fun r ↦ translatePoint_algebraMap I φ v r
    rw [translatePoint_degreeOne, translatePoint_degreeOne, translatePoint_degreeOne, e,
      eval₂_taylor_add, add_assoc]

/-! ### The counit and coassociativity laws -/

/-- The counit law: evaluating the tangent coordinates at `0` recovers the identity. -/
theorem coaction_counit :
    (MvPolynomial.eval₂Hom (RingHom.id (Gr I)) fun _ : σ ↦ (0 : Gr I)).comp
      (coaction I).toRingHom = RingHom.id (Gr I) := by
  have key := gr_ringHom_ext I (T := Gr I)
    (f := (MvPolynomial.eval₂Hom (RingHom.id (Gr I)) fun _ : σ ↦ (0 : Gr I)).comp
      (coaction I).toRingHom) (g := RingHom.id (Gr I)) ?_ ?_
  · exact key
  · intro r
    change MvPolynomial.eval₂Hom (RingHom.id (Gr I)) (fun _ : σ ↦ (0 : Gr I))
      (coaction I (algebraMap _ _ r)) = _
    rw [coaction_algebraMap, MvPolynomial.eval₂Hom_C, RingHom.id_apply]
  · intro x
    change MvPolynomial.eval₂Hom (RingHom.id (Gr I)) (fun _ : σ ↦ (0 : Gr I)) (coaction I _) = _
    rw [coaction_degreeOne, map_add, MvPolynomial.eval₂Hom_C, RingHom.id_apply,
      MvPolynomial.eval₂Hom_zero'_apply, MvPolynomial.constantCoeff_map, constantCoeff_taylor,
      map_zero, map_zero, add_zero]

theorem aeval_zero_coaction (z : Gr I) :
    MvPolynomial.aeval (fun _ : σ ↦ (0 : Gr I)) (coaction I z) = z := by
  have := RingHom.congr_fun (coaction_counit I) z
  rw [MvPolynomial.aeval_eq_eval₂Hom, Algebra.algebraMap_self]
  exact this

/-- The coassociativity law: translating by `ε` and then by `ε'` is translating by `ε + ε'`. -/
theorem coaction_coassoc :
    (MvPolynomial.map (coaction I).toRingHom).comp (coaction I).toRingHom =
      (MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C) fun i : σ ↦
        MvPolynomial.C (MvPolynomial.X i : MvPolynomial σ (Gr I)) + MvPolynomial.X i).comp
          (coaction I).toRingHom := by
  have hC : MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C)
      (fun i : σ ↦ MvPolynomial.C (MvPolynomial.X i : MvPolynomial σ (Gr I))) =
      (MvPolynomial.C : MvPolynomial σ (Gr I) →+* MvPolynomial σ (MvPolynomial σ (Gr I))) :=
    MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun i ↦ by simp)
  have h := translatePoint_add I (MvPolynomial.C.comp MvPolynomial.C)
    (fun i : σ ↦ MvPolynomial.C (MvPolynomial.X i : MvPolynomial σ (Gr I)))
    (fun i : σ ↦ MvPolynomial.X i)
  unfold translatePoint at h
  rw [hC, show ((fun i : σ ↦ MvPolynomial.C (MvPolynomial.X i : MvPolynomial σ (Gr I))) +
    fun i ↦ MvPolynomial.X i) = fun i ↦ MvPolynomial.C (MvPolynomial.X i) + MvPolynomial.X i from
    rfl] at h
  have hmap : MvPolynomial.map (σ := σ) (coaction I).toRingHom =
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp (coaction I).toRingHom) fun i ↦ MvPolynomial.X i :=
    MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun i ↦ by simp)
  rw [hmap]
  exact h

/-! ### Equivariance of the closed immersion into the normal sheaf -/

/-- The coordinate ring `Sym_R(I)/I·Sym_R(I)` of the normal sheaf. -/
abbrev Ns : Type u := AffineNormalCone.normalSheafRing (Amb A σ) I

/-- Shortcut instance, as for `gr_I(R)`. -/
instance instCommRingNs : CommRing (Ns I) := Ideal.Quotient.commRing _

/-- Shortcut instance for polynomials over the normal-sheaf ring. -/
instance instCommRingPolyNs : CommRing (MvPolynomial σ (Ns I)) := AddMonoidAlgebra.commRing

theorem algebraMap_ns_eq_zero {x : Amb A σ} (hx : x ∈ I) : algebraMap (Amb A σ) (Ns I) x = 0 := by
  change Ideal.Quotient.mk _ (algebraMap (Amb A σ) (SymmetricAlgebra (Amb A σ) I) x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ hx

/-- The linear map `x ↦ [x] + Σ_i ε_i [∂_i x]` from `I` to `(Sym(I)/I·Sym(I))[ε]`, the derivative
of the translation. -/
def nsCoactionLinear : I →ₗ[Amb A σ] MvPolynomial σ (Ns I) where
  toFun x := MvPolynomial.C (Ideal.Quotient.mk _ (SymmetricAlgebra.ι (Amb A σ) I x)) +
    MvPolynomial.map (algebraMap (Amb A σ) (Ns I)) (taylor A σ x)
  map_add' x y := by
    simp only [map_add, Submodule.coe_add]
    ring
  map_smul' r x := by
    have hx : algebraMap (Amb A σ) (Ns I) x = 0 := algebraMap_ns_eq_zero I x.2
    have hr : Ideal.Quotient.mk _ (algebraMap (Amb A σ) (SymmetricAlgebra (Amb A σ) I) r) =
      algebraMap (Amb A σ) (Ns I) r := rfl
    simp only [RingHom.id_apply, map_smul, Submodule.coe_smul, smul_eq_mul, taylor_mul, map_add,
      map_mul, MvPolynomial.map_C, hx, MvPolynomial.C_0, zero_mul, add_zero, Algebra.smul_def,
      MvPolynomial.algebraMap_apply, hr]
    ring

theorem nsCoactionLinear_apply (x : I) :
    nsCoactionLinear I x = MvPolynomial.C (Ideal.Quotient.mk _ (SymmetricAlgebra.ι (Amb A σ) I x)) +
      MvPolynomial.map (algebraMap (Amb A σ) (Ns I)) (taylor A σ x) := rfl

theorem lift_nsCoactionLinear_eq_zero :
    ∀ a ∈ Ideal.map (algebraMap (Amb A σ) (SymmetricAlgebra (Amb A σ) I)) I,
      SymmetricAlgebra.lift (nsCoactionLinear I) a = 0 := by
  intro a ha
  have hle : Ideal.map (algebraMap (Amb A σ) (SymmetricAlgebra (Amb A σ) I)) I ≤
      RingHom.ker (SymmetricAlgebra.lift (nsCoactionLinear I)).toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change SymmetricAlgebra.lift (nsCoactionLinear I) (algebraMap _ _ r) = 0
    rw [AlgHom.commutes, MvPolynomial.algebraMap_apply, algebraMap_ns_eq_zero I hr,
      MvPolynomial.C_0]
  exact RingHom.mem_ker.mp (hle ha)

/-- The translation coaction `Sym(I)/I·Sym(I) → (Sym(I)/I·Sym(I))[ε]` of the tangent bundle on the
affine normal sheaf. -/
def nsCoaction : Ns I →ₐ[Amb A σ] MvPolynomial σ (Ns I) :=
  Ideal.Quotient.liftₐ _ (SymmetricAlgebra.lift (nsCoactionLinear I))
    (lift_nsCoactionLinear_eq_zero I)

theorem nsCoaction_mk_ι (x : I) :
    nsCoaction I (Ideal.Quotient.mk _ (SymmetricAlgebra.ι (Amb A σ) I x)) =
      MvPolynomial.C (Ideal.Quotient.mk _ (SymmetricAlgebra.ι (Amb A σ) I x)) +
        MvPolynomial.map (algebraMap (Amb A σ) (Ns I)) (taylor A σ x) := by
  have h := DFunLike.congr_fun (Ideal.Quotient.liftₐ_comp _
    (SymmetricAlgebra.lift (nsCoactionLinear I)) (lift_nsCoactionLinear_eq_zero I))
    (SymmetricAlgebra.ι (Amb A σ) I x)
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, SymmetricAlgebra.lift_ι_apply] at h
  exact h

/-- Vistoli's lemma in the polynomial model: the closed immersion `C_{U/M} → N_{U/M}` is
equivariant for the tangent translation, i.e. the coaction of the normal cone is compatible with
the translation coaction of the normal sheaf through the surjection `Sym(I)/I·Sym(I) ↠ gr_I(R)`.
Equivalently, the translation action on the normal sheaf preserves the normal cone. -/
theorem coaction_comp_nsToGr :
    (coaction I).comp (AffineNormalCone.nsToGr (Amb A σ) I) =
      (MvPolynomial.mapAlgHom (AffineNormalCone.nsToGr (Amb A σ) I)).comp (nsCoaction I) := by
  have key : ((coaction I).comp (AffineNormalCone.nsToGr (Amb A σ) I)).comp
      (Ideal.Quotient.mkₐ (Amb A σ) _) =
      ((MvPolynomial.mapAlgHom (AffineNormalCone.nsToGr (Amb A σ) I)).comp (nsCoaction I)).comp
        (Ideal.Quotient.mkₐ (Amb A σ) _) := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x ↦ ?_)
    change coaction I (AffineNormalCone.nsToGr (Amb A σ) I
        (Ideal.Quotient.mk _ (SymmetricAlgebra.ι (Amb A σ) I x))) =
      MvPolynomial.mapAlgHom (AffineNormalCone.nsToGr (Amb A σ) I)
        (nsCoaction I (Ideal.Quotient.mk _ (SymmetricAlgebra.ι (Amb A σ) I x)))
    rw [AffineNormalCone.nsToGr_mk, AffineNormalCone.symToRees_ι, coaction_degreeOne,
      nsCoaction_mk_ι, map_add, MvPolynomial.mapAlgHom_apply, MvPolynomial.map_C,
      MvPolynomial.mapAlgHom_apply, MvPolynomial.map_map, AlgHom.coe_toRingHom,
      AffineNormalCone.nsToGr_mk, AffineNormalCone.symToRees_ι, AlgHom.comp_algebraMap]
  refine AlgHom.ext fun z ↦ ?_
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact DFunLike.congr_fun key s

/-- Translating a `B`-point of the normal sheaf. -/
def nsTranslatePoint {B : Type u} [CommRing B] (φ : Ns I →+* B) (v : σ → B) : Ns I →+* B :=
  (MvPolynomial.eval₂Hom φ v).comp (nsCoaction I).toRingHom

/-- On `B`-points: translating a point of the cone, viewed in the normal sheaf, is translating it
in the normal sheaf. -/
theorem nsTranslatePoint_comp_nsToGr {B : Type u} [CommRing B] (φ : Gr I →+* B) (v : σ → B) :
    nsTranslatePoint I (φ.comp (AffineNormalCone.nsToGr (Amb A σ) I).toRingHom) v =
      (translatePoint I φ v).comp (AffineNormalCone.nsToGr (Amb A σ) I).toRingHom := by
  have h : (coaction I).toRingHom.comp (AffineNormalCone.nsToGr (Amb A σ) I).toRingHom =
      (MvPolynomial.mapAlgHom (AffineNormalCone.nsToGr (Amb A σ) I)).toRingHom.comp
        (nsCoaction I).toRingHom :=
    congrArg AlgHom.toRingHom (coaction_comp_nsToGr I)
  rw [nsTranslatePoint, translatePoint, RingHom.comp_assoc, h, ← RingHom.comp_assoc]
  congr 1
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
  · simp
  · simp

/-! ### The action as a morphism of schemes -/

open CategoryTheory

/-- The total space `T_M|_U ×_U C_{U/M} = C_{U/M} × 𝔸^σ`. -/
abbrev actionSpace : _root_.AlgebraicGeometry.Scheme.{u} :=
  _root_.AlgebraicGeometry.Spec (.of (MvPolynomial σ (Gr I)))

/-- The action `T_M|_U ×_U C_{U/M} → C_{U/M}` of the tangent bundle on the affine normal cone. -/
def actionMap : actionSpace I ⟶ AffineNormalCone.scheme (Amb A σ) I :=
  _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom (coaction I).toRingHom)

/-- The projection `C_{U/M} × 𝔸^σ → C_{U/M}`. -/
def actionProjection : actionSpace I ⟶ AffineNormalCone.scheme (Amb A σ) I :=
  _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom MvPolynomial.C)

/-- The zero section `C_{U/M} → C_{U/M} × 𝔸^σ`. -/
def actionZeroSection : AffineNormalCone.scheme (Amb A σ) I ⟶ actionSpace I :=
  _root_.AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (MvPolynomial.eval₂Hom (RingHom.id (Gr I)) fun _ ↦ 0))

/-- The unit law of the action. -/
theorem actionZeroSection_comp_actionMap : actionZeroSection I ≫ actionMap I = 𝟙 _ := by
  rw [actionZeroSection, actionMap, ← _root_.AlgebraicGeometry.Spec.map_comp,
    ← CommRingCat.ofHom_comp, coaction_counit, CommRingCat.ofHom_id,
    _root_.AlgebraicGeometry.Spec.map_id]

theorem coaction_comp_base :
    (coaction I).toRingHom.comp (AffineNormalCone.associatedGradedBaseRingHom (Amb A σ) I) =
      (MvPolynomial.C : Gr I →+* MvPolynomial σ (Gr I)).comp
        (AffineNormalCone.associatedGradedBaseRingHom (Amb A σ) I) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r ↦ ?_)
  change coaction I (Ideal.Quotient.mk _ (algebraMap _ _ r)) =
    MvPolynomial.C (Ideal.Quotient.mk _ (algebraMap _ _ r))
  exact coaction_algebraMap I r

/-- The action is a morphism over `U = Spec (R/I)`. -/
theorem actionMap_comp_projection :
    actionMap I ≫ AffineNormalCone.projection (Amb A σ) I =
      actionProjection I ≫ AffineNormalCone.projection (Amb A σ) I := by
  rw [actionMap, actionProjection, AffineNormalCone.projection,
    ← _root_.AlgebraicGeometry.Spec.map_comp, ← _root_.AlgebraicGeometry.Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, coaction_comp_base]

/-- The associativity law of the action, as morphisms `C_{U/M} × 𝔸^σ × 𝔸^σ → C_{U/M}`. -/
theorem actionMap_assoc :
    _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (MvPolynomial.map (coaction I).toRingHom)) ≫ actionMap I =
      _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C) fun i : σ ↦
          MvPolynomial.C (MvPolynomial.X i : MvPolynomial σ (Gr I)) + MvPolynomial.X i)) ≫
        actionMap I := by
  rw [actionMap, ← _root_.AlgebraicGeometry.Spec.map_comp, ← _root_.AlgebraicGeometry.Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, coaction_coassoc]

/-- The affine closed immersion of the normal cone into the normal sheaf, in the presentation
`Sym(I)/I·Sym(I)` of `Cones/NormalConeGlobal.lean`. -/
def coneToNs : AffineNormalCone.scheme (Amb A σ) I ⟶
    _root_.AlgebraicGeometry.Spec (.of (Ns I)) :=
  _root_.AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (AffineNormalCone.nsToGr (Amb A σ) I).toRingHom)

/-- The translation action of the tangent bundle on the normal sheaf. -/
def nsActionMap : _root_.AlgebraicGeometry.Spec (.of (MvPolynomial σ (Ns I))) ⟶
    _root_.AlgebraicGeometry.Spec (.of (Ns I)) :=
  _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom (nsCoaction I).toRingHom)

/-- Vistoli's lemma as a commutative square of schemes: the closed immersion `C_{U/M} → N_{U/M}` is
equivariant for the translation actions of `T_M|_U`. -/
theorem actionMap_comp_coneToNs :
    actionMap I ≫ coneToNs I =
      _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (MvPolynomial.mapAlgHom (AffineNormalCone.nsToGr (Amb A σ) I)).toRingHom) ≫
        nsActionMap I := by
  rw [actionMap, coneToNs, nsActionMap, ← _root_.AlgebraicGeometry.Spec.map_comp,
    ← _root_.AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact congrArg AlgHom.toRingHom (coaction_comp_nsToGr I)

end

end ConeTranslation

end GromovWitten.AlgebraicGeometry
