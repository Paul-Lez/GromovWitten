/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.RelativeSpec
import GromovWitten.AlgebraicGeometry.Cones.Affine
import GromovWitten.AlgebraicGeometry.Cones.Graded
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# The normal cone and normal sheaf of a closed immersion of schemes

For a quasi-coherent ideal sheaf `I` on a scheme `X`, the *normal cone* `C_{Z/X}` of the closed
subscheme `Z = V(I)` is the relative `Spec` over `X` of the associated graded algebras
`gr_{I(U)}(Γ(X, U)) = ⊕ I(U)ⁿ/I(U)ⁿ⁺¹` of the affine opens, and the *normal sheaf* `N_{Z/X}` is
the relative `Spec` of the symmetric algebras `Sym(I(U)) ⊗ Γ(X, U)/I(U)`, i.e. of
`Sym_{Γ/I}(I/I²)`.  Both are glued with `RelativeSpec` from the affine constructions of
`Cones/Affine.lean`; the required base-change squares along the restriction maps of affine opens
are proved from the flatness of these restriction maps: the Rees algebra commutes with flat base
change (`ReesBlowup.reesBaseChangeMap`), the symmetric algebra commutes with arbitrary base change
(`GradedCone.baseChangeEquiv`), and quotients by extended ideals commute with arbitrary base
change (`quotBaseChangeEquiv`, from Mathlib's `Algebra.TensorProduct.tensorQuotientEquiv`).

The canonical surjection `Sym(I) → Rees(I)` onto the degree-one generators then descends to a
compatible family of surjections `Sym(I/I²) → gr_I`, hence to a closed immersion of the normal
cone into the normal sheaf over `X` (`normalConeToNormalSheaf`), globalizing the affine
`AffineNormalCone.coneToNormalSheaf`.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Polynomial
open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry

open GlobalBlowup RelativeSpec AffineNormalCone ReesBlowupOfEq

universe u

noncomputable section

/-! ### Base change of quotients by extended ideals -/

section QuotientBaseChange

variable {A B S T : Type u} [CommRing A] [CommRing B] [CommRing S] [CommRing T]
  [Algebra A B] [Algebra A S] [Algebra B T] (ρ : B ⊗[A] S ≃ₐ[B] T) (I : Ideal A)

theorem algEquiv_one_tmul_algebraMap (a : A) :
    ρ ((1 : B) ⊗ₜ[A] algebraMap A S a) = algebraMap B T (algebraMap A B a) := by
  have h1 : (1 : B) ⊗ₜ[A] algebraMap A S a = algebraMap A (B ⊗[A] S) a := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [h1, IsScalarTower.algebraMap_apply A B (B ⊗[A] S), AlgEquiv.commutes]

/-- The extended ideal of `I` in `T` is the image under `ρ` of the extended ideal of `I` in
`B ⊗ S` through `S`. -/
theorem map_algebraMap_map_eq :
    (I.map (algebraMap A B)).map (algebraMap B T) =
      ((I.map (algebraMap A S)).map
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := S))).map
          (ρ : B ⊗[A] S →+* T) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, ← algEquiv_one_tmul_algebraMap ρ a]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha))
  · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap]
    change ρ (Algebra.TensorProduct.includeRight (algebraMap A S a)) ∈ _
    rw [Algebra.TensorProduct.includeRight_apply, algEquiv_one_tmul_algebraMap ρ a]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)

/-- Base change of the quotient `S/IS` along `A → B` is the quotient `T/IT`, when
`T = B ⊗ S`. -/
def quotBaseChangeEquiv :
    B ⊗[A] (S ⧸ I.map (algebraMap A S)) ≃ₐ[B]
      T ⧸ (I.map (algebraMap A B)).map (algebraMap B T) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := A) B S B (I.map (algebraMap A S))).trans
    (Ideal.quotientEquivAlg _ _ ρ (map_algebraMap_map_eq ρ I))

theorem quotBaseChangeEquiv_one_tmul_mk (s : S) :
    quotBaseChangeEquiv ρ I ((1 : B) ⊗ₜ[A] Ideal.Quotient.mk _ s) =
      Ideal.Quotient.mk _ (ρ ((1 : B) ⊗ₜ[A] s)) :=
  rfl

end QuotientBaseChange

/-! ### Flat base change of Rees algebras and associated graded rings -/

namespace AffineNormalCone

section Rees

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A) (J : Ideal B)
  (hJ : I.map (algebraMap A B) = J)

theorem reesMapOfEq_algebraMap (a : A) :
    reesMapOfEq I (algebraMap A B) J hJ (algebraMap A (reesAlgebra I) a) =
      algebraMap B (reesAlgebra J) (algebraMap A B a) := by
  apply Subtype.ext
  change Polynomial.map (algebraMap A B) (C a) = C (algebraMap A B a)
  rw [Polynomial.map_C]

/-- Coefficientwise extension of Rees algebras as an `A`-algebra map. -/
def reesMapOfEqAlg : reesAlgebra I →ₐ[A] reesAlgebra J where
  toRingHom := reesMapOfEq I (algebraMap A B) J hJ
  commutes' a := by
    change reesMapOfEq I (algebraMap A B) J hJ (algebraMap A (reesAlgebra I) a) = _
    rw [reesMapOfEq_algebraMap, IsScalarTower.algebraMap_apply A B (reesAlgebra J)]

@[simp]
theorem reesMapOfEqAlg_apply (x : reesAlgebra I) :
    reesMapOfEqAlg I J hJ x = reesMapOfEq I (algebraMap A B) J hJ x :=
  rfl

/-- The base-change comparison map of Rees algebras, as a `B`-algebra map. -/
def reesTensorMap : B ⊗[A] reesAlgebra I →ₐ[B] reesAlgebra J :=
  Algebra.TensorProduct.lift (Algebra.ofId B _) (reesMapOfEqAlg I J hJ) fun _ _ ↦ Commute.all _ _

@[simp]
theorem reesTensorMap_tmul (b : B) (x : reesAlgebra I) :
    reesTensorMap I J hJ (b ⊗ₜ[A] x) =
      algebraMap B (reesAlgebra J) b * reesMapOfEq I (algebraMap A B) J hJ x := by
  rw [reesTensorMap, Algebra.TensorProduct.lift_tmul]
  rfl

/-- The Rees algebras of equal ideals are equal. -/
def reesEquivOfEq : reesAlgebra (I.map (algebraMap A B)) ≃ₐ[B] reesAlgebra J :=
  Subalgebra.equivOfEq _ _ (by rw [hJ])

theorem reesTensorMap_eq :
    reesTensorMap I J hJ =
      (reesEquivOfEq I J hJ).toAlgHom.comp (reesTensorMap I (I.map (algebraMap A B)) rfl) := by
  refine Algebra.TensorProduct.ext' fun b x ↦ ?_
  change _ = reesEquivOfEq I J hJ (reesTensorMap I (I.map (algebraMap A B)) rfl (b ⊗ₜ[A] x))
  rw [reesTensorMap_tmul, reesTensorMap_tmul, map_mul, AlgEquiv.commutes]
  congr 1

theorem reesTensorMap_apply_eq (z : B ⊗[A] reesAlgebra I) :
    reesTensorMap I (I.map (algebraMap A B)) rfl z =
      ReesBlowup.reesBaseChangeMap (B := B) I
        (Algebra.TensorProduct.comm A B (reesAlgebra I) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    rw [reesTensorMap_tmul, Algebra.TensorProduct.comm_tmul, ReesBlowup.reesBaseChangeMap_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem reesTensorMap_apply_eq' (z : B ⊗[A] reesAlgebra I) :
    reesTensorMap I J hJ z = reesEquivOfEq I J hJ (ReesBlowup.reesBaseChangeMap (B := B) I
      (Algebra.TensorProduct.comm A B (reesAlgebra I) z)) := by
  rw [reesTensorMap_eq, ← reesTensorMap_apply_eq]
  rfl

theorem reesTensorMap_bijective [Module.Flat A B] : Function.Bijective (reesTensorMap I J hJ) := by
  have h : ⇑(reesTensorMap I J hJ) = ⇑(reesEquivOfEq I J hJ) ∘
      ⇑(ReesBlowup.reesBaseChangeMap (B := B) I) ∘
        ⇑(Algebra.TensorProduct.comm A B (reesAlgebra I)) :=
    funext (reesTensorMap_apply_eq' I J hJ)
  rw [h]
  have hb : Function.Bijective (ReesBlowup.reesBaseChangeMap (B := B) I) :=
    ⟨ReesBlowup.reesBaseChangeMap_injective I, ReesBlowup.reesBaseChangeMap_surjective I⟩
  exact (reesEquivOfEq I J hJ).bijective.comp
    (hb.comp (Algebra.TensorProduct.comm A B (reesAlgebra I)).bijective)

/-- Flat base change of the Rees algebra. -/
def reesTensorEquiv [Module.Flat A B] : B ⊗[A] reesAlgebra I ≃ₐ[B] reesAlgebra J :=
  AlgEquiv.ofBijective (reesTensorMap I J hJ) (reesTensorMap_bijective I J hJ)

theorem reesTensorEquiv_one_tmul [Module.Flat A B] (x : reesAlgebra I) :
    reesTensorEquiv I J hJ ((1 : B) ⊗ₜ[A] x) = reesMapOfEq I (algebraMap A B) J hJ x := by
  change reesTensorMap I J hJ ((1 : B) ⊗ₜ[A] x) = _
  rw [reesTensorMap_tmul, map_one, one_mul]

end Rees

section AssociatedGraded

variable {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A) (f : A →+* B) (J : Ideal B)
  (hJ : I.map f = J)

theorem reesMapOfEq_algebraMap' (a : A) :
    reesMapOfEq I f J hJ (algebraMap A (reesAlgebra I) a) = algebraMap B (reesAlgebra J) (f a) := by
  apply Subtype.ext
  change Polynomial.map f (C a) = C (f a)
  rw [Polynomial.map_C]

theorem map_le_comap_map_reesMapOfEq :
    Ideal.map (algebraMap A (reesAlgebra I)) I ≤
      (Ideal.map (algebraMap B (reesAlgebra J)) J).comap (reesMapOfEq I f J hJ) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Ideal.mem_comap, reesMapOfEq_algebraMap']
  exact Ideal.mem_map_of_mem _ (hJ ▸ Ideal.mem_map_of_mem f ha)

/-- The map of associated graded rings induced by a ring map carrying `I` onto `J`. -/
def grMapOfEq : associatedGradedRing A I →+* associatedGradedRing B J :=
  Ideal.quotientMap _ (reesMapOfEq I f J hJ) (map_le_comap_map_reesMapOfEq I f J hJ)

@[simp]
theorem grMapOfEq_mk (x : reesAlgebra I) :
    grMapOfEq I f J hJ (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (reesMapOfEq I f J hJ x) :=
  rfl

theorem grMapOfEq_congr {f' : A →+* B} (e : f = f') :
    grMapOfEq I f J hJ = grMapOfEq I f' J (e ▸ hJ) := by
  subst e
  rfl

theorem grMapOfEq_id (I : Ideal A) :
    grMapOfEq I (RingHom.id A) I (Ideal.map_id I) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  change Ideal.Quotient.mk _ (reesMapOfEq I (RingHom.id A) I (Ideal.map_id I) x) =
    Ideal.Quotient.mk _ x
  refine congrArg _ (Subtype.ext ?_)
  change (x : A[X]).map (RingHom.id A) = x
  rw [Polynomial.map_id]

theorem grMapOfEq_comp {C : Type u} [CommRing C] (g : B →+* C) (K : Ideal C)
    (hK : J.map g = K) :
    grMapOfEq I (g.comp f) K (by rw [← Ideal.map_map, hJ, hK]) =
      (grMapOfEq J g K hK).comp (grMapOfEq I f J hJ) := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  change Ideal.Quotient.mk _ (reesMapOfEq I (g.comp f) K _ x) =
    Ideal.Quotient.mk _ (reesMapOfEq J g K hK (reesMapOfEq I f J hJ x))
  refine congrArg _ (Subtype.ext ?_)
  change (x : A[X]).map (g.comp f) = ((x : A[X]).map f).map g
  rw [Polynomial.map_map]

theorem grMapOfEq_algebraMap (a : A) :
    grMapOfEq I f J hJ (algebraMap A (associatedGradedRing A I) a) =
      algebraMap B (associatedGradedRing B J) (f a) := by
  change grMapOfEq I f J hJ (Ideal.Quotient.mk _ (algebraMap A (reesAlgebra I) a)) =
    Ideal.Quotient.mk _ (algebraMap B (reesAlgebra J) (f a))
  rw [grMapOfEq_mk, reesMapOfEq_algebraMap']

end AssociatedGraded

section AssociatedGradedBaseChange

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] (I : Ideal A)
  (J : Ideal B) (hJ : I.map (algebraMap A B) = J)

/-- Flat base change of the associated graded ring. -/
def grTensorEquiv : B ⊗[A] associatedGradedRing A I ≃ₐ[B] associatedGradedRing B J :=
  (quotBaseChangeEquiv (reesTensorEquiv I J hJ) I).trans
    (Ideal.quotientEquivAlgOfEq B
      (show (I.map (algebraMap A B)).map (algebraMap B (reesAlgebra J)) =
        J.map (algebraMap B (reesAlgebra J)) by rw [hJ]))

theorem grTensorEquiv_one_tmul_mk (x : reesAlgebra I) :
    grTensorEquiv I J hJ ((1 : B) ⊗ₜ[A] Ideal.Quotient.mk _ x) =
      grMapOfEq I (algebraMap A B) J hJ (Ideal.Quotient.mk _ x) := by
  rw [grTensorEquiv, AlgEquiv.trans_apply, quotBaseChangeEquiv_one_tmul_mk,
    reesTensorEquiv_one_tmul, grMapOfEq_mk]
  rfl

theorem grTensorEquiv_one_tmul (z : associatedGradedRing A I) :
    grTensorEquiv I J hJ ((1 : B) ⊗ₜ[A] z) = grMapOfEq I (algebraMap A B) J hJ z := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact grTensorEquiv_one_tmul_mk I J hJ x

end AssociatedGradedBaseChange

end AffineNormalCone

/-! ### The global normal cone -/

namespace NormalCone

variable (X : Scheme.{u}) (I : X.IdealSheafData)

/-- The quasi-coherent algebra `gr_I(𝒪_X)` of a quasi-coherent ideal sheaf. -/
def algebraData : AlgebraData X where
  ring U := associatedGradedRing Γ(X, U.1) (I.ideal U)
  map {U V} h := grMapOfEq (I.ideal V) (res X h) (I.ideal U) (I.map_ideal h)
  map_id U := by
    rw [grMapOfEq_congr _ _ _ _ (res_refl X U)]
    exact grMapOfEq_id _
  map_comp {U V W} hUV hVW := by
    rw [grMapOfEq_congr _ _ _ _ (res_comp X hUV hVW)]
    exact grMapOfEq_comp (I.ideal W) (res X hVW) (I.ideal V) (I.map_ideal hVW) (res X hUV)
      (I.ideal U) (I.map_ideal hUV)
  isPushout {U V} h := by
    let _ := (res X h).toAlgebra
    have : Module.Flat Γ(X, V.1) Γ(X, U.1) := res_flat X h
    exact isPushout_of_algEquiv _ (grTensorEquiv (I.ideal V) (I.ideal U) (I.map_ideal h))
      (grTensorEquiv_one_tmul (I.ideal V) (I.ideal U) (I.map_ideal h))

/-- The normal cone `C_{Z/X}` of the closed subscheme `Z = V(I)`, as a scheme over `X`. -/
abbrev normalCone : Scheme.{u} := relativeSpec X (algebraData X I)

/-- The structure morphism `C_{Z/X} → X`. -/
def toBase : normalCone X I ⟶ X := RelativeSpec.toBase X (algebraData X I)

instance toBase_isAffineHom : IsAffineHom (toBase X I) :=
  RelativeSpec.toBase_isAffineHom X (algebraData X I)

/-- The affine normal cone of an affine open embeds into the normal cone. -/
def affineι (U : X.affineOpens) : AffineNormalCone.scheme Γ(X, U.1) (I.ideal U) ⟶ normalCone X I :=
  RelativeSpec.affineι X (algebraData X I) U

instance affineι_isOpenImmersion (U : X.affineOpens) : IsOpenImmersion (affineι X I U) :=
  RelativeSpec.affineι_isOpenImmersion X (algebraData X I) U

/-- Over every affine open, the normal cone is the affine normal cone `Spec gr_I`. -/
theorem isPullback_affine (U : X.affineOpens) :
    IsPullback (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, U.1) (associatedGradedRing Γ(X, U.1) (I.ideal U)))) ≫
        (isAffineOpen X U).isoSpec.inv) (affineι X I U) U.1.ι (toBase X I) :=
  RelativeSpec.isPullback_affine X (algebraData X I) U

/-- The affine normal cones cover the normal cone. -/
theorem iSup_opensRange_affineι : ⨆ U : X.affineOpens, (affineι X I U).opensRange = ⊤ :=
  RelativeSpec.iSup_opensRange_affineι X (algebraData X I)

end NormalCone

/-! ### Symmetric algebras of ideals and their flat base change -/

namespace AffineNormalCone

section SymCongr

variable {R : Type u} [CommRing R] {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- The isomorphism of symmetric algebras induced by a linear isomorphism. -/
def symCongr (e : M ≃ₗ[R] N) : SymmetricAlgebra R M ≃ₐ[R] SymmetricAlgebra R N :=
  AlgEquiv.ofAlgHom (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp e.toLinearMap))
    (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R M).comp e.symm.toLinearMap))
    (SymmetricAlgebra.algHom_ext (LinearMap.ext fun n ↦ by simp))
    (SymmetricAlgebra.algHom_ext (LinearMap.ext fun m ↦ by simp))

@[simp]
theorem symCongr_ι (e : M ≃ₗ[R] N) (m : M) :
    symCongr e (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R N (e m) :=
  SymmetricAlgebra.lift_ι_apply _ _

end SymCongr

section SymIdeal

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A) (J : Ideal B)
  (hJ : I.map (algebraMap A B) = J)

/-- The `A`-linear map `I → J` induced by `A → B`. -/
def idealMapLinear : I →ₗ[A] J where
  toFun x := ⟨algebraMap A B x, hJ ▸ Ideal.mem_map_of_mem (algebraMap A B) x.2⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' a x := Subtype.ext (by simp [Algebra.smul_def])

@[simp]
theorem idealMapLinear_coe (x : I) : (idealMapLinear I J hJ x : B) = algebraMap A B x :=
  rfl

/-- The map of symmetric algebras induced by `A → B`, as an `A`-algebra map. -/
def symMapOfEqAlg : SymmetricAlgebra A I →ₐ[A] SymmetricAlgebra B J :=
  SymmetricAlgebra.lift (((SymmetricAlgebra.ι B J).restrictScalars A).comp (idealMapLinear I J hJ))

@[simp]
theorem symMapOfEqAlg_ι (x : I) :
    symMapOfEqAlg I J hJ (SymmetricAlgebra.ι A I x) =
      SymmetricAlgebra.ι B J (idealMapLinear I J hJ x) := by
  rw [symMapOfEqAlg, SymmetricAlgebra.lift_ι_apply]
  rfl

/-- The `B`-linear map `B ⊗ I → B`. -/
def idealTensorMap : B ⊗[A] I →ₗ[B] B :=
  (Algebra.TensorProduct.rid A B B).toLinearMap.comp (I.subtype.baseChange B)

@[simp]
theorem idealTensorMap_tmul (b : B) (x : I) :
    idealTensorMap I (b ⊗ₜ[A] x) = b * algebraMap A B x := by
  rw [idealTensorMap, LinearMap.comp_apply, LinearMap.baseChange_tmul, AlgEquiv.toLinearMap_apply,
    Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_comm]
  rfl

include hJ in
theorem range_idealTensorMap : LinearMap.range (idealTensorMap I) = J := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b x =>
      rw [idealTensorMap_tmul]
      exact J.mul_mem_left b (hJ ▸ Ideal.mem_map_of_mem (algebraMap A B) x.2)
    | add x y hx hy => rw [map_add]; exact J.add_mem hx hy
  · rw [← hJ, Ideal.map, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨(1 : B) ⊗ₜ[A] ⟨x, hx⟩, by rw [idealTensorMap_tmul, one_mul]⟩

variable [Module.Flat A B]

theorem idealTensorMap_injective : Function.Injective (idealTensorMap (B := B) I) := by
  rw [idealTensorMap, LinearMap.coe_comp]
  refine (Algebra.TensorProduct.rid A B B).injective.comp ?_
  rw [LinearMap.baseChange_eq_ltensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective

/-- Flat base change of an ideal: `B ⊗ I ≅ IB`. -/
def idealTensorEquiv : B ⊗[A] I ≃ₗ[B] J :=
  (LinearEquiv.ofInjective _ (idealTensorMap_injective (B := B) I)).trans
    (LinearEquiv.ofEq _ _ (range_idealTensorMap I J hJ))

theorem idealTensorEquiv_one_tmul (x : I) :
    idealTensorEquiv I J hJ ((1 : B) ⊗ₜ[A] x) = idealMapLinear I J hJ x := by
  apply Subtype.ext
  change idealTensorMap I ((1 : B) ⊗ₜ[A] x) = algebraMap A B x
  rw [idealTensorMap_tmul, one_mul]

/-- Flat base change of the symmetric algebra of an ideal. -/
def symTensorEquiv : B ⊗[A] SymmetricAlgebra A I ≃ₐ[B] SymmetricAlgebra B J :=
  (GradedCone.baseChangeEquiv A I B).symm.trans (symCongr (idealTensorEquiv I J hJ))

theorem symTensorEquiv_one_tmul (s : SymmetricAlgebra A I) :
    symTensorEquiv I J hJ ((1 : B) ⊗ₜ[A] s) = symMapOfEqAlg I J hJ s := by
  have key : ((symTensorEquiv I J hJ).toAlgHom.restrictScalars A).comp
      Algebra.TensorProduct.includeRight = symMapOfEqAlg I J hJ := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x ↦ ?_)
    change symTensorEquiv I J hJ ((1 : B) ⊗ₜ[A] SymmetricAlgebra.ι A I x) =
      symMapOfEqAlg I J hJ (SymmetricAlgebra.ι A I x)
    rw [symMapOfEqAlg_ι, symTensorEquiv, AlgEquiv.trans_apply, ← idealTensorEquiv_one_tmul,
      ← symCongr_ι]
    congr 1
    rw [AlgEquiv.symm_apply_eq]
    change _ = GradedCone.baseChangeForward A I B (SymmetricAlgebra.ι B (B ⊗[A] I) _)
    rw [GradedCone.baseChangeForward, SymmetricAlgebra.lift_ι_apply, LinearMap.baseChange_tmul]
  exact AlgHom.congr_fun key s

end SymIdeal

section NormalSheafRing

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- The coordinate ring `Sym_A(I) ⊗_A A/I = Sym_A(I)/I·Sym_A(I)` of the normal sheaf, presented
as a quotient of the symmetric algebra of the ideal itself. -/
abbrev normalSheafRing : Type u :=
  SymmetricAlgebra A I ⧸ Ideal.map (algebraMap A (SymmetricAlgebra A I)) I

end NormalSheafRing

section SymMapOfEq

variable {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A) (f : A →+* B) (J : Ideal B)
  (hJ : I.map f = J)

/-- The map of symmetric algebras induced by a ring map carrying `I` onto `J`. -/
def symMapOfEq : SymmetricAlgebra A I →+* SymmetricAlgebra B J :=
  letI := f.toAlgebra
  (symMapOfEqAlg I J hJ).toRingHom

theorem symMapOfEq_ι (x : I) :
    symMapOfEq I f J hJ (SymmetricAlgebra.ι A I x) =
      SymmetricAlgebra.ι B J ⟨f x, hJ ▸ Ideal.mem_map_of_mem f x.2⟩ := by
  let _ := f.toAlgebra
  exact symMapOfEqAlg_ι I J hJ x

theorem symMapOfEq_algebraMap (a : A) :
    symMapOfEq I f J hJ (algebraMap A (SymmetricAlgebra A I) a) =
      algebraMap B (SymmetricAlgebra B J) (f a) := by
  let _ := f.toAlgebra
  change symMapOfEqAlg I J hJ (algebraMap A (SymmetricAlgebra A I) a) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A B (SymmetricAlgebra B J)]
  rfl

theorem symMapOfEq_congr {f' : A →+* B} (e : f = f') :
    symMapOfEq I f J hJ = symMapOfEq I f' J (e ▸ hJ) := by
  subst e
  rfl

theorem symMapOfEq_id (I : Ideal A) :
    symMapOfEq I (RingHom.id A) I (Ideal.map_id I) = RingHom.id _ := by
  refine RingHom.ext fun s ↦ ?_
  induction s using SymmetricAlgebra.induction with
  | algebraMap a => rw [symMapOfEq_algebraMap]; rfl
  | ι x => rw [symMapOfEq_ι]; rfl
  | mul a b ha hb => rw [map_mul, ha, hb, map_mul]
  | add a b ha hb => rw [map_add, ha, hb, map_add]

theorem symMapOfEq_comp {C : Type u} [CommRing C] (g : B →+* C) (K : Ideal C)
    (hK : J.map g = K) :
    symMapOfEq I (g.comp f) K (by rw [← Ideal.map_map, hJ, hK]) =
      (symMapOfEq J g K hK).comp (symMapOfEq I f J hJ) := by
  refine RingHom.ext fun s ↦ ?_
  induction s using SymmetricAlgebra.induction with
  | algebraMap a =>
    change _ = symMapOfEq J g K hK (symMapOfEq I f J hJ (algebraMap A (SymmetricAlgebra A I) a))
    rw [symMapOfEq_algebraMap, symMapOfEq_algebraMap, symMapOfEq_algebraMap]
    rfl
  | ι x =>
    change _ = symMapOfEq J g K hK (symMapOfEq I f J hJ (SymmetricAlgebra.ι A I x))
    rw [symMapOfEq_ι, symMapOfEq_ι, symMapOfEq_ι]
    rfl
  | mul a b ha hb => rw [map_mul, ha, hb, map_mul]
  | add a b ha hb => rw [map_add, ha, hb, map_add]

theorem symMapOfEq_map_le :
    Ideal.map (algebraMap A (SymmetricAlgebra A I)) I ≤
      (Ideal.map (algebraMap B (SymmetricAlgebra B J)) J).comap (symMapOfEq I f J hJ) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Ideal.mem_comap, symMapOfEq_algebraMap]
  exact Ideal.mem_map_of_mem _ (hJ ▸ Ideal.mem_map_of_mem f ha)

/-- The map of normal-sheaf coordinate rings induced by a ring map carrying `I` onto `J`. -/
def nsMapOfEq : normalSheafRing A I →+* normalSheafRing B J :=
  Ideal.quotientMap _ (symMapOfEq I f J hJ) (symMapOfEq_map_le I f J hJ)

@[simp]
theorem nsMapOfEq_mk (s : SymmetricAlgebra A I) :
    nsMapOfEq I f J hJ (Ideal.Quotient.mk _ s) = Ideal.Quotient.mk _ (symMapOfEq I f J hJ s) :=
  rfl

theorem nsMapOfEq_congr {f' : A →+* B} (e : f = f') :
    nsMapOfEq I f J hJ = nsMapOfEq I f' J (e ▸ hJ) := by
  subst e
  rfl

theorem nsMapOfEq_id (I : Ideal A) :
    nsMapOfEq I (RingHom.id A) I (Ideal.map_id I) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  refine RingHom.ext fun s ↦ ?_
  change Ideal.Quotient.mk _ (symMapOfEq I (RingHom.id A) I (Ideal.map_id I) s) =
    Ideal.Quotient.mk _ s
  rw [symMapOfEq_id]
  rfl

theorem nsMapOfEq_comp {C : Type u} [CommRing C] (g : B →+* C) (K : Ideal C)
    (hK : J.map g = K) :
    nsMapOfEq I (g.comp f) K (by rw [← Ideal.map_map, hJ, hK]) =
      (nsMapOfEq J g K hK).comp (nsMapOfEq I f J hJ) := by
  apply Ideal.Quotient.ringHom_ext
  refine RingHom.ext fun s ↦ ?_
  change Ideal.Quotient.mk _ (symMapOfEq I (g.comp f) K _ s) =
    Ideal.Quotient.mk _ (symMapOfEq J g K hK (symMapOfEq I f J hJ s))
  rw [symMapOfEq_comp I f J hJ g K hK]
  rfl

theorem nsMapOfEq_algebraMap (a : A) :
    nsMapOfEq I f J hJ (algebraMap A (normalSheafRing A I) a) =
      algebraMap B (normalSheafRing B J) (f a) := by
  change nsMapOfEq I f J hJ (Ideal.Quotient.mk _ (algebraMap A (SymmetricAlgebra A I) a)) =
    Ideal.Quotient.mk _ (algebraMap B (SymmetricAlgebra B J) (f a))
  rw [nsMapOfEq_mk, symMapOfEq_algebraMap]

end SymMapOfEq

section NormalSheafBaseChange

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A) (J : Ideal B)
  (hJ : I.map (algebraMap A B) = J)

theorem symMapOfEq_eq_symMapOfEqAlg (s : SymmetricAlgebra A I) :
    symMapOfEq I (algebraMap A B) J hJ s = symMapOfEqAlg I J hJ s := by
  induction s using SymmetricAlgebra.induction with
  | algebraMap a =>
    rw [symMapOfEq_algebraMap, AlgHom.commutes,
      IsScalarTower.algebraMap_apply A B (SymmetricAlgebra B J)]
  | ι x => rw [symMapOfEq_ι, symMapOfEqAlg_ι]; rfl
  | mul a b ha hb => rw [map_mul, ha, hb, map_mul]
  | add a b ha hb => rw [map_add, ha, hb, map_add]

variable [Module.Flat A B]

/-- Flat base change of the normal-sheaf coordinate ring. -/
def nsTensorEquiv : B ⊗[A] normalSheafRing A I ≃ₐ[B] normalSheafRing B J :=
  (quotBaseChangeEquiv (symTensorEquiv I J hJ) I).trans
    (Ideal.quotientEquivAlgOfEq B
      (show (I.map (algebraMap A B)).map (algebraMap B (SymmetricAlgebra B J)) =
        J.map (algebraMap B (SymmetricAlgebra B J)) by rw [hJ]))

theorem nsTensorEquiv_one_tmul (z : normalSheafRing A I) :
    nsTensorEquiv I J hJ ((1 : B) ⊗ₜ[A] z) = nsMapOfEq I (algebraMap A B) J hJ z := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [nsTensorEquiv, AlgEquiv.trans_apply, quotBaseChangeEquiv_one_tmul_mk,
    symTensorEquiv_one_tmul, nsMapOfEq_mk, symMapOfEq_eq_symMapOfEqAlg]
  rfl

end NormalSheafBaseChange

/-! ### The surjection `Sym(I/I²) → gr_I` -/

section SymToRees

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- The surjection `Sym_A(I) → Rees_I(A)` sending `x ∈ I` to `x t`. -/
def symToRees : SymmetricAlgebra A I →ₐ[A] reesAlgebra I :=
  SymmetricAlgebra.lift (degreeOneRees A I)

@[simp]
theorem symToRees_ι (x : I) : symToRees A I (SymmetricAlgebra.ι A I x) = degreeOneRees A I x :=
  SymmetricAlgebra.lift_ι_apply _ _

theorem coe_degreeOneRees (x : I) : (degreeOneRees A I x : A[X]) = monomial 1 (x : A) :=
  rfl

/-- The Rees algebra is generated in degree one, so `Sym_A(I) → Rees_I(A)` is surjective. -/
theorem symToRees_surjective : Function.Surjective (symToRees A I) := by
  intro p
  have hp : (p : A[X]) ∈ Algebra.adjoin A
      (Submodule.map (monomial 1 : A →ₗ[A] A[X]) I : Set A[X]) := by
    rw [adjoin_monomial_eq_reesAlgebra]
    exact p.2
  have hle : Algebra.adjoin A (Submodule.map (monomial 1 : A →ₗ[A] A[X]) I : Set A[X]) ≤
      (symToRees A I).range.map (reesAlgebra I).val := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨symToRees A I (SymmetricAlgebra.ι A I ⟨x, hx⟩), ⟨_, rfl⟩, by
      rw [symToRees_ι]
      rfl⟩
  obtain ⟨q, ⟨s, rfl⟩, hq⟩ := hle hp
  exact ⟨s, Subtype.ext hq⟩

theorem symToRees_map_le :
    Ideal.map (algebraMap A (SymmetricAlgebra A I)) I ≤
      (Ideal.map (algebraMap A (reesAlgebra I)) I).comap (symToRees A I) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
  exact Ideal.mem_map_of_mem _ ha

/-- The surjection `Sym_{A/I}(I/I²) → gr_I(A)`, the affine closed immersion of the normal cone
into the normal sheaf. -/
def nsToGr : normalSheafRing A I →ₐ[A] associatedGradedRing A I :=
  Ideal.quotientMapₐ _ (symToRees A I) (symToRees_map_le A I)

@[simp]
theorem nsToGr_mk (s : SymmetricAlgebra A I) :
    nsToGr A I (Ideal.Quotient.mk _ s) = Ideal.Quotient.mk _ (symToRees A I s) :=
  rfl

theorem nsToGr_surjective : Function.Surjective (nsToGr A I) := by
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨s, rfl⟩ := symToRees_surjective A I y
  exact ⟨Ideal.Quotient.mk _ s, rfl⟩

end SymToRees

section SymToReesNaturality

variable {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A) (f : A →+* B) (J : Ideal B)
  (hJ : I.map f = J)

theorem reesMapOfEq_degreeOneRees (x : I) :
    reesMapOfEq I f J hJ (degreeOneRees A I x) =
      degreeOneRees B J ⟨f x, hJ ▸ Ideal.mem_map_of_mem f x.2⟩ := by
  apply Subtype.ext
  change (monomial 1 (x : A)).map f = monomial 1 (f x)
  rw [Polynomial.map_monomial]

/-- The surjections `Sym(I/I²) → gr_I` are compatible with the maps induced by ring maps. -/
theorem nsToGr_naturality :
    (nsToGr B J).toRingHom.comp (nsMapOfEq I f J hJ) =
      (grMapOfEq I f J hJ).comp (nsToGr A I).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  refine RingHom.ext fun s ↦ ?_
  change Ideal.Quotient.mk _ (symToRees B J (symMapOfEq I f J hJ s)) =
    Ideal.Quotient.mk _ (reesMapOfEq I f J hJ (symToRees A I s))
  congr 1
  induction s using SymmetricAlgebra.induction with
  | algebraMap a =>
    rw [symMapOfEq_algebraMap, AlgHom.commutes, AlgHom.commutes, reesMapOfEq_algebraMap']
  | ι x => rw [symMapOfEq_ι, symToRees_ι, symToRees_ι, reesMapOfEq_degreeOneRees]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

end SymToReesNaturality

/-! ### Comparison with `Sym_{A/I}(I/I²)` -/

section NormalSheafRingEquiv

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- `(A/I) ⊗_A I ≅ I/I²`. -/
def quotTensorIdealEquiv : (A ⧸ I) ⊗[A] I ≃ₗ[A ⧸ I] I.Cotangent :=
  LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    ((TensorProduct.quotTensorEquivQuotSMul I I).trans (LinearEquiv.refl A I.Cotangent))

theorem quotTensorIdealEquiv_one_tmul (x : I) :
    quotTensorIdealEquiv A I ((1 : A ⧸ I) ⊗ₜ[A] x) = I.toCotangent x := by
  change TensorProduct.quotTensorEquivQuotSMul I I ((1 : A ⧸ I) ⊗ₜ[A] x) = _
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
  rfl

/-- The quotient presentation `Sym_A(I)/I·Sym_A(I)` of the normal-sheaf coordinate ring agrees
with the presentation `Sym_{A/I}(I/I²)` of `Cones/Affine.lean`. -/
def normalSheafRingEquiv : normalSheafRing A I ≃ₐ[A ⧸ I] normalSheafCoordinateRing A I :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (SymmetricAlgebra A I) I).trans
    ((GradedCone.baseChangeEquiv A I (A ⧸ I)).symm.trans (symCongr (quotTensorIdealEquiv A I)))

theorem normalSheafRingEquiv_mk_ι (x : I) :
    normalSheafRingEquiv A I (Ideal.Quotient.mk _ (SymmetricAlgebra.ι A I x)) =
      SymmetricAlgebra.ι (A ⧸ I) I.Cotangent (I.toCotangent x) := by
  rw [normalSheafRingEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk, ← quotTensorIdealEquiv_one_tmul,
    ← symCongr_ι]
  congr 1
  rw [AlgEquiv.symm_apply_eq]
  change _ = GradedCone.baseChangeForward A I (A ⧸ I) (SymmetricAlgebra.ι _ _ _)
  rw [GradedCone.baseChangeForward, SymmetricAlgebra.lift_ι_apply, LinearMap.baseChange_tmul]

/-- Through this identification, the surjection `nsToGr` is the coordinate map of the affine
closed immersion `coneToNormalSheaf` of `Cones/Affine.lean`. -/
theorem normalSheafCoordinateMap_comp_equiv :
    (normalSheafCoordinateMap A I).comp (normalSheafRingEquiv A I).toRingEquiv.toRingHom =
      (nsToGr A I).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  refine RingHom.ext fun s ↦ ?_
  change normalSheafCoordinateMap A I (normalSheafRingEquiv A I (Ideal.Quotient.mk _ s)) =
    nsToGr A I (Ideal.Quotient.mk _ s)
  induction s using SymmetricAlgebra.induction with
  | algebraMap a =>
    change normalSheafCoordinateMap A I (normalSheafRingEquiv A I
      (algebraMap (A ⧸ I) (normalSheafRing A I) (Ideal.Quotient.mk I a))) = _
    rw [AlgEquiv.commutes, normalSheafCoordinateMap_base, nsToGr_mk, AlgHom.commutes]
    rfl
  | ι x =>
    rw [normalSheafRingEquiv_mk_ι, normalSheafCoordinateMap_ι,
      conormalToAssociatedGraded_toCotangent, nsToGr_mk, symToRees_ι]
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The affine closed immersion `Spec gr_I → Spec Sym(I/I²)` used in the global gluing is the
affine `coneToNormalSheaf` of `Cones/Affine.lean`, up to the identification of coordinate
rings. -/
theorem coneToNormalSheaf_comp_specMap_equiv :
    coneToNormalSheaf A I ≫
        Spec.map (CommRingCat.ofHom (normalSheafRingEquiv A I).toRingEquiv.toRingHom) =
      Spec.map (CommRingCat.ofHom (nsToGr A I).toRingHom) := by
  rw [← normalSheafCoordinateMap_comp_equiv, CommRingCat.ofHom_comp, Spec.map_comp]
  rfl

end NormalSheafRingEquiv

end AffineNormalCone

/-! ### The global normal sheaf and the closed immersion of the normal cone -/

namespace NormalSheaf

variable (X : Scheme.{u}) (I : X.IdealSheafData)

/-- The quasi-coherent algebra `Sym(I/I²)` of a quasi-coherent ideal sheaf. -/
def algebraData : AlgebraData X where
  ring U := normalSheafRing Γ(X, U.1) (I.ideal U)
  map {U V} h := nsMapOfEq (I.ideal V) (res X h) (I.ideal U) (I.map_ideal h)
  map_id U := by
    rw [nsMapOfEq_congr _ _ _ _ (res_refl X U)]
    exact nsMapOfEq_id _
  map_comp {U V W} hUV hVW := by
    rw [nsMapOfEq_congr _ _ _ _ (res_comp X hUV hVW)]
    exact nsMapOfEq_comp (I.ideal W) (res X hVW) (I.ideal V) (I.map_ideal hVW) (res X hUV)
      (I.ideal U) (I.map_ideal hUV)
  isPushout {U V} h := by
    let _ := (res X h).toAlgebra
    have : Module.Flat Γ(X, V.1) Γ(X, U.1) := res_flat X h
    exact isPushout_of_algEquiv _ (nsTensorEquiv (I.ideal V) (I.ideal U) (I.map_ideal h))
      (nsTensorEquiv_one_tmul (I.ideal V) (I.ideal U) (I.map_ideal h))

/-- The normal sheaf `N_{Z/X} = Spec Sym(I/I²)` of the closed subscheme `Z = V(I)`, as a scheme
over `X`. -/
abbrev normalSheaf : Scheme.{u} := relativeSpec X (algebraData X I)

/-- The structure morphism `N_{Z/X} → X`. -/
def toBase : normalSheaf X I ⟶ X := RelativeSpec.toBase X (algebraData X I)

instance toBase_isAffineHom : IsAffineHom (toBase X I) :=
  RelativeSpec.toBase_isAffineHom X (algebraData X I)

/-- The affine normal sheaf of an affine open embeds into the normal sheaf. -/
def affineι (U : X.affineOpens) :
    Spec (.of (normalSheafRing Γ(X, U.1) (I.ideal U))) ⟶ normalSheaf X I :=
  RelativeSpec.affineι X (algebraData X I) U

instance affineι_isOpenImmersion (U : X.affineOpens) : IsOpenImmersion (affineι X I U) :=
  RelativeSpec.affineι_isOpenImmersion X (algebraData X I) U

/-- Over every affine open, the normal sheaf is the affine normal sheaf. -/
theorem isPullback_affine (U : X.affineOpens) :
    IsPullback (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, U.1) (normalSheafRing Γ(X, U.1) (I.ideal U)))) ≫
        (isAffineOpen X U).isoSpec.inv) (affineι X I U) U.1.ι (toBase X I) :=
  RelativeSpec.isPullback_affine X (algebraData X I) U

end NormalSheaf

namespace NormalCone

variable (X : Scheme.{u}) (I : X.IdealSheafData)

/-- The morphism of quasi-coherent algebras `Sym(I/I²) → gr_I`. -/
def toNormalSheafHom : RelativeSpec.Hom X (algebraData X I) (NormalSheaf.algebraData X I) where
  app U := nsToGr Γ(X, U.1) (I.ideal U)
  naturality {U V} h := nsToGr_naturality (I.ideal V) (res X h) (I.ideal U) (I.map_ideal h)

/-- The closed immersion `C_{Z/X} → N_{Z/X}` of the normal cone into the normal sheaf. -/
def toNormalSheaf : normalCone X I ⟶ NormalSheaf.normalSheaf X I := (toNormalSheafHom X I).map

instance toNormalSheaf_isClosedImmersion : IsClosedImmersion (toNormalSheaf X I) :=
  (toNormalSheafHom X I).map_isClosedImmersion fun U ↦ nsToGr_surjective Γ(X, U.1) (I.ideal U)

/-- The closed immersion lies over `X`. -/
theorem toNormalSheaf_toBase : toNormalSheaf X I ≫ NormalSheaf.toBase X I = toBase X I :=
  (toNormalSheafHom X I).map_toBase

/-- Over every affine open, the closed immersion is the affine `Spec` of the surjection
`Sym(I/I²) → gr_I`. -/
theorem isPullback_toNormalSheaf (U : X.affineOpens) :
    IsPullback (Spec.map (CommRingCat.ofHom (nsToGr Γ(X, U.1) (I.ideal U)).toRingHom))
      (affineι X I U) (NormalSheaf.affineι X I U) (toNormalSheaf X I) :=
  (toNormalSheafHom X I).isPullback_map U

/-- Over every affine open, the closed immersion of the normal cone into the normal sheaf is the
affine closed immersion `coneToNormalSheaf` of `Cones/Affine.lean`, composed with the
identification of the two presentations of the normal-sheaf coordinate ring. -/
theorem isPullback_coneToNormalSheaf (U : X.affineOpens) :
    IsPullback (coneToNormalSheaf Γ(X, U.1) (I.ideal U) ≫ Spec.map (CommRingCat.ofHom
        (normalSheafRingEquiv Γ(X, U.1) (I.ideal U)).toRingEquiv.toRingHom))
      (affineι X I U) (NormalSheaf.affineι X I U) (toNormalSheaf X I) := by
  rw [coneToNormalSheaf_comp_specMap_equiv]
  exact isPullback_toNormalSheaf X I U

end NormalCone

end

end GromovWitten.AlgebraicGeometry
