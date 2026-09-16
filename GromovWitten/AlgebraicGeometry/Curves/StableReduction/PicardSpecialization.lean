/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.Contraction
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Geometric Picard and Jacobian specialization

This file connects line bundles on an arithmetic surface to the weighted numerical Picard group
of its actual special fibre.  A relative Picard class is represented by a genuine line bundle on
the total scheme together with its component degrees on every geometric fibre.  Its specialization
is the divisor of degrees on the genuine irreducible components of the scheme-theoretic special
fibre, modulo the weighted intersection relations.

Tensor product and genuine dual line bundles give both absolute and degree-decorated relative
Picard classes their additive commutative group laws.  Specialization and generic-fibre
restriction are constructed additive homomorphisms for those canonical laws.
`JacobianSpecializationData` records only the still-missing geometric propositions that generic
line-bundle classes extend and that numerical specialization vanishes on the kernel of generic
restriction.  A choice of extensions is then made internally and proved to induce a well-defined
additive specialization.  Consequently the prime-to-special-characteristic torsion map below has
concrete geometric source and the numerical Picard group of `SpecialFiberIntersectionData` as its
concrete target.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

universe u

noncomputable section

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}
variable {M : Model R K C toK}

/-- Isomorphism classes of genuine relative line bundles with component-degree data. -/
abbrev RelativePicardClass {X S : Scheme.{u}} (f : X ⟶ S) :=
  Quotient (RelativeLineBundle.isomorphicSetoid f)

namespace RelativePicardClass

/-- Tensor product on isomorphism classes of relative line bundles. -/
def tensor {f : X ⟶ S} :
    RelativePicardClass f → RelativePicardClass f → RelativePicardClass f :=
  Quotient.map₂ RelativeLineBundle.tensor (by
    intro L L' hL N N' hN
    rcases hL with ⟨⟨eL⟩, hdL⟩
    rcases hN with ⟨⟨eN⟩, hdN⟩
    refine ⟨⟨LineBundle.tensorMapIso eL eN⟩, ?_⟩
    funext K hK y C
    change L.componentDegree K y C + N.componentDegree K y C =
      L'.componentDegree K y C + N'.componentDegree K y C
    rw [hdL, hdN])

/-- The trivial relative Picard class has the trivial line bundle and zero component degree. -/
def trivial (f : X ⟶ S) : RelativePicardClass f :=
  ⟦RelativeLineBundle.trivial f⟧

@[simp]
theorem tensor_mk {f : X ⟶ S} (L N : RelativeLineBundle f) :
    tensor (⟦L⟧ : RelativePicardClass f) ⟦N⟧ = ⟦L.tensor N⟧ := rfl

theorem tensor_assoc {f : X ⟶ S} (a b c : RelativePicardClass f) :
    tensor (tensor a b) c = tensor a (tensor b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro L N P
  apply Quotient.sound
  refine ⟨⟨LineBundle.tensorAssocIso L.line N.line P.line⟩, ?_⟩
  funext K hK y C
  exact add_assoc _ _ _

@[simp]
theorem trivial_tensor {f : X ⟶ S} (a : RelativePicardClass f) :
    tensor (trivial f) a = a := by
  refine Quotient.inductionOn a ?_
  intro L
  apply Quotient.sound
  refine ⟨⟨LineBundle.trivialTensorIso L.line⟩, ?_⟩
  funext K hK y C
  exact zero_add _

@[simp]
theorem tensor_trivial {f : X ⟶ S} (a : RelativePicardClass f) :
    tensor a (trivial f) = a := by
  refine Quotient.inductionOn a ?_
  intro L
  apply Quotient.sound
  refine ⟨⟨LineBundle.tensorTrivialIso L.line⟩, ?_⟩
  funext K hK y C
  exact add_zero _

theorem tensor_comm {f : X ⟶ S} (a b : RelativePicardClass f) :
    tensor a b = tensor b a := by
  refine Quotient.inductionOn₂ a b ?_
  intro L N
  apply Quotient.sound
  refine ⟨⟨LineBundle.tensorCommIso L.line N.line⟩, ?_⟩
  funext K hK y C
  exact add_comm _ _

instance addCommMonoid {f : X ⟶ S} : AddCommMonoid (RelativePicardClass f) := by
  letI : Add (RelativePicardClass f) := ⟨tensor⟩
  letI : Zero (RelativePicardClass f) := ⟨trivial f⟩
  exact
    { add := tensor
      add_assoc := tensor_assoc
      zero := trivial f
      zero_add := trivial_tensor
      add_zero := tensor_trivial
      add_comm := tensor_comm
      nsmul := nsmulRec }

/-- A relative line bundle plus its genuine dual is the trivial relative Picard class. -/
@[simp]
theorem add_dual_mk {f : X ⟶ S} (L : RelativeLineBundle f) :
    (⟦L⟧ : RelativePicardClass f) + ⟦L.dual⟧ = 0 := by
  apply Quotient.sound
  refine ⟨⟨LineBundle.tensorDualIso L.line⟩, ?_⟩
  funext K hK y C
  exact add_neg_cancel _

/-- Two additive right inverses in the commutative relative Picard monoid coincide. -/
theorem inverse_unique {f : X ⟶ S} (a b c : RelativePicardClass f)
    (hb : a + b = 0) (hc : a + c = 0) : b = c := by
  calc
    b = b + 0 := (add_zero b).symm
    _ = b + (a + c) := by rw [hc]
    _ = (b + a) + c := (add_assoc b a c).symm
    _ = (a + b) + c := by rw [add_comm b a]
    _ = 0 + c := by rw [hb]
    _ = c := zero_add c

/-- Dual relative line bundles descend to isomorphism classes. -/
def dual {f : X ⟶ S} : RelativePicardClass f → RelativePicardClass f :=
  Quotient.map RelativeLineBundle.dual (by
    intro L N hLN
    have hclass : (⟦L⟧ : RelativePicardClass f) = ⟦N⟧ := Quotient.sound hLN
    apply Quotient.exact
    apply inverse_unique (⟦L⟧ : RelativePicardClass f)
    · exact add_dual_mk L
    · rw [hclass]
      exact add_dual_mk N)

@[simp]
theorem dual_mk {f : X ⟶ S} (L : RelativeLineBundle f) :
    dual (⟦L⟧ : RelativePicardClass f) = ⟦L.dual⟧ := rfl

@[simp]
theorem add_dual {f : X ⟶ S} (a : RelativePicardClass f) : a + dual a = 0 := by
  refine Quotient.inductionOn a ?_
  exact add_dual_mk

instance addCommGroup {f : X ⟶ S} : AddCommGroup (RelativePicardClass f) := by
  letI : Neg (RelativePicardClass f) := ⟨dual⟩
  exact
    { __ := RelativePicardClass.addCommMonoid
      neg := dual
      zsmul := zsmulRec
      neg_add_cancel := fun a ↦ by
        rw [add_comm]
        exact add_dual a }

/-- Natural scalar multiplication of a represented relative Picard class is its bundled tensor
power. -/
@[simp]
theorem nsmul_mk {f : X ⟶ S} (L : RelativeLineBundle f) (n : ℕ) :
    n • (⟦L⟧ : RelativePicardClass f) = ⟦L.tensorPow n⟧ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [succ_nsmul, ih]
      rfl

/-- Integer scalar multiplication of a represented relative Picard class is its bundled integer
tensor power. -/
@[simp]
theorem zsmul_mk {f : X ⟶ S} (L : RelativeLineBundle f) (n : ℤ) :
    n • (⟦L⟧ : RelativePicardClass f) = ⟦L.tensorIntPow n⟧ := by
  cases n with
  | ofNat n =>
      change n • (⟦L⟧ : RelativePicardClass f) = ⟦L.tensorPow n⟧
      exact nsmul_mk L n
  | negSucc n =>
      rw [negSucc_zsmul, ← neg_nsmul]
      change (n + 1) • dual (⟦L⟧ : RelativePicardClass f) =
        ⟦L.dual.tensorPow (n + 1)⟧
      rw [dual_mk, nsmul_mk]

/-- Pullback of relative Picard classes along an arbitrary base morphism. -/
def pullback {X S T : Scheme.{u}} {f : X ⟶ S} (b : T ⟶ S) :
    RelativePicardClass f →
      RelativePicardClass (CategoryTheory.Limits.pullback.snd f b) :=
  Quotient.map (fun L ↦ L.pullback b) (by
    intro L N h
    rcases h with ⟨⟨e⟩, hdegree⟩
    refine ⟨⟨(Scheme.Modules.pullback
      (CategoryTheory.Limits.pullback.fst f b)).mapIso e⟩, ?_⟩
    simp only [RelativeLineBundle.pullback]
    funext K _ y C
    change L.componentDegree K (y ≫ b) _ = N.componentDegree K (y ≫ b) _
    rw [hdegree])

@[simp]
theorem pullback_mk {X S T : Scheme.{u}} {f : X ⟶ S} (b : T ⟶ S)
    (L : RelativeLineBundle f) :
    pullback b (⟦L⟧ : RelativePicardClass f) = ⟦L.pullback b⟧ := rfl

/-- Arbitrary base change is additive on relative Picard classes. -/
def pullbackHom {X S T : Scheme.{u}} {f : X ⟶ S} (b : T ⟶ S) :
    RelativePicardClass f →+
      RelativePicardClass (CategoryTheory.Limits.pullback.snd f b) where
  toFun := pullback b
  map_zero' := by
    apply Quotient.sound
    refine ⟨⟨LineBundle.pullbackTrivialIso
      (CategoryTheory.Limits.pullback.fst f b)⟩, ?_⟩
    funext K hK y C
    rfl
  map_add' := by
    intro a c
    refine Quotient.inductionOn₂ a c ?_
    intro L N
    apply Quotient.sound
    refine ⟨⟨LineBundle.pullbackTensorIso
      (CategoryTheory.Limits.pullback.fst f b) L.line N.line⟩, ?_⟩
    funext K hK y C
    rfl

/-- Base change preserves dual relative Picard classes. -/
@[simp]
theorem pullback_neg {X S T : Scheme.{u}} {f : X ⟶ S} (b : T ⟶ S)
    (a : RelativePicardClass f) : pullback b (-a) = -(pullback b a) :=
  map_neg (pullbackHom b) a

end RelativePicardClass

/-- Additive notation for the Picard group, with addition given by tensor product. -/
instance picardClassAddCommGroup (X : Scheme.{u}) : AddCommGroup (PicardClass X) where
  add := fun a b ↦ a * b
  add_assoc := mul_assoc
  zero := 1
  zero_add := one_mul
  add_zero := mul_one
  nsmul := fun n a ↦ a ^ n
  nsmul_zero := pow_zero
  nsmul_succ := fun n a ↦ pow_succ a n
  neg := Inv.inv
  zsmul := fun n a ↦ a ^ n
  zsmul_zero' := zpow_zero
  zsmul_succ' := DivInvMonoid.zpow_succ'
  zsmul_neg' := DivInvMonoid.zpow_neg'
  neg_add_cancel := inv_mul_cancel
  add_comm := mul_comm

namespace ArithmeticSurface.SpecialFiberIntersectionData

variable (D : ArithmeticSurface.SpecialFiberIntersectionData M)

/-- The divisor of component degrees of a relative line bundle on the scheme-theoretic special
fibre. -/
def specialFiberDegreeDivisor (L : RelativeLineBundle M.toBase) :
    D.toNumericalType.Divisor := fun i ↦
  L.degree (specialPointMap R) i

/-- Specialization of a relative Picard class to the weighted numerical Picard group of the
actual special fibre. -/
def specialize : RelativePicardClass M.toBase → D.toNumericalType.Pic :=
  Quotient.lift (fun L ↦ QuotientAddGroup.mk (D.specialFiberDegreeDivisor L)) (by
    intro L N h
    rcases h with ⟨-, hdegree⟩
    apply congrArg QuotientAddGroup.mk
    funext i
    simp only [specialFiberDegreeDivisor, RelativeLineBundle.degree]
    rw [hdegree])

/-- Restriction of a relative class to the actual generic-fibre scheme. -/
def restrictGeneric (_D : ArithmeticSurface.SpecialFiberIntersectionData M) :
    RelativePicardClass M.toBase →
    PicardClass (genericFiber R K M.toBase).left :=
  Quotient.lift (fun L ↦ Quotient.mk _ (L.line.pullback (genericFiberι R K M.toBase))) (by
    intro L N h
    rcases h with ⟨⟨e⟩, -⟩
    apply Quotient.sound
    exact ⟨(Scheme.Modules.pullback (genericFiberι R K M.toBase)).mapIso e⟩)

/-- Specialization as an additive homomorphism. -/
def specializationHom : RelativePicardClass M.toBase →+ D.toNumericalType.Pic where
  toFun := D.specialize
  map_zero' := by
    apply congrArg QuotientAddGroup.mk
    funext i
    rfl
  map_add' := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro L N
    apply congrArg QuotientAddGroup.mk
    funext i
    rfl

/-- Generic-fibre restriction as an additive homomorphism. -/
def genericRestrictionHom :
    RelativePicardClass M.toBase →+
      PicardClass (genericFiber R K M.toBase).left where
  toFun := D.restrictGeneric
  map_zero' := by
    apply Quotient.sound
    exact ⟨LineBundle.pullbackTrivialIso (genericFiberι R K M.toBase)⟩
  map_add' := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro L N
    apply Quotient.sound
    exact ⟨LineBundle.pullbackTensorIso
      (genericFiberι R K M.toBase) L.line N.line⟩

end ArithmeticSurface.SpecialFiberIntersectionData

/-- The two geometric inputs needed to descend numerical specialization to the generic Picard
group.  Surjectivity says that every generic class extends to the model.  Kernel containment says
that two extensions of the same generic class have the same numerical specialization. -/
structure JacobianSpecializationData
    (D : ArithmeticSurface.SpecialFiberIntersectionData M) : Prop where
  restriction_surjective : Function.Surjective D.genericRestrictionHom
  specialization_ker : D.genericRestrictionHom.ker ≤ D.specializationHom.ker

namespace JacobianSpecializationData

variable {D : ArithmeticSurface.SpecialFiberIntersectionData M}

/-- A chosen extension of a generic Picard class.  No additive structure is imposed on this
choice; additivity of specialization follows from independence of extensions. -/
noncomputable def extension (J : JacobianSpecializationData D)
    (x : PicardClass (genericFiber R K M.toBase).left) :
    RelativePicardClass M.toBase :=
  Classical.choose (J.restriction_surjective x)

@[simp]
theorem restriction_extension (J : JacobianSpecializationData D)
    (x : PicardClass (genericFiber R K M.toBase).left) :
    D.genericRestrictionHom (J.extension x) = x :=
  Classical.choose_spec (J.restriction_surjective x)

/-- Numerical specialization is equal for any two relative classes with the same generic
restriction. -/
theorem specialization_eq_of_restriction_eq (J : JacobianSpecializationData D)
    {a b : RelativePicardClass M.toBase}
    (h : D.genericRestrictionHom a = D.genericRestrictionHom b) :
    D.specializationHom a = D.specializationHom b := by
  have hab : a - b ∈ D.genericRestrictionHom.ker := by
    rw [AddMonoidHom.mem_ker, map_sub, h, sub_self]
  have hs := J.specialization_ker hab
  rw [AddMonoidHom.mem_ker, map_sub, sub_eq_zero] at hs
  exact hs

/-- Specialization from the geometric generic Picard group to the weighted numerical Picard
group of the special fibre. -/
noncomputable def genericSpecialization (J : JacobianSpecializationData D) :
    PicardClass (genericFiber R K M.toBase).left →+ D.toNumericalType.Pic where
  toFun := fun x ↦ D.specializationHom (J.extension x)
  map_zero' := by
    rw [← map_zero D.specializationHom]
    apply J.specialization_eq_of_restriction_eq
    rw [J.restriction_extension, map_zero]
  map_add' := by
    intro x y
    rw [← map_add D.specializationHom]
    apply J.specialization_eq_of_restriction_eq
    rw [J.restriction_extension, map_add, J.restriction_extension,
      J.restriction_extension]

/-- Descended generic specialization agrees with numerical specialization on every relative
line-bundle class. -/
@[simp]
theorem genericSpecialization_restrict (J : JacobianSpecializationData D)
    (a : RelativePicardClass M.toBase) :
    J.genericSpecialization (D.genericRestrictionHom a) = D.specializationHom a := by
  apply J.specialization_eq_of_restriction_eq
  rw [J.restriction_extension]

/-- Generic specialization is the unique additive map whose composite with generic restriction
is numerical specialization. -/
theorem genericSpecialization_unique (J : JacobianSpecializationData D)
    (φ : PicardClass (genericFiber R K M.toBase).left →+ D.toNumericalType.Pic)
    (hφ : φ.comp D.genericRestrictionHom = D.specializationHom) :
    φ = J.genericSpecialization := by
  ext x
  obtain ⟨a, rfl⟩ := J.restriction_surjective x
  calc
    φ (D.genericRestrictionHom a) = D.specializationHom a :=
      DFunLike.congr_fun hφ a
    _ = J.genericSpecialization (D.genericRestrictionHom a) :=
      (J.genericSpecialization_restrict a).symm

/-- Any extension of a generic class has the same numerical specialization as the selected one. -/
theorem specialize_extension_independent (J : JacobianSpecializationData D)
    (a : RelativePicardClass M.toBase)
    (x : PicardClass (genericFiber R K M.toBase).left)
    (ha : D.genericRestrictionHom a = x) :
    D.specializationHom a = J.genericSpecialization x := by
  apply J.specialization_eq_of_restriction_eq
  rw [ha, J.restriction_extension]

/-- `ℓ`-torsion in the geometric generic Picard group. -/
def genericTorsion (_J : JacobianSpecializationData D) (ℓ : ℕ) :
    AddSubgroup (PicardClass (genericFiber R K M.toBase).left) :=
  AddSubgroup.torsionBy _ (ℓ : ℤ)

/-- Generic Picard `ℓ`-torsion is naturally a module over `ZMod ℓ`. -/
noncomputable instance genericTorsion_zmodModule
    (J : JacobianSpecializationData D) (ℓ : ℕ) :
    Module (ZMod ℓ) (J.genericTorsion ℓ) := by
  unfold genericTorsion
  exact AddSubgroup.torsionBy.zmodModule

/-- Generic Jacobian torsion specializes to numerical Picard torsion. -/
def torsionSpecialization (J : JacobianSpecializationData D) (ℓ : ℕ) :
    J.genericTorsion ℓ →+ D.toNumericalType.torsion ℓ := by
  exact
    { toFun := fun x ↦ ⟨J.genericSpecialization x, by
        change (ℓ : ℤ) • J.genericSpecialization (x :
          PicardClass (genericFiber R K M.toBase).left) = 0
        rw [← map_zsmul]
        have hx : (ℓ : ℤ) • (x : PicardClass (genericFiber R K M.toBase).left) = 0 :=
          x.property
        rw [hx, map_zero]⟩
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }

/-- The torsion specialization map as a linear map over the prime residue ring. -/
def torsionSpecializationLinear (J : JacobianSpecializationData D) (ℓ : ℕ) :
    J.genericTorsion ℓ →ₗ[ZMod ℓ] D.toNumericalType.torsion ℓ := by
  exact
    { J.torsionSpecialization ℓ with
      map_smul' := fun c x ↦ ZMod.map_smul (J.torsionSpecialization ℓ) c x }

/-- The rank-nullity bridge used in Stacks Project tag `0CAD`: if generic `ℓ`-torsion has
dimension `2g`, then the kernel of numerical specialization has dimension at least
`2g - dim Pic(T)[ℓ]`.  This kernel, rather than the whole generic torsion group, is the object
that the geometric specialization exact sequence embeds into the reduced special fibre. -/
theorem two_mul_genus_sub_primeTorsionDimension_le_kernel_finrank
    (J : JacobianSpecializationData D) (ℓ g : ℕ) [Fact ℓ.Prime]
    [Module.Finite (ZMod ℓ) (J.genericTorsion ℓ)]
    (hfull : Module.finrank (ZMod ℓ) (J.genericTorsion ℓ) = 2 * g) :
    2 * g - D.toNumericalType.primeTorsionDimension ℓ ≤
      Module.finrank (ZMod ℓ) (LinearMap.ker (J.torsionSpecializationLinear ℓ)) := by
  have hrank := (J.torsionSpecializationLinear ℓ).finrank_range_add_finrank_ker
  have hrange : Module.finrank (ZMod ℓ)
      (LinearMap.range (J.torsionSpecializationLinear ℓ)) ≤
      D.toNumericalType.primeTorsionDimension ℓ := by
    apply LinearMap.finrank_le_finrank_of_injective
      (f := (LinearMap.range (J.torsionSpecializationLinear ℓ)).subtype)
    exact Subtype.val_injective
  rw [hfull] at hrank
  rw [Nat.sub_le_iff_le_add]
  omega

/-- The numerical equality squeeze in the higher-genus semistable-reduction argument.

The first two inequalities are the Picard-specialization output: the specialization kernel is
large by rank-nullity and embeds into the reduced-fibre Picard torsion.  The next inequality is
the lower coherent-cohomology estimate for the reduced special fibre.  Strictness of the usual
upper estimate for a nonreduced fibre then forces every component multiplicity to be one. -/
theorem all_multiplicities_one_of_full_torsion
    (J : JacobianSpecializationData D) (ℓ g h1 geometricGenus : ℕ) [Fact ℓ.Prime]
    [Module.Finite (ZMod ℓ) (J.genericTorsion ℓ)]
    (hfull : Module.finrank (ZMod ℓ) (J.genericTorsion ℓ) = 2 * g)
    (hpicard : D.toNumericalType.primeTorsionDimension ℓ ≤
      D.toNumericalType.topologicalGenus)
    (hkernel : Module.finrank (ZMod ℓ)
      (LinearMap.ker (J.torsionSpecializationLinear ℓ)) ≤ h1 + geometricGenus)
    (hcohomologyLower : D.toNumericalType.topologicalGenus + geometricGenus ≤ h1)
    (hstrict : (∃ i, D.multiplicity i ≠ 1) → h1 < g) :
    ∀ i, D.multiplicity i = 1 := by
  have hkernelLower :=
    J.two_mul_genus_sub_primeTorsionDimension_le_kernel_finrank ℓ g hfull
  have hsub : 2 * g - D.toNumericalType.topologicalGenus ≤
      2 * g - D.toNumericalType.primeTorsionDimension ℓ :=
    Nat.sub_le_sub_left hpicard (2 * g)
  have hlargeKernel : 2 * g - D.toNumericalType.topologicalGenus ≤
      Module.finrank (ZMod ℓ)
        (LinearMap.ker (J.torsionSpecializationLinear ℓ)) :=
    hsub.trans hkernelLower
  have hreduced : ¬ ∃ i, D.multiplicity i ≠ 1 := by
    intro hnonreduced
    have hupperStrict := hstrict hnonreduced
    omega
  intro i
  by_contra hi
  exact hreduced ⟨i, hi⟩

/-- The `ℓ > 768g` specialization of the multiplicity-one criterion.  The global numerical
estimate supplies the Picard-dimension hypothesis; the remaining assumptions are precisely the
geometric Picard-kernel and reduced-fibre cohomology inputs in the later roadmap layers. -/
theorem all_multiplicities_one_of_large_prime_full_torsion
    (J : JacobianSpecializationData D) (hmin : D.toNumericalType.IsMinimal)
    (hgenus : 2 ≤ D.toNumericalType.arithmeticGenus)
    (ℓ g h1 geometricGenus : ℕ) [Fact ℓ.Prime]
    [Module.Finite (ZMod ℓ) (J.genericTorsion ℓ)]
    (hlarge : 768 * D.toNumericalType.arithmeticGenus < (ℓ : ℤ))
    (hfull : Module.finrank (ZMod ℓ) (J.genericTorsion ℓ) = 2 * g)
    (hkernel : Module.finrank (ZMod ℓ)
      (LinearMap.ker (J.torsionSpecializationLinear ℓ)) ≤ h1 + geometricGenus)
    (hcohomologyLower : D.toNumericalType.topologicalGenus + geometricGenus ≤ h1)
    (hstrict : (∃ i, D.multiplicity i ≠ 1) → h1 < g) :
    ∀ i, D.multiplicity i = 1 := by
  apply J.all_multiplicities_one_of_full_torsion ℓ g h1 geometricGenus hfull
  · exact D.toNumericalType.primeTorsionDimension_le_topologicalGenus_of_large_prime
      hmin hgenus ℓ hlarge
  · exact hkernel
  · exact hcohomologyLower
  · exact hstrict

end JacobianSpecializationData

/-- The integer `ℓ` is invertible in the special residue field, hence prime to its
characteristic. -/
def PrimeToSpecialCharacteristic (ℓ : ℕ) : Prop :=
  algebraMap ℤ (specialResidueField R) (ℓ : ℤ) ≠ 0

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction
