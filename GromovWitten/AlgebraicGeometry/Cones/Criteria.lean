/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.Cones.Picard

/-!
# Cohomological criteria for morphisms of `h¹/h⁰` groupoids

`Cones/Picard.lean` attaches to a two-term complex `E = [E⁰ → E¹]` of `R`-modules its Picard
groupoid `E.quotient = [E¹/E⁰]`, the fibrewise model of `h¹/h⁰(E)`, and turns a chain map into a
functor.  This file proves that *every* geometric property of that functor is detected by the two
cohomology modules

* `h⁰(E) = ker(E.differential)`, which is the automorphism group of every object, and
* `h¹(E) = coker(E.differential)`, which is the set of isomorphism classes of objects.

## Main results

* `PicardCriteria.autEquivKernel`, `PicardCriteria.homEquivKernel`: every automorphism group is
  `h⁰`, and every nonempty hom-set is a torsor under `h⁰`.
* `PicardCriteria.isoClass`, `PicardCriteria.isoClass_eq_iff`,
  `PicardCriteria.isoClass_surjective`: isomorphism classes of objects are exactly `h¹`.
* `PicardCriteria.faithful_iff`, `PicardCriteria.full_iff`, `PicardCriteria.essSurj_iff`,
  `PicardCriteria.isEquivalence_iff`: the induced functor is faithful iff `h⁰(φ)` is injective,
  full iff `h⁰(φ)` is surjective *and* `h¹(φ)` is injective, essentially surjective iff `h¹(φ)`
  is surjective, and an equivalence iff `φ` is a quasi-isomorphism.  The last statement is the
  converse of `LinearTwoTermComplex.Hom.IsQuasiIsomorphism.quotientEquivalence`.
* `PicardCriteria.IsCohomologicalMono`, `PicardCriteria.isCohomologicalMono_iff_fullyFaithful`,
  `PicardCriteria.IsCohomologicalMono.injective_isoClass`,
  `PicardCriteria.quotientFunctor_cancel`: the "closed immersion" criterion.  A chain map with
  `h⁰(φ)` bijective and `h¹(φ)` injective induces a fully faithful functor which is injective on
  isomorphism classes, and if `φ` is moreover degreewise injective the induced functor is a
  monomorphism, in the strict sense that it can be cancelled on the left.
* `PicardCriteria.ShortExact` and its namespace: a degreewise short exact sequence
  `0 → K' → K → K'' → 0` of two-term complexes has a connecting homomorphism
  `PicardCriteria.ShortExact.delta : h⁰(K'') → h¹(K')` constructed from lifts and proved
  independent of them, and the six-term cohomology sequence is exact
  (`injective_kernelMap`, `exact_h0_middle`, `exact_h0_right`, `exact_h1_left`,
  `exact_h1_middle`, `surjective_cokernelMap`).  Geometrically this makes
  `[K¹/K⁰] → [K''¹/K''⁰]` essentially surjective, exhibits the fibres of the map on hom-sets as
  torsors under `h⁰(K')` (`hom_fibre_torsor`) and the fibres on isomorphism classes as the
  orbits of the translation action of `[K'¹/K'⁰]` (`translate`, `translateInvarianceIso`,
  `nonempty_iso_map_iff`); if `K''` is acyclic the inclusion induces an equivalence
  (`isQuasiIsomorphism_of_acyclic`, `quotientEquivalenceOfAcyclic`).

`Cones/CriteriaBundle.lean` continues with virtual ranks of complexes of finite free modules and
with the prestack of fibres of `h¹/h⁰(Eᵛ)` on the affine objects of the big fppf site.

Nothing here is stored as a structure field: every geometric conclusion is derived from the
cohomological hypotheses.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry

namespace PicardCriteria

universe u v

variable {R : Type u} [CommRing R] {E F G : LinearTwoTermComplex R}

open LinearTwoTermComplex

/-! ## The cohomology of a two-term complex -/

/-- Degree-zero cohomology of a two-term complex: the kernel of the differential.  It is the
automorphism group of every object of the Picard groupoid. -/
abbrev h0 (E : LinearTwoTermComplex R) : Submodule R E.degreeZero :=
  LinearMap.ker E.differential

/-- Degree-one cohomology of a two-term complex: the cokernel of the differential.  It is the
module of isomorphism classes of objects of the Picard groupoid. -/
abbrev h1 (E : LinearTwoTermComplex R) : Type u :=
  E.degreeOne ⧸ (LinearMap.range E.differential : Submodule R E.degreeOne)

/-- The class in `h¹` of an element of `E¹`. -/
abbrev h1mk (E : LinearTwoTermComplex R) (x : E.degreeOne) : h1 E :=
  Submodule.Quotient.mk x

theorem h1mk_eq_zero_iff (x : E.degreeOne) :
    h1mk E x = 0 ↔ x ∈ LinearMap.range E.differential :=
  Submodule.Quotient.mk_eq_zero _

theorem h1mk_surjective : Function.Surjective (h1mk E) :=
  Submodule.Quotient.mk_surjective _

@[simp]
theorem h1mk_add (x y : E.degreeOne) : h1mk E (x + y) = h1mk E x + h1mk E y :=
  rfl

@[simp]
theorem h1mk_zero : h1mk E 0 = 0 :=
  rfl

@[simp]
theorem h1mk_sub (x y : E.degreeOne) : h1mk E (x - y) = h1mk E x - h1mk E y :=
  rfl

theorem h1mk_eq_iff (x y : E.degreeOne) :
    h1mk E x = h1mk E y ↔ x - y ∈ LinearMap.range E.differential :=
  Submodule.Quotient.eq _

/-- Objects of a Picard groupoid are determined by their underlying element of `E¹`. -/
theorem quotient_ext {x y : E.quotient} (h : x.back = y.back) : x = y := by
  cases x
  cases y
  exact congrArg TwoTermQuotient.mk h

@[simp]
theorem cokernelMap_h1mk (f : Hom E F) (x : E.degreeOne) :
    f.cokernelMap (h1mk E x) = h1mk F (f.degreeOne x) :=
  rfl

@[simp]
theorem kernelMap_coe (f : Hom E F) (a : h0 E) :
    ((f.kernelMap a : h0 F) : F.degreeZero) = f.degreeZero (a : E.degreeZero) :=
  rfl

/-! ## Automorphisms, hom-sets and isomorphism classes -/

/-- The automorphism group of an object of the Picard groupoid is `h⁰`, independently of the
object. -/
def autEquivKernel (x : E.quotient) : (x ⟶ x) ≃ h0 E where
  toFun a := ⟨a.val, by
    rw [LinearMap.mem_ker]
    exact add_left_cancel (a.translate.trans (add_zero x.back).symm)⟩
  invFun a := ⟨(a : E.degreeZero), by rw [LinearMap.mem_ker.mp a.2, add_zero]⟩
  left_inv a := by apply TwoTermQuotient.Hom.ext; rfl
  right_inv a := by apply Subtype.ext; rfl

@[simp]
theorem autEquivKernel_apply_coe (x : E.quotient) (a : x ⟶ x) :
    ((autEquivKernel x a : h0 E) : E.degreeZero) = a.val :=
  rfl

@[simp]
theorem autEquivKernel_symm_apply_val (x : E.quotient) (a : h0 E) :
    ((autEquivKernel x).symm a).val = (a : E.degreeZero) :=
  rfl

/-- Under the identification of automorphisms with `h⁰`, composition is addition. -/
theorem autEquivKernel_comp (x : E.quotient) (a b : x ⟶ x) :
    autEquivKernel x (a ≫ b) = autEquivKernel x a + autEquivKernel x b :=
  rfl

/-- Under the identification of automorphisms with `h⁰`, the induced functor acts by `h⁰(φ)`. -/
theorem autEquivKernel_map (f : Hom E F) (x : E.quotient) (a : x ⟶ x) :
    autEquivKernel (f.quotientFunctor.obj x) (f.quotientFunctor.map a) =
      f.kernelMap (autEquivKernel x a) :=
  rfl

/-- Every nonempty hom-set of the Picard groupoid is a torsor under `h⁰`: choosing one arrow
`b : x ⟶ y` identifies all arrows `x ⟶ y` with `h⁰`. -/
def homEquivKernel {x y : E.quotient} (b : x ⟶ y) : (x ⟶ y) ≃ h0 E where
  toFun a := ⟨a.val - b.val, by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact add_left_cancel (a.translate.trans b.translate.symm)⟩
  invFun a := ⟨b.val + (a : E.degreeZero), by
    rw [map_add, LinearMap.mem_ker.mp a.2, add_zero, b.translate]⟩
  left_inv a := by
    apply TwoTermQuotient.Hom.ext
    change b.val + (a.val - b.val) = a.val
    abel
  right_inv a := by
    apply Subtype.ext
    change b.val + (a : E.degreeZero) - b.val = (a : E.degreeZero)
    abel

@[simp]
theorem homEquivKernel_apply_coe {x y : E.quotient} (b a : x ⟶ y) :
    ((homEquivKernel b a : h0 E) : E.degreeZero) = a.val - b.val :=
  rfl

/-- The isomorphism class of an object of the Picard groupoid, as an element of `h¹`. -/
def isoClass (x : E.quotient) : h1 E :=
  h1mk E x.back

@[simp]
theorem isoClass_def (x : E.quotient) : isoClass x = h1mk E x.back :=
  rfl

/-- Two objects of the Picard groupoid are isomorphic exactly when they have the same class in
`h¹`. -/
theorem isoClass_eq_iff (x y : E.quotient) : isoClass x = isoClass y ↔ Nonempty (x ≅ y) := by
  rw [isoClass, isoClass, TwoTermQuotient.nonempty_iso_iff]
  rw [Submodule.Quotient.eq]
  constructor
  · intro h
    simpa only [neg_sub] using (LinearMap.range E.differential).neg_mem h
  · intro h
    simpa only [neg_sub] using (LinearMap.range E.differential).neg_mem h

/-- Every class in `h¹` is the isomorphism class of an object. -/
theorem isoClass_surjective : Function.Surjective (isoClass (E := E)) := by
  intro q
  obtain ⟨y, rfl⟩ := h1mk_surjective q
  exact ⟨⟨y⟩, rfl⟩

/-- On isomorphism classes, the functor induced by a chain map is `h¹(φ)`. -/
@[simp]
theorem isoClass_map (f : Hom E F) (x : E.quotient) :
    isoClass (f.quotientFunctor.obj x) = f.cokernelMap (isoClass x) :=
  rfl


/-! ## The cohomological criteria -/

/-- Faithfulness is exactly injectivity of `h⁰(φ)`. -/
theorem faithful_iff (f : Hom E F) :
    f.quotientFunctor.Faithful ↔ Function.Injective f.kernelMap := by
  constructor
  · intro hF a b hab
    let x : E.quotient := ⟨0⟩
    let a' : x ⟶ x := (autEquivKernel x).symm a
    let b' : x ⟶ x := (autEquivKernel x).symm b
    have h : f.quotientFunctor.map a' = f.quotientFunctor.map b' := by
      apply TwoTermQuotient.Hom.ext
      change f.degreeZero (a : E.degreeZero) = f.degreeZero (b : E.degreeZero)
      exact congrArg Subtype.val hab
    have h' := hF.map_injective h
    exact (autEquivKernel x).symm.injective h'
  · intro hker
    refine ⟨fun {x y} a b hab => ?_⟩
    apply TwoTermQuotient.Hom.ext
    let c : h0 E := ⟨a.val - b.val, by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact add_left_cancel (a.translate.trans b.translate.symm)⟩
    have hc : f.kernelMap c = 0 := by
      apply Subtype.ext
      change f.degreeZero (a.val - b.val) = 0
      rw [map_sub, sub_eq_zero]
      exact congrArg TwoTermQuotient.Hom.val hab
    have hc0 : c = 0 := hker (by simpa using hc)
    exact sub_eq_zero.mp (congrArg Subtype.val hc0)

/-- Essential surjectivity is exactly surjectivity of `h¹(φ)`. -/
theorem essSurj_iff (f : Hom E F) :
    f.quotientFunctor.EssSurj ↔ Function.Surjective f.cokernelMap := by
  constructor
  · intro hF q
    obtain ⟨y, rfl⟩ := h1mk_surjective q
    obtain ⟨x, ⟨e⟩⟩ := hF.mem_essImage (⟨y⟩ : F.quotient)
    refine ⟨isoClass x, ?_⟩
    rw [← isoClass_map]
    exact (isoClass_eq_iff _ _).2 ⟨e⟩
  · intro hcok
    apply Hom.quotientFunctorEssSurj
    intro y
    obtain ⟨q, hq⟩ := hcok (h1mk F y)
    obtain ⟨x, rfl⟩ := h1mk_surjective q
    refine ⟨x, ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
    exact hq.symm

/-- Fullness is exactly surjectivity of `h⁰(φ)` together with injectivity of `h¹(φ)`.  The second
condition is what forbids the functor from creating isomorphisms between non-isomorphic
objects. -/
theorem full_iff (f : Hom E F) :
    f.quotientFunctor.Full ↔
      (Function.Surjective f.kernelMap ∧ Function.Injective f.cokernelMap) := by
  constructor
  · intro hF
    constructor
    · intro c
      let x : E.quotient := ⟨0⟩
      let a : f.quotientFunctor.obj x ⟶ f.quotientFunctor.obj x :=
        (autEquivKernel (f.quotientFunctor.obj x)).symm c
      obtain ⟨b, hb⟩ := hF.map_surjective a
      refine ⟨autEquivKernel x b, ?_⟩
      apply Subtype.ext
      change f.degreeZero b.val = (c : F.degreeZero)
      exact congrArg TwoTermQuotient.Hom.val hb
    · intro q q' hq
      obtain ⟨y, rfl⟩ := h1mk_surjective q
      obtain ⟨y', rfl⟩ := h1mk_surjective q'
      have hmem : f.degreeOne (y' - y) ∈ LinearMap.range F.differential := by
        rw [← h1mk_eq_zero_iff, map_sub]
        change h1mk F (f.degreeOne y') - h1mk F (f.degreeOne y) = 0
        rw [sub_eq_zero]
        exact hq.symm
      obtain ⟨c, hc⟩ := hmem
      let x : E.quotient := ⟨y⟩
      let x' : E.quotient := ⟨y'⟩
      let a : f.quotientFunctor.obj x ⟶ f.quotientFunctor.obj x' := ⟨c, by
        change f.degreeOne y + F.differential c = f.degreeOne y'
        rw [hc, map_sub]
        abel⟩
      obtain ⟨b, hb⟩ := hF.map_surjective a
      have hb' : y + E.differential b.val = y' := b.translate
      change h1mk E y = h1mk E y'
      rw [Submodule.Quotient.eq]
      refine ⟨-b.val, ?_⟩
      rw [map_neg, ← hb']
      abel
  · rintro ⟨hker, hcok⟩
    refine ⟨fun {x y} a => ?_⟩
    let q : h1 E := h1mk E (y.back - x.back)
    have hq : f.cokernelMap q = 0 := by
      change h1mk F (f.degreeOne (y.back - x.back)) = 0
      rw [h1mk_eq_zero_iff]
      refine ⟨a.val, ?_⟩
      have ha := a.translate
      dsimp [Hom.quotientFunctor] at ha
      rw [map_sub]
      exact eq_sub_of_add_eq' ha
    have hq0 : q = 0 := hcok (by simpa using hq)
    obtain ⟨b₀, hb₀⟩ := (h1mk_eq_zero_iff (E := E) (y.back - x.back)).1 hq0
    let c : h0 F :=
      ⟨a.val - f.degreeZero b₀, by
        rw [LinearMap.mem_ker, map_sub, ← f.comm, hb₀, sub_eq_zero]
        have ha := a.translate
        dsimp [Hom.quotientFunctor] at ha
        rw [map_sub]
        exact eq_sub_of_add_eq' ha⟩
    obtain ⟨c', hc'⟩ := hker c
    refine ⟨⟨b₀ + (c' : E.degreeZero), ?_⟩, ?_⟩
    · rw [map_add, LinearMap.mem_ker.mp c'.2, add_zero, hb₀]
      abel
    · apply TwoTermQuotient.Hom.ext
      have hc'' := congrArg Subtype.val hc'
      change f.degreeZero (c' : E.degreeZero) = a.val - f.degreeZero b₀ at hc''
      change f.degreeZero (b₀ + (c' : E.degreeZero)) = a.val
      rw [map_add, hc'']
      abel

/-- The equivalence criterion: the functor induced on Picard groupoids is an equivalence exactly
when the chain map is a quasi-isomorphism, that is, exactly when it induces bijections on `h⁰`
and on `h¹`.  The forward implication is the converse of
`LinearTwoTermComplex.Hom.IsQuasiIsomorphism.quotientEquivalence`. -/
theorem isEquivalence_iff (f : Hom E F) :
    f.quotientFunctor.IsEquivalence ↔ f.IsQuasiIsomorphism := by
  constructor
  · intro hF
    have hfaithful : Function.Injective f.kernelMap := (faithful_iff f).1 inferInstance
    obtain ⟨hker, hcok⟩ := (full_iff f).1 inferInstance
    have hess : Function.Surjective f.cokernelMap := (essSurj_iff f).1 inferInstance
    exact ⟨⟨hfaithful, hker⟩, ⟨hcok, hess⟩⟩
  · rintro ⟨⟨hkinj, hksurj⟩, ⟨hcinj, hcsurj⟩⟩
    have _ : f.quotientFunctor.Faithful := (faithful_iff f).2 hkinj
    have _ : f.quotientFunctor.Full := (full_iff f).2 ⟨hksurj, hcinj⟩
    have _ : f.quotientFunctor.EssSurj := (essSurj_iff f).2 hcsurj
    exact { }

/-- A chain map whose induced functor on Picard groupoids is an equivalence is a
quasi-isomorphism. -/
theorem isQuasiIsomorphism_of_isEquivalence (f : Hom E F)
    (h : f.quotientFunctor.IsEquivalence) : f.IsQuasiIsomorphism :=
  (isEquivalence_iff f).1 h

/-! ## The monomorphism (closed immersion) criterion -/

/-- The cohomological criterion for `h¹/h⁰(φ)` to be a monomorphism of groupoids: an isomorphism
on `h⁰` and an injection on `h¹`.  This is the algebraic shadow of a closed immersion of cone
stacks: no automorphisms are lost or gained, and distinct isomorphism classes stay distinct. -/
def IsCohomologicalMono (f : Hom E F) : Prop :=
  Function.Bijective f.kernelMap ∧ Function.Injective f.cokernelMap

namespace IsCohomologicalMono

variable {f : Hom E F}

/-- The criterion is exactly full faithfulness of the induced functor. -/
theorem iff_full_and_faithful (f : Hom E F) :
    IsCohomologicalMono f ↔ (f.quotientFunctor.Full ∧ f.quotientFunctor.Faithful) := by
  constructor
  · rintro ⟨⟨hkinj, hksurj⟩, hcinj⟩
    exact ⟨(full_iff f).2 ⟨hksurj, hcinj⟩, (faithful_iff f).2 hkinj⟩
  · rintro ⟨hfull, hfaithful⟩
    obtain ⟨hksurj, hcinj⟩ := (full_iff f).1 hfull
    exact ⟨⟨(faithful_iff f).1 hfaithful, hksurj⟩, hcinj⟩

/-- The induced functor is full. -/
theorem full (h : IsCohomologicalMono f) : f.quotientFunctor.Full :=
  ((iff_full_and_faithful f).1 h).1

/-- The induced functor is faithful. -/
theorem faithful (h : IsCohomologicalMono f) : f.quotientFunctor.Faithful :=
  ((iff_full_and_faithful f).1 h).2

/-- The induced functor is fully faithful, as data. -/
noncomputable def fullyFaithful (h : IsCohomologicalMono f) :
    f.quotientFunctor.FullyFaithful :=
  have _ := h.full
  have _ := h.faithful
  Functor.FullyFaithful.ofFullyFaithful f.quotientFunctor

/-- The induced functor is injective on isomorphism classes. -/
theorem injective_isoClass (h : IsCohomologicalMono f) {x y : E.quotient}
    (hxy : Nonempty (f.quotientFunctor.obj x ≅ f.quotientFunctor.obj y)) :
    Nonempty (x ≅ y) := by
  rw [← isoClass_eq_iff]
  apply h.2
  rw [← isoClass_map, ← isoClass_map]
  exact (isoClass_eq_iff _ _).2 hxy

/-- A quasi-isomorphism satisfies the monomorphism criterion. -/
theorem of_isQuasiIsomorphism (h : f.IsQuasiIsomorphism) : IsCohomologicalMono f :=
  ⟨h.1, h.2.1⟩

/-- The monomorphism criterion together with essential surjectivity, that is, with surjectivity
of `h¹(φ)`, is the equivalence criterion. -/
theorem isQuasiIsomorphism_of_surjective (h : IsCohomologicalMono f)
    (hsurj : Function.Surjective f.cokernelMap) : f.IsQuasiIsomorphism :=
  ⟨h.1, h.2, hsurj⟩

end IsCohomologicalMono

/-- An equality of objects of a Picard groupoid induces the zero translation. -/
@[simp]
theorem eqToHom_val {x y : E.quotient} (h : x = y) : (eqToHom h).val = 0 := by
  subst h
  rfl

/-- If a chain map is injective in both degrees, the induced functor is a monomorphism: it can be
cancelled on the left.  Together with `IsCohomologicalMono` this is the full strength of the
"closed immersion" criterion, the cohomological part giving full faithfulness and the degreewise
part giving injectivity on objects. -/
theorem quotientFunctor_cancel (f : Hom E F)
    (hzero : Function.Injective f.degreeZero) (hone : Function.Injective f.degreeOne)
    {X : Type v} [Category.{v} X] (P Q : X ⥤ E.quotient)
    (h : P ⋙ f.quotientFunctor = Q ⋙ f.quotientFunctor) : P = Q := by
  have hobj : ∀ x : X, P.obj x = Q.obj x := by
    intro x
    have hx := Functor.congr_obj h x
    have hback : f.degreeOne (P.obj x).back = f.degreeOne (Q.obj x).back :=
      congrArg TwoTermQuotient.back hx
    have := hone hback
    cases hP : P.obj x with
    | mk p =>
      cases hQ : Q.obj x with
      | mk q =>
        rw [hP, hQ] at this
        exact congrArg TwoTermQuotient.mk this
  refine CategoryTheory.Functor.ext hobj fun x y a => ?_
  apply TwoTermQuotient.Hom.ext
  apply hzero
  have hval := congrArg TwoTermQuotient.Hom.val (Functor.congr_hom h a)
  simp only [Functor.comp_map, Hom.quotientFunctor_map_val, TwoTermQuotient.comp_val,
    eqToHom_val] at hval ⊢
  simpa using hval


/-! ## Short exact sequences of two-term complexes -/

section ShortExactSequences

variable {K' K K'' : LinearTwoTermComplex R} {i : Hom K' K} {p : Hom K K''}

/-- A degreewise short exact sequence `0 → K' → K → K'' → 0` of two-term complexes.  All six
fields are hypotheses about the two chain maps; no conclusion is stored. -/
structure ShortExact (i : Hom K' K) (p : Hom K K'') : Prop where
  /-- The first map is injective in degree zero. -/
  injective_degreeZero : Function.Injective i.degreeZero
  /-- The first map is injective in degree one. -/
  injective_degreeOne : Function.Injective i.degreeOne
  /-- The second map is surjective in degree zero. -/
  surjective_degreeZero : Function.Surjective p.degreeZero
  /-- The second map is surjective in degree one. -/
  surjective_degreeOne : Function.Surjective p.degreeOne
  /-- Exactness in the middle in degree zero. -/
  exact_degreeZero : LinearMap.ker p.degreeZero = LinearMap.range i.degreeZero
  /-- Exactness in the middle in degree one. -/
  exact_degreeOne : LinearMap.ker p.degreeOne = LinearMap.range i.degreeOne

namespace ShortExact

/-- The composite of the two maps of a short exact sequence vanishes in degree zero. -/
theorem comp_degreeZero (h : ShortExact i p) (x : K'.degreeZero) :
    p.degreeZero (i.degreeZero x) = 0 := by
  have hx : i.degreeZero x ∈ LinearMap.ker p.degreeZero := by
    rw [h.exact_degreeZero]
    exact ⟨x, rfl⟩
  exact hx

/-- The composite of the two maps of a short exact sequence vanishes in degree one. -/
theorem comp_degreeOne (h : ShortExact i p) (x : K'.degreeOne) :
    p.degreeOne (i.degreeOne x) = 0 := by
  have hx : i.degreeOne x ∈ LinearMap.ker p.degreeOne := by
    rw [h.exact_degreeOne]
    exact ⟨x, rfl⟩
  exact hx

/-! ### The connecting homomorphism -/

/-- Every class in `h⁰(K'')` lifts to `K⁰`, and the differential of any lift comes from `K'¹`. -/
theorem exists_delta_lift (h : ShortExact i p) (c : h0 K'') :
    ∃ b : K'.degreeOne, ∃ a : K.degreeZero,
      p.degreeZero a = (c : K''.degreeZero) ∧ i.degreeOne b = K.differential a := by
  obtain ⟨a, ha⟩ := h.surjective_degreeZero (c : K''.degreeZero)
  have hmem : K.differential a ∈ LinearMap.ker p.degreeOne := by
    rw [LinearMap.mem_ker, p.comm, ha]
    exact LinearMap.mem_ker.mp c.2
  rw [h.exact_degreeOne] at hmem
  obtain ⟨b, hb⟩ := hmem
  exact ⟨b, a, ha, hb⟩

/-- The class of the lift in `h¹(K')` does not depend on the chosen lift. -/
theorem delta_well_defined (h : ShortExact i p) {a a₀ : K.degreeZero} {b b₀ : K'.degreeOne}
    (hp : p.degreeZero a = p.degreeZero a₀)
    (hb : i.degreeOne b = K.differential a) (hb₀ : i.degreeOne b₀ = K.differential a₀) :
    h1mk K' b = h1mk K' b₀ := by
  have hmem : a - a₀ ∈ LinearMap.ker p.degreeZero := by
    rw [LinearMap.mem_ker, map_sub, hp, sub_self]
  rw [h.exact_degreeZero] at hmem
  obtain ⟨e, he⟩ := hmem
  have key : i.degreeOne (b - b₀) = i.degreeOne (K'.differential e) := by
    rw [map_sub, hb, hb₀, ← map_sub, ← he]
    exact (i.comm e).symm
  have hbe : b - b₀ = K'.differential e := h.injective_degreeOne key
  rw [Submodule.Quotient.eq]
  exact ⟨e, hbe.symm⟩

/-- The connecting map `h⁰(K'') → h¹(K')` as a function. -/
noncomputable def deltaFun (h : ShortExact i p) (c : h0 K'') : h1 K' :=
  h1mk K' (Classical.choose (h.exists_delta_lift c))

/-- The defining property of the connecting map: it may be computed from any lift. -/
theorem deltaFun_eq (h : ShortExact i p) (c : h0 K'') {a : K.degreeZero} {b : K'.degreeOne}
    (ha : p.degreeZero a = (c : K''.degreeZero)) (hb : i.degreeOne b = K.differential a) :
    deltaFun h c = h1mk K' b := by
  obtain ⟨a₀, ha₀, hb₀⟩ := Classical.choose_spec (h.exists_delta_lift c)
  exact h.delta_well_defined (ha₀.trans ha.symm) hb₀ hb

/-- The connecting homomorphism `δ : h⁰(K'') → h¹(K')` of a short exact sequence of two-term
complexes. -/
noncomputable def delta (h : ShortExact i p) : h0 K'' →ₗ[R] h1 K' where
  toFun := deltaFun h
  map_add' c c' := by
    obtain ⟨b, a, ha, hb⟩ := h.exists_delta_lift c
    obtain ⟨b', a', ha', hb'⟩ := h.exists_delta_lift c'
    rw [deltaFun_eq h c ha hb, deltaFun_eq h c' ha' hb',
      deltaFun_eq h (c + c') (a := a + a') (b := b + b')
        (by rw [map_add, ha, ha']; rfl) (by rw [map_add, hb, hb', map_add])]
    rfl
  map_smul' r c := by
    obtain ⟨b, a, ha, hb⟩ := h.exists_delta_lift c
    rw [deltaFun_eq h c ha hb,
      deltaFun_eq h (r • c) (a := r • a) (b := r • b)
        (by rw [map_smul, ha]; rfl) (by rw [map_smul, hb, map_smul])]
    rfl

@[simp]
theorem delta_apply (h : ShortExact i p) (c : h0 K'') : h.delta c = deltaFun h c :=
  rfl

/-! ### The six-term exact cohomology sequence -/

/-- `h⁰(i)` is injective: exactness at `h⁰(K')`. -/
theorem injective_kernelMap (h : ShortExact i p) : Function.Injective i.kernelMap := by
  intro x y hxy
  apply Subtype.ext
  exact h.injective_degreeZero (congrArg Subtype.val hxy)

/-- Exactness at `h⁰(K)`: the kernel of `h⁰(p)` is the image of `h⁰(i)`. -/
theorem exact_h0_middle (h : ShortExact i p) :
    LinearMap.ker p.kernelMap = LinearMap.range i.kernelMap := by
  apply le_antisymm
  · intro c hc
    have hc0 : p.degreeZero (c : K.degreeZero) = 0 := congrArg Subtype.val hc
    have hmem : (c : K.degreeZero) ∈ LinearMap.range i.degreeZero := by
      rw [← h.exact_degreeZero]
      exact hc0
    obtain ⟨e, he⟩ := hmem
    have hker : e ∈ LinearMap.ker K'.differential := by
      apply h.injective_degreeOne
      rw [i.comm, he, map_zero]
      exact LinearMap.mem_ker.mp c.2
    exact ⟨⟨e, hker⟩, Subtype.ext he⟩
  · rintro _ ⟨e, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    exact h.comp_degreeZero (e : K'.degreeZero)

/-- Exactness at `h⁰(K'')`: the kernel of the connecting map is the image of `h⁰(p)`. -/
theorem exact_h0_right (h : ShortExact i p) :
    LinearMap.ker h.delta = LinearMap.range p.kernelMap := by
  apply le_antisymm
  · intro c hc
    obtain ⟨b, a, ha, hb⟩ := h.exists_delta_lift c
    have hc0 : h1mk K' b = 0 := by
      rw [← deltaFun_eq h c ha hb]
      exact hc
    obtain ⟨e, he⟩ := (h1mk_eq_zero_iff (E := K') b).1 hc0
    have hzero : K.differential (a - i.degreeZero e) = 0 := by
      rw [map_sub, ← i.comm, he, hb, sub_self]
    refine ⟨⟨a - i.degreeZero e, hzero⟩, ?_⟩
    apply Subtype.ext
    change p.degreeZero (a - i.degreeZero e) = (c : K''.degreeZero)
    rw [map_sub, ha, h.comp_degreeZero, sub_zero]
  · rintro _ ⟨c, rfl⟩
    rw [LinearMap.mem_ker]
    have hzero : i.degreeOne 0 = K.differential (c : K.degreeZero) := by
      rw [map_zero, LinearMap.mem_ker.mp c.2]
    rw [delta_apply, deltaFun_eq h _ rfl hzero]
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨0, map_zero _⟩

/-- Exactness at `h¹(K')`: the kernel of `h¹(i)` is the image of the connecting map. -/
theorem exact_h1_left (h : ShortExact i p) :
    LinearMap.ker i.cokernelMap = LinearMap.range h.delta := by
  apply le_antisymm
  · intro q hq
    obtain ⟨b, rfl⟩ := h1mk_surjective q
    have hq0 : h1mk K (i.degreeOne b) = 0 := hq
    obtain ⟨a, ha⟩ := (h1mk_eq_zero_iff (E := K) (i.degreeOne b)).1 hq0
    have hker : p.degreeZero a ∈ LinearMap.ker K''.differential := by
      rw [LinearMap.mem_ker, ← p.comm, ha]
      exact h.comp_degreeOne b
    exact ⟨⟨p.degreeZero a, hker⟩, deltaFun_eq h ⟨p.degreeZero a, hker⟩ rfl ha.symm⟩
  · rintro _ ⟨c, rfl⟩
    obtain ⟨b, a, ha, hb⟩ := h.exists_delta_lift c
    rw [LinearMap.mem_ker, delta_apply, deltaFun_eq h c ha hb]
    change h1mk K (i.degreeOne b) = 0
    rw [h1mk_eq_zero_iff, hb]
    exact ⟨a, rfl⟩

/-- Exactness at `h¹(K)`: the kernel of `h¹(p)` is the image of `h¹(i)`. -/
theorem exact_h1_middle (h : ShortExact i p) :
    LinearMap.ker p.cokernelMap = LinearMap.range i.cokernelMap := by
  apply le_antisymm
  · intro q hq
    obtain ⟨y, rfl⟩ := h1mk_surjective q
    have hq0 : h1mk K'' (p.degreeOne y) = 0 := hq
    obtain ⟨z'', hz''⟩ := (h1mk_eq_zero_iff (E := K'') (p.degreeOne y)).1 hq0
    obtain ⟨z, hz⟩ := h.surjective_degreeZero z''
    have hmem : y - K.differential z ∈ LinearMap.range i.degreeOne := by
      rw [← h.exact_degreeOne, LinearMap.mem_ker, map_sub, p.comm, hz, hz'', sub_self]
    obtain ⟨b, hb⟩ := hmem
    refine ⟨h1mk K' b, ?_⟩
    change h1mk K (i.degreeOne b) = h1mk K y
    rw [hb, Submodule.Quotient.eq]
    exact ⟨-z, by rw [map_neg]; abel⟩
  · rintro _ ⟨q, rfl⟩
    obtain ⟨b, rfl⟩ := h1mk_surjective q
    rw [LinearMap.mem_ker]
    change h1mk K'' (p.degreeOne (i.degreeOne b)) = 0
    rw [h.comp_degreeOne]
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨0, map_zero _⟩

/-- `h¹(p)` is surjective: exactness at `h¹(K'')`. -/
theorem surjective_cokernelMap (h : ShortExact i p) : Function.Surjective p.cokernelMap := by
  intro q
  obtain ⟨y'', rfl⟩ := h1mk_surjective q
  obtain ⟨y, hy⟩ := h.surjective_degreeOne y''
  exact ⟨h1mk K y, by rw [cokernelMap_h1mk, hy]⟩

/-! ### Geometric consequences for the Picard groupoids -/

/-- The quotient functor of the surjection of a short exact sequence is essentially surjective:
every object of `[K''¹/K''⁰]` lifts to `[K¹/K⁰]`. -/
theorem essSurj_quotientFunctor (h : ShortExact i p) : p.quotientFunctor.EssSurj :=
  (essSurj_iff p).2 h.surjective_cokernelMap

/-- Fibres of the induced functor on hom-sets are torsors under `h⁰(K')`: two arrows of
`[K¹/K⁰]` with the same image differ by a unique automorphism coming from `K'`. -/
theorem hom_fibre_torsor (h : ShortExact i p) {x y : K.quotient} (a b : x ⟶ y)
    (hab : p.quotientFunctor.map a = p.quotientFunctor.map b) :
    ∃! e : h0 K', i.degreeZero (e : K'.degreeZero) = a.val - b.val := by
  have hker : a.val - b.val ∈ LinearMap.ker K.differential := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact add_left_cancel (a.translate.trans b.translate.symm)
  have hp : a.val - b.val ∈ LinearMap.ker p.degreeZero := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact congrArg TwoTermQuotient.Hom.val hab
  rw [h.exact_degreeZero] at hp
  obtain ⟨e, he⟩ := hp
  have he' : e ∈ LinearMap.ker K'.differential := by
    apply h.injective_degreeOne
    rw [i.comm, he, map_zero]
    exact LinearMap.mem_ker.mp hker
  refine ⟨⟨e, he'⟩, he, fun e' he'' => ?_⟩
  apply Subtype.ext
  exact h.injective_degreeZero (he''.trans he.symm)

/-- Translation of the Picard groupoid of `K` by an object of the Picard groupoid of `K'`: this
is the action of `[K'¹/K'⁰]` on `[K¹/K⁰]` whose quotient is `[K''¹/K''⁰]`. -/
def translate (i : Hom K' K) (t : K'.degreeOne) : K.quotient ⥤ K.quotient where
  obj x := ⟨x.back + i.degreeOne t⟩
  map {x y} a := ⟨a.val, by
    change x.back + i.degreeOne t + K.differential a.val = y.back + i.degreeOne t
    rw [add_right_comm, a.translate]⟩
  map_id x := by apply TwoTermQuotient.Hom.ext; rfl
  map_comp a b := by apply TwoTermQuotient.Hom.ext; rfl

@[simp]
theorem translate_obj_back (i : Hom K' K) (t : K'.degreeOne) (x : K.quotient) :
    ((translate i t).obj x).back = x.back + i.degreeOne t :=
  rfl

@[simp]
theorem translate_map_val (i : Hom K' K) (t : K'.degreeOne) {x y : K.quotient} (a : x ⟶ y) :
    ((translate i t).map a).val = a.val :=
  rfl

/-- Translating by zero is the identity. -/
theorem translate_zero (i : Hom K' K) : translate i 0 = 𝟭 K.quotient := by
  refine CategoryTheory.Functor.ext (fun x => ?_) (fun x y a => ?_)
  · exact quotient_ext (by simp)
  · apply TwoTermQuotient.Hom.ext
    simp only [Functor.id_map, TwoTermQuotient.comp_val, translate_map_val, eqToHom_val]
    abel

/-- Translations compose. -/
theorem translate_add (i : Hom K' K) (t t' : K'.degreeOne) :
    translate i (t + t') = translate i t ⋙ translate i t' := by
  refine CategoryTheory.Functor.ext (fun x => ?_) (fun x y a => ?_)
  · exact quotient_ext (by simp [add_assoc])
  · apply TwoTermQuotient.Hom.ext
    simp only [Functor.comp_map, TwoTermQuotient.comp_val, translate_map_val, eqToHom_val]
    abel

/-- The comparison arrow exhibiting the projection as invariant under translation. -/
def translateInvarianceHom (h : ShortExact i p) (t : K'.degreeOne) (x : K.quotient) :
    (translate i t ⋙ p.quotientFunctor).obj x ⟶ p.quotientFunctor.obj x where
  val := 0
  translate := by
    change p.degreeOne (x.back + i.degreeOne t) + K''.differential 0 = p.degreeOne x.back
    rw [map_add, h.comp_degreeOne, map_zero, add_zero, add_zero]

@[simp]
theorem translateInvarianceHom_val (h : ShortExact i p) (t : K'.degreeOne) (x : K.quotient) :
    (translateInvarianceHom h t x).val = 0 :=
  rfl

/-- The projection to `[K''¹/K''⁰]` is invariant under the translation action of `K'`. -/
noncomputable def translateInvarianceIso (h : ShortExact i p) (t : K'.degreeOne) :
    translate i t ⋙ p.quotientFunctor ≅ p.quotientFunctor :=
  NatIso.ofComponents (fun x => asIso (translateInvarianceHom h t x))
    (fun {x y} a => by
      apply TwoTermQuotient.Hom.ext
      simp)

/-- Fibres of the induced map on isomorphism classes are exactly the orbits of the translation
action of `[K'¹/K'⁰]`: two objects of `[K¹/K⁰]` have isomorphic images in `[K''¹/K''⁰]` exactly
when one is isomorphic to a translate of the other. -/
theorem nonempty_iso_map_iff (h : ShortExact i p) (x y : K.quotient) :
    Nonempty (p.quotientFunctor.obj x ≅ p.quotientFunctor.obj y) ↔
      ∃ t : K'.degreeOne, Nonempty (x ≅ (translate i t).obj y) := by
  constructor
  · intro hiso
    have hcl : p.cokernelMap (isoClass x) = p.cokernelMap (isoClass y) := by
      rw [← isoClass_map, ← isoClass_map]
      exact (isoClass_eq_iff _ _).2 hiso
    have hmem : isoClass x - isoClass y ∈ LinearMap.ker p.cokernelMap := by
      rw [LinearMap.mem_ker, map_sub, hcl, sub_self]
    rw [h.exact_h1_middle] at hmem
    obtain ⟨q, hq⟩ := hmem
    obtain ⟨t, rfl⟩ := h1mk_surjective q
    refine ⟨t, (isoClass_eq_iff _ _).1 ?_⟩
    have hthis : h1mk K (i.degreeOne t) = isoClass x - isoClass y := hq
    change isoClass x = h1mk K (y.back + i.degreeOne t)
    rw [h1mk_add, hthis]
    change isoClass x = isoClass y + (isoClass x - isoClass y)
    abel
  · rintro ⟨t, hiso⟩
    refine (isoClass_eq_iff _ _).1 ?_
    rw [isoClass_map, isoClass_map]
    have hx : isoClass x = isoClass ((translate i t).obj y) := (isoClass_eq_iff _ _).2 hiso
    rw [hx]
    change p.cokernelMap (h1mk K (y.back + i.degreeOne t)) = p.cokernelMap (isoClass y)
    rw [h1mk_add, map_add, cokernelMap_h1mk, cokernelMap_h1mk, h.comp_degreeOne, h1mk_zero,
      add_zero]
    rfl

/-! ### Acyclic quotients -/

/-- If the quotient complex is acyclic then the inclusion is a quasi-isomorphism, hence induces
an equivalence of Picard groupoids.  This is the two-term form of "a distinguished triangle with
zero third term is an isomorphism". -/
theorem isQuasiIsomorphism_of_acyclic (h : ShortExact i p)
    (hzero : ∀ c : h0 K'', c = 0) (hone : ∀ q : h1 K'', q = 0) :
    i.IsQuasiIsomorphism := by
  refine ⟨⟨h.injective_kernelMap, ?_⟩, ?_, ?_⟩
  · intro c
    have hmem : c ∈ LinearMap.ker p.kernelMap := by
      rw [LinearMap.mem_ker]
      exact hzero _
    rw [h.exact_h0_middle] at hmem
    exact hmem
  · intro q q' hqq'
    have hsub : q - q' ∈ LinearMap.ker i.cokernelMap := by
      rw [LinearMap.mem_ker, map_sub, hqq', sub_self]
    rw [h.exact_h1_left] at hsub
    obtain ⟨c, hc⟩ := hsub
    rw [hzero c] at hc
    rw [← sub_eq_zero, ← hc, map_zero]
  · intro q
    have hmem : q ∈ LinearMap.ker p.cokernelMap := by
      rw [LinearMap.mem_ker]
      exact hone _
    rw [h.exact_h1_middle] at hmem
    exact hmem

/-- The equivalence of Picard groupoids attached to a short exact sequence with acyclic
quotient. -/
noncomputable def quotientEquivalenceOfAcyclic (h : ShortExact i p)
    (hzero : ∀ c : h0 K'', c = 0) (hone : ∀ q : h1 K'', q = 0) :
    K'.quotient ≌ K.quotient :=
  (h.isQuasiIsomorphism_of_acyclic hzero hone).quotientEquivalence

end ShortExact

end ShortExactSequences

end PicardCriteria

end GromovWitten.AlgebraicGeometry
