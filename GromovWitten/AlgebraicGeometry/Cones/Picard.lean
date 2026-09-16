/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Cones.TwoTermQuotient
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# The Picard groupoid of a two-term linear complex

A complex `E⁰ ⟶ E¹` determines the translation groupoid `[E¹/E⁰]`.  This file proves the
functorial and homotopical part of the `h¹/h⁰` construction: chain maps induce functors, chain
homotopies induce specified natural isomorphisms, and a chain-homotopy equivalence induces an
equivalence of quotient groupoids.  Automorphisms are retained throughout.
-/

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace GromovWitten.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R]

/-- A two-term complex of `R`-modules, displayed in degrees zero and one. -/
structure LinearTwoTermComplex where
  degreeZero : Type u
  degreeOne : Type u
  [degreeZero_add : AddCommGroup degreeZero]
  [degreeOne_add : AddCommGroup degreeOne]
  [degreeZero_module : Module R degreeZero]
  [degreeOne_module : Module R degreeOne]
  differential : degreeZero →ₗ[R] degreeOne

attribute [instance] LinearTwoTermComplex.degreeZero_add
  LinearTwoTermComplex.degreeOne_add LinearTwoTermComplex.degreeZero_module
  LinearTwoTermComplex.degreeOne_module

namespace LinearTwoTermComplex

variable {R}

/-- The cohomological dual of a two-term complex.  If `E` is displayed in degrees `-1,0`,
then `E.dual` is displayed in degrees `0,1`: the terms are reversed and the differential is
the transpose.  Its quotient is the fibrewise model for `h¹/h⁰(Eᵛ)`. -/
def dual (E : LinearTwoTermComplex R) : LinearTwoTermComplex R where
  degreeZero := Module.Dual R E.degreeOne
  degreeOne := Module.Dual R E.degreeZero
  differential := E.differential.dualMap

@[simp]
theorem dual_differential (E : LinearTwoTermComplex R) :
    E.dual.differential = E.differential.dualMap :=
  rfl

/-- The dual of a proved-zero module is again proved zero. -/
theorem dual_subsingleton {M : Type u} [AddCommGroup M] [Module R M]
    [Subsingleton M] : Subsingleton (Module.Dual R M) := by
  constructor
  intro f g
  apply LinearMap.ext
  intro x
  rw [Subsingleton.elim x 0]
  simp

/-! ## Realization as a cochain complex -/

/-- The graded object underlying the cochain realization of a two-term linear complex.

The source of the displayed differential is placed in cohomological degree `-1` and its target
in degree `0`.  Every other degree is the categorical zero module. -/
noncomputable def cochainObject (E : LinearTwoTermComplex R) (i : ℤ) : ModuleCat.{u} R :=
  if i = -1 then ModuleCat.of R E.degreeZero
  else if i = 0 then ModuleCat.of R E.degreeOne
  else 0

/-- The differential of the cochain realization.  It is the displayed linear differential in
degree `-1` and zero in every other degree. -/
noncomputable def cochainDifferential (E : LinearTwoTermComplex R) (i : ℤ) :
    cochainObject E i ⟶ cochainObject E (i + 1) := by
  by_cases hi : i = -1
  · subst i
    simpa [cochainObject] using ModuleCat.ofHom E.differential
  · exact 0

/-- A two-term linear complex as an honest cochain complex of modules, supported in degrees
`-1` and `0`.  The square-zero law is proved from the support: the only potentially nonzero
differential is followed by zero. -/
noncomputable def toCochainComplex (E : LinearTwoTermComplex R) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.of (cochainObject E) (cochainDifferential E) (by
    intro i
    by_cases hi : i = -1
    · subst i
      simp [cochainDifferential]
    · simp [cochainDifferential, hi])

@[simp]
theorem toCochainComplex_X_negOne (E : LinearTwoTermComplex R) :
    E.toCochainComplex.X (-1) = ModuleCat.of R E.degreeZero := by
  rfl

@[simp]
theorem toCochainComplex_X_zero (E : LinearTwoTermComplex R) :
    E.toCochainComplex.X 0 = ModuleCat.of R E.degreeOne := by
  rfl

/-- Terms outside the displayed two degrees are genuine zero objects. -/
theorem toCochainComplex_X_isZero (E : LinearTwoTermComplex R) (i : ℤ)
    (hiNeg : i ≠ -1) (hiZero : i ≠ 0) :
    CategoryTheory.Limits.IsZero (E.toCochainComplex.X i) := by
  change CategoryTheory.Limits.IsZero (cochainObject E i)
  rw [cochainObject, if_neg hiNeg, if_neg hiZero]
  exact CategoryTheory.Limits.isZero_zero _

/-- The cochain differential from degree `-1` to degree `0` is exactly the linear differential
with which the two-term complex was defined. -/
@[simp]
theorem toCochainComplex_d_negOne_zero (E : LinearTwoTermComplex R) :
    E.toCochainComplex.d (-1) 0 = ModuleCat.ofHom E.differential := by
  apply ModuleCat.hom_ext
  rfl

/-- The Picard groupoid `h¹/h⁰(E)=[E¹/E⁰]` of a two-term complex. -/
abbrev quotient (E : LinearTwoTermComplex R) :=
  TwoTermQuotient R E.degreeZero E.degreeOne E.differential

/-- A chain map between two-term complexes. -/
structure Hom (E F : LinearTwoTermComplex R) where
  degreeZero : E.degreeZero →ₗ[R] F.degreeZero
  degreeOne : E.degreeOne →ₗ[R] F.degreeOne
  comm (x : E.degreeZero) :
    degreeOne (E.differential x) = F.differential (degreeZero x)

namespace Hom

variable {E F G : LinearTwoTermComplex R}

/-- Identity chain map. -/
def id (E : LinearTwoTermComplex R) : Hom E E where
  degreeZero := LinearMap.id
  degreeOne := LinearMap.id
  comm _ := rfl

/-- Composition of chain maps. -/
def comp (g : Hom F G) (f : Hom E F) : Hom E G where
  degreeZero := g.degreeZero.comp f.degreeZero
  degreeOne := g.degreeOne.comp f.degreeOne
  comm x := by rw [LinearMap.comp_apply, LinearMap.comp_apply, f.comm, g.comm]

/-- A chain map induces a functor on translation quotient groupoids. -/
def quotientFunctor (f : Hom E F) : E.quotient ⥤ F.quotient where
  obj x := ⟨f.degreeOne x.back⟩
  map {x y} a := ⟨f.degreeZero a.val, by
    change f.degreeOne x.back + F.differential (f.degreeZero a.val) = f.degreeOne y.back
    rw [← f.comm, ← map_add, a.translate]⟩
  map_id x := by
    apply TwoTermQuotient.Hom.ext
    change f.degreeZero 0 = 0
    exact map_zero _
  map_comp a b := by
    apply TwoTermQuotient.Hom.ext
    change f.degreeZero (a.val + b.val) = f.degreeZero a.val + f.degreeZero b.val
    exact f.degreeZero.map_add a.val b.val

@[simp]
theorem quotientFunctor_obj_back (f : Hom E F) (x : E.quotient) :
    (f.quotientFunctor.obj x).back = f.degreeOne x.back :=
  rfl

@[simp]
theorem quotientFunctor_map_val (f : Hom E F) {x y : E.quotient} (a : x ⟶ y) :
    (f.quotientFunctor.map a).val = f.degreeZero a.val :=
  rfl

@[simp]
theorem quotientFunctor_id (E : LinearTwoTermComplex R) :
    (id E).quotientFunctor = 𝟭 E.quotient :=
  rfl

@[simp]
theorem quotientFunctor_comp (g : Hom F G) (f : Hom E F) :
    (g.comp f).quotientFunctor = f.quotientFunctor ⋙ g.quotientFunctor :=
  rfl

/-- Injectivity in degree zero makes the induced quotient functor faithful. -/
theorem quotientFunctorFaithful (f : Hom E F) (hf : Function.Injective f.degreeZero) :
    f.quotientFunctor.Faithful where
  map_injective {x y} a b h := by
    apply TwoTermQuotient.Hom.ext
    apply hf
    exact congrArg TwoTermQuotient.Hom.val h

/-- The explicit arrow-lifting condition on a two-term chain map.

This is the elementwise pullback condition for the square of differentials. -/
def HasTranslationLifting (f : Hom E F) : Prop :=
  ∀ (x y : E.degreeOne) (a : F.degreeZero),
    f.degreeOne x + F.differential a = f.degreeOne y →
      ∃ b : E.degreeZero, f.degreeZero b = a ∧ x + E.differential b = y

/-- The translation-lifting condition makes the quotient functor full. -/
theorem quotientFunctorFull (f : Hom E F) (hf : f.HasTranslationLifting) :
    f.quotientFunctor.Full where
  map_surjective {x y} a := by
    obtain ⟨b, hb, htranslate⟩ := hf x.back y.back a.val a.translate
    refine ⟨⟨b, htranslate⟩, ?_⟩
    apply TwoTermQuotient.Hom.ext
    exact hb

/-- Surjectivity on the cokernel, written without collapsing the quotient groupoids to sets. -/
def SurjectiveOnCokernels (f : Hom E F) : Prop :=
  ∀ y : F.degreeOne, ∃ x : E.degreeOne,
    y - f.degreeOne x ∈ LinearMap.range F.differential

/-- Surjectivity on cokernels makes the quotient functor essentially surjective. -/
theorem quotientFunctorEssSurj (f : Hom E F) (hf : f.SurjectiveOnCokernels) :
    f.quotientFunctor.EssSurj where
  mem_essImage y := by
    obtain ⟨x, hx⟩ := hf y.back
    let x' : E.quotient := ⟨x⟩
    obtain ⟨e⟩ := (TwoTermQuotient.nonempty_iso_iff F.differential
      (f.quotientFunctor.obj x') y).2 hx
    exact ⟨x', ⟨e⟩⟩

/-- The map induced by a chain map on degree-zero cohomology, the kernel of the differential. -/
def kernelMap (f : Hom E F) :
    LinearMap.ker E.differential →ₗ[R] LinearMap.ker F.differential where
  toFun x := ⟨f.degreeZero x, by
    rw [LinearMap.mem_ker, ← f.comm, LinearMap.mem_ker.mp x.property, map_zero]⟩
  map_add' x y := by ext; exact f.degreeZero.map_add x y
  map_smul' r x := by ext; exact f.degreeZero.map_smul r x

/-- The map induced by a chain map on degree-one cohomology, the cokernel of the differential. -/
def cokernelMap (f : Hom E F) :
    (E.degreeOne ⧸ (LinearMap.range E.differential : Submodule R E.degreeOne)) →ₗ[R]
      (F.degreeOne ⧸ (LinearMap.range F.differential : Submodule R F.degreeOne)) :=
  Submodule.mapQ (LinearMap.range E.differential) (LinearMap.range F.differential)
    f.degreeOne (by
      rintro _ ⟨x, rfl⟩
      exact ⟨f.degreeZero x, (f.comm x).symm⟩)

@[simp]
theorem kernelMap_id (E : LinearTwoTermComplex R) :
    (id E).kernelMap = LinearMap.id := by
  ext x
  rfl

@[simp]
theorem kernelMap_comp (g : Hom F G) (f : Hom E F) :
    (g.comp f).kernelMap = g.kernelMap.comp f.kernelMap := by
  ext x
  rfl

@[simp]
theorem cokernelMap_id (E : LinearTwoTermComplex R) :
    (id E).cokernelMap = LinearMap.id := by
  ext x
  rfl

@[simp]
theorem cokernelMap_comp (g : Hom F G) (f : Hom E F) :
    (g.comp f).cokernelMap = g.cokernelMap.comp f.cokernelMap := by
  ext x
  rfl

/-- A quasi-isomorphism of two-term complexes is a chain map inducing bijections on the kernel
and cokernel of the differential. -/
def IsQuasiIsomorphism (f : Hom E F) : Prop :=
  Function.Bijective f.kernelMap ∧ Function.Bijective f.cokernelMap

namespace IsQuasiIsomorphism

variable {f : Hom E F}

/-- The identity chain map is a quasi-isomorphism. -/
theorem id (E : LinearTwoTermComplex R) : (Hom.id E).IsQuasiIsomorphism := by
  constructor
  · rw [kernelMap_id]
    exact Function.bijective_id
  · rw [cokernelMap_id]
    exact Function.bijective_id

/-- A composite of quasi-isomorphisms is a quasi-isomorphism. -/
theorem comp {g : Hom F G} (hg : g.IsQuasiIsomorphism) (hf : f.IsQuasiIsomorphism) :
    (g.comp f).IsQuasiIsomorphism := by
  constructor
  · rw [kernelMap_comp]
    exact hg.1.comp hf.1
  · rw [cokernelMap_comp]
    exact hg.2.comp hf.2

/-- A quasi-isomorphism induces a faithful functor on Picard groupoids. -/
theorem quotientFunctorFaithful (hf : f.IsQuasiIsomorphism) :
    f.quotientFunctor.Faithful where
  map_injective {x y} a b hab := by
    apply TwoTermQuotient.Hom.ext
    let d : LinearMap.ker E.differential := ⟨a.val - b.val, by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact add_left_cancel (a.translate.trans b.translate.symm)⟩
    have hd : f.kernelMap d = 0 := by
      apply Subtype.ext
      change f.degreeZero (a.val - b.val) = 0
      rw [map_sub, sub_eq_zero]
      exact congrArg TwoTermQuotient.Hom.val hab
    have : d = 0 := hf.1.1 (by simpa using hd)
    exact sub_eq_zero.mp (congrArg Subtype.val this)

/-- A quasi-isomorphism induces a full functor on Picard groupoids. -/
theorem quotientFunctorFull (hf : f.IsQuasiIsomorphism) :
    f.quotientFunctor.Full where
  map_surjective {x y} a := by
    let q : E.degreeOne ⧸ (LinearMap.range E.differential : Submodule R E.degreeOne) :=
      Submodule.Quotient.mk (y.back - x.back)
    have hq : f.cokernelMap q = 0 := by
      change Submodule.Quotient.mk (f.degreeOne (y.back - x.back)) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      refine ⟨a.val, ?_⟩
      change F.differential a.val = f.degreeOne (y.back - x.back)
      have ha := a.translate
      dsimp [Hom.quotientFunctor] at ha
      rw [map_sub]
      exact eq_sub_of_add_eq' ha
    have hq0 : q = 0 := hf.2.1 (by simpa using hq)
    have hRange : y.back - x.back ∈ LinearMap.range E.differential := by
      rw [← Submodule.Quotient.mk_eq_zero]
      exact hq0
    obtain ⟨b₀, hb₀⟩ := hRange
    let d : LinearMap.ker F.differential :=
      ⟨a.val - f.degreeZero b₀, by
        rw [LinearMap.mem_ker, map_sub, ← f.comm, hb₀, sub_eq_zero]
        have ha := a.translate
        dsimp [Hom.quotientFunctor] at ha
        rw [map_sub]
        exact eq_sub_of_add_eq' ha⟩
    obtain ⟨c, hc⟩ := hf.1.2 d
    let b : E.degreeZero := b₀ + c.1
    refine ⟨⟨b, ?_⟩, ?_⟩
    · dsimp [b]
      rw [map_add, LinearMap.mem_ker.mp c.property, add_zero, hb₀]
      abel
    · apply TwoTermQuotient.Hom.ext
      change f.degreeZero b = a.val
      have hc' := congrArg Subtype.val hc
      change f.degreeZero c.1 = a.val - f.degreeZero b₀ at hc'
      dsimp [b]
      rw [map_add, hc']
      abel

/-- A quasi-isomorphism is essentially surjective on Picard groupoids. -/
theorem quotientFunctorEssSurj (hf : f.IsQuasiIsomorphism) :
    f.quotientFunctor.EssSurj := by
  apply Hom.quotientFunctorEssSurj f
  intro y
  obtain ⟨q, hq⟩ := hf.2.2 (Submodule.Quotient.mk y)
  obtain ⟨x⟩ := q
  refine ⟨x, ?_⟩
  have heq :
      Submodule.Quotient.mk (f.degreeOne x) =
        (Submodule.Quotient.mk y :
          F.degreeOne ⧸ (LinearMap.range F.differential : Submodule R F.degreeOne)) := by
    change Submodule.Quotient.mk (f.degreeOne x) =
      (Submodule.Quotient.mk y :
        F.degreeOne ⧸ (LinearMap.range F.differential : Submodule R F.degreeOne)) at hq
    exact hq
  rw [Submodule.Quotient.eq] at heq
  simpa only [neg_sub] using
    (LinearMap.range F.differential).neg_mem heq

/-- Every quasi-isomorphism of two-term complexes induces an equivalence of their Picard
groupoids. -/
noncomputable def quotientEquivalence (hf : f.IsQuasiIsomorphism) :
    E.quotient ≌ F.quotient := by
  letI : f.quotientFunctor.Faithful := hf.quotientFunctorFaithful
  letI : f.quotientFunctor.Full := hf.quotientFunctorFull
  letI : f.quotientFunctor.EssSurj := hf.quotientFunctorEssSurj
  letI : f.quotientFunctor.IsEquivalence := { }
  exact f.quotientFunctor.asEquivalence

end IsQuasiIsomorphism

end Hom

/-- A chain homotopy from `f` to `g`.

With the displayed convention, `g-f = d h + h d`; this makes `h(x)` the translation arrow from
`f¹(x)` to `g¹(x)` in the quotient groupoid. -/
structure ChainHomotopy {E F : LinearTwoTermComplex R} (f g : Hom E F) where
  homotopy : E.degreeOne →ₗ[R] F.degreeZero
  degreeZero (x : E.degreeZero) :
    g.degreeZero x = f.degreeZero x + homotopy (E.differential x)
  degreeOne (x : E.degreeOne) :
    g.degreeOne x = f.degreeOne x + F.differential (homotopy x)

namespace ChainHomotopy

variable {E F : LinearTwoTermComplex R} {f g : Hom E F}

/-- The natural transformation induced by a chain homotopy. -/
def natTrans (H : ChainHomotopy f g) : f.quotientFunctor ⟶ g.quotientFunctor where
  app x := ⟨H.homotopy x.back, (H.degreeOne x.back).symm⟩
  naturality {x y} a := by
    apply TwoTermQuotient.Hom.ext
    change f.degreeZero a.val + H.homotopy y.back =
      H.homotopy x.back + g.degreeZero a.val
    rw [← a.translate, map_add, H.degreeZero]
    abel

/-- A chain homotopy induces a specified natural isomorphism of quotient functors. -/
noncomputable def natIso (H : ChainHomotopy f g) : f.quotientFunctor ≅ g.quotientFunctor :=
  NatIso.ofComponents (fun x ↦ asIso (H.natTrans.app x))
    (fun {_ _} a ↦ by
      dsimp
      exact H.natTrans.naturality a)

@[simp]
theorem natIso_hom_app_val (H : ChainHomotopy f g) (x : E.quotient) :
    (H.natIso.hom.app x).val = H.homotopy x.back :=
  by simp [natIso, natTrans]

/-- Chain-homotopic maps induce the same map on degree-zero cohomology. -/
theorem kernelMap_eq (H : ChainHomotopy f g) : f.kernelMap = g.kernelMap := by
  ext x
  change f.degreeZero x = g.degreeZero x
  rw [H.degreeZero]
  rw [LinearMap.mem_ker.mp x.property, map_zero, add_zero]

/-- Chain-homotopic maps induce the same map on degree-one cohomology. -/
theorem cokernelMap_eq (H : ChainHomotopy f g) : f.cokernelMap = g.cokernelMap := by
  ext x
  change Submodule.Quotient.mk (f.degreeOne x) =
    Submodule.Quotient.mk (g.degreeOne x)
  rw [Submodule.Quotient.eq]
  rw [H.degreeOne]
  refine ⟨-H.homotopy x, ?_⟩
  simp

end ChainHomotopy

/-- A chain-homotopy equivalence of two-term complexes. -/
structure HomotopyEquivalence (E F : LinearTwoTermComplex R) where
  hom : Hom E F
  inv : Hom F E
  unit : ChainHomotopy (Hom.id E) (inv.comp hom)
  counit : ChainHomotopy (hom.comp inv) (Hom.id F)

namespace HomotopyEquivalence

variable {E F : LinearTwoTermComplex R}

/-- A chain-homotopy equivalence is a quasi-isomorphism. -/
theorem isQuasiIsomorphism (e : HomotopyEquivalence E F) :
    e.hom.IsQuasiIsomorphism := by
  have unitKernel : e.inv.kernelMap.comp e.hom.kernelMap = LinearMap.id := by
    rw [← Hom.kernelMap_comp, ← e.unit.kernelMap_eq, Hom.kernelMap_id]
  have counitKernel : e.hom.kernelMap.comp e.inv.kernelMap = LinearMap.id := by
    rw [← Hom.kernelMap_comp, e.counit.kernelMap_eq, Hom.kernelMap_id]
  have unitCokernel : e.inv.cokernelMap.comp e.hom.cokernelMap = LinearMap.id := by
    rw [← Hom.cokernelMap_comp, ← e.unit.cokernelMap_eq, Hom.cokernelMap_id]
  have counitCokernel : e.hom.cokernelMap.comp e.inv.cokernelMap = LinearMap.id := by
    rw [← Hom.cokernelMap_comp, e.counit.cokernelMap_eq, Hom.cokernelMap_id]
  constructor
  · constructor
    · intro x y hxy
      have := congrArg e.inv.kernelMap hxy
      simpa only [← LinearMap.comp_apply, unitKernel, LinearMap.id_apply] using this
    · intro y
      refine ⟨e.inv.kernelMap y, ?_⟩
      have := DFunLike.congr_fun counitKernel y
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using this
  · constructor
    · intro x y hxy
      have := congrArg e.inv.cokernelMap hxy
      simpa only [← LinearMap.comp_apply, unitCokernel, LinearMap.id_apply] using this
    · intro y
      refine ⟨e.inv.cokernelMap y, ?_⟩
      have := DFunLike.congr_fun counitCokernel y
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using this

/-- A chain-homotopy equivalence induces an equivalence of Picard groupoids. -/
noncomputable def quotientEquivalence (e : HomotopyEquivalence E F) : E.quotient ≌ F.quotient :=
  CategoryTheory.Equivalence.mk e.hom.quotientFunctor e.inv.quotientFunctor
    (by simpa using e.unit.natIso)
    (by simpa using e.counit.natIso)

end HomotopyEquivalence

/-! ## Adding a contractible two-term summand -/

namespace AcyclicSummand

variable (E : LinearTwoTermComplex R)
  (K : Type u) [AddCommGroup K] [Module R K]

/-- Adjoin the contractible complex `[K → K]` with identity differential. -/
abbrev add : LinearTwoTermComplex R where
  degreeZero := E.degreeZero × K
  degreeOne := E.degreeOne × K
  differential :=
    { toFun := fun x ↦ (E.differential x.1, x.2)
      map_add' := by
        intro x y
        ext <;> simp
      map_smul' := by
        intro r x
        ext <;> simp }

/-- Include a complex into its sum with `[K ≃ K]`. -/
def inclusion : LinearTwoTermComplex.Hom E (add E K) where
  degreeZero :=
    { toFun := fun x ↦ (x, 0)
      map_add' := by
        intro x y
        change (x + y, 0) = (x, 0) + (y, 0)
        simp
      map_smul' := by
        intro r x
        change (r • x, 0) = r • (x, 0)
        simp }
  degreeOne :=
    { toFun := fun x ↦ (x, 0)
      map_add' := by
        intro x y
        change (x + y, 0) = (x, 0) + (y, 0)
        simp
      map_smul' := by
        intro r x
        change (r • x, 0) = r • (x, 0)
        simp }
  comm _ := rfl

/-- Project away the contractible summand. -/
def projection : LinearTwoTermComplex.Hom (add E K) E where
  degreeZero :=
    { toFun := Prod.fst
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  degreeOne :=
    { toFun := Prod.fst
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  comm _ := rfl

/-- Projection followed by inclusion is chain-homotopic to the identity, with zero homotopy. -/
def unitHomotopy : LinearTwoTermComplex.ChainHomotopy
    (LinearTwoTermComplex.Hom.id E) ((projection E K).comp (inclusion E K)) where
  homotopy := 0
  degreeZero x := by
    dsimp [projection, inclusion, LinearTwoTermComplex.Hom.comp,
      LinearTwoTermComplex.Hom.id]
    simp
  degreeOne x := by
    dsimp [projection, inclusion, LinearTwoTermComplex.Hom.comp,
      LinearTwoTermComplex.Hom.id]
    simp

/-- The identity on the enlarged complex contracts the extra `[K ≃ K]` summand. -/
def counitHomotopy : LinearTwoTermComplex.ChainHomotopy
    ((inclusion E K).comp (projection E K))
    (LinearTwoTermComplex.Hom.id (add E K)) where
  homotopy :=
    { toFun := fun x ↦ (0, x.2)
      map_add' := by
        intro x y
        change (0, (x + y).2) = (0, x.2) + (0, y.2)
        simp
      map_smul' := by
        intro r x
        change (0, (r • x).2) = r • (0, x.2)
        simp }
  degreeZero x := by
    dsimp [add, projection, inclusion, LinearTwoTermComplex.Hom.comp,
      LinearTwoTermComplex.Hom.id]
    exact Prod.ext (by simp) (by simp)
  degreeOne x := by
    dsimp [add, projection, inclusion, LinearTwoTermComplex.Hom.comp,
      LinearTwoTermComplex.Hom.id]
    exact Prod.ext (by simp) (by simp)

/-- Adding the acyclic summand `[K ≃ K]` is a chain-homotopy equivalence. -/
def homotopyEquivalence : LinearTwoTermComplex.HomotopyEquivalence E (add E K) where
  hom := inclusion E K
  inv := projection E K
  unit := unitHomotopy E K
  counit := counitHomotopy E K

/-- The inclusion after adjoining `[K ≃ K]` is a quasi-isomorphism. -/
theorem inclusion_isQuasiIsomorphism :
    (inclusion E K).IsQuasiIsomorphism :=
  (homotopyEquivalence E K).isQuasiIsomorphism

/-- Adding `[K ≃ K]` does not change the Picard quotient groupoid. -/
noncomputable def quotientEquivalence : E.quotient ≌ (add E K).quotient :=
  (homotopyEquivalence E K).quotientEquivalence

end AcyclicSummand

/-- Concrete two-term quasi-isomorphism criterion used by quotient presentations.  The first two
conditions say that arrows lift uniquely; the third is surjectivity on isomorphism classes. -/
structure QuotientEquivalenceCriterion {E F : LinearTwoTermComplex R} (f : Hom E F) : Prop where
  degreeZero_injective : Function.Injective f.degreeZero
  translation_lifting : f.HasTranslationLifting
  cokernel_surjective : f.SurjectiveOnCokernels

namespace QuotientEquivalenceCriterion

variable {E F : LinearTwoTermComplex R} {f : Hom E F}

/-- A chain map satisfying the cartesian-arrow and cokernel criteria induces an equivalence of
Picard groupoids. -/
noncomputable def quotientEquivalence (h : QuotientEquivalenceCriterion f) :
    E.quotient ≌ F.quotient := by
  letI : f.quotientFunctor.Faithful := Hom.quotientFunctorFaithful f h.degreeZero_injective
  letI : f.quotientFunctor.Full := Hom.quotientFunctorFull f h.translation_lifting
  letI : f.quotientFunctor.EssSurj := Hom.quotientFunctorEssSurj f h.cokernel_surjective
  letI : f.quotientFunctor.IsEquivalence := { }
  exact f.quotientFunctor.asEquivalence

end QuotientEquivalenceCriterion

end LinearTwoTermComplex

end GromovWitten.AlgebraicGeometry
