/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import GromovWitten.AlgebraicGeometry.Curves.ArithmeticGenus
import GromovWitten.AlgebraicGeometry.Curves.ArithmeticGenusNormalization
import GromovWitten.AlgebraicGeometry.Curves.ModuleExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# The long exact cohomology sequence for a short exact sequence of `𝒪_X`-modules

`Curves/ArithmeticGenus.lean` constructs `Hⁿ(X, M) = cohomology X M n` as Mathlib's `Ext`-theoretic
sheaf cohomology `CategoryTheory.Sheaf.H` of the underlying abelian sheaf of an `𝒪_X`-module `M`.
This file supplies the long exact cohomology sequence attached to a short exact sequence
`S : ShortComplex X.Modules`, using Mathlib's covariant long exact `Ext` sequence
(`Abelian.Ext.covariant_sequence_exact₁/₂/₃` from
`Mathlib/Algebra/Homology/DerivedCategory/Ext/ExactSequences.lean`) with the *first* argument
fixed at the constant sheaf `ULift ℤ`, since `Sheaf.H F n = Ext (constantSheaf J AddCommGrpCat
(ULift ℤ)) F n`.

## Main declarations

* `moduleToSheafAb_map_shortExact` — the underlying short complex of abelian sheaves of a short
  exact sequence of `𝒪_X`-modules is short exact.
* `cohomologyConnectingHom` — the connecting homomorphism `δ : Hⁿ(X, S.X₃) →+ Hⁿ⁺¹(X, S.X₁)`.
* `cohomology_exact_at_X₂`, `cohomology_exact_at_X₃`, `cohomology_exact_at_X₁` — exactness of the
  long exact sequence at every term, as function-level exactness (`Function.Exact`).
* `cohomology_zero_injective` — `H⁰(X, S.X₁) → H⁰(X, S.X₂)` is injective.
* `cohomologyConnectingHom_smul`, `cohomologyConnectingHomLinear`,
  `cohomologyConnectingHomBaseLinear` — the connecting homomorphism commutes with multiplication by
  a global function, hence is `Γ(X, 𝒪_X)`-linear and, for a `k`-scheme structure on `X`, `k`-linear.
* `eulerCharacteristic_add_of_shortExact` — `χ(X, S.X₂) = χ(X, S.X₁) + χ(X, S.X₃)` (as `h⁰ - h¹`),
  given finite-dimensionality of the six spaces involved and vanishing of `H²(X, S.X₁)`.

## Exactness of the forgetful functor to abelian sheaves

Up to the definitional identification `TopCat.Sheaf Ab X = CategoryTheory.Sheaf
(Opens.grothendieckTopology X) AddCommGrpCat`, `moduleToSheafAb X` is Mathlib's forgetful functor
`SheafOfModules.toSheaf X.ringCatSheaf`.  That it preserves finite limits is a Mathlib instance
(`Mathlib/Algebra/Category/ModuleCat/Sheaf/Limits.lean`), which gives the monomorphism half and
middle-exactness of `moduleToSheafAb_map_shortExact`.  Mathlib has no
`PreservesFiniteColimits (SheafOfModules.toSheaf R)`, so the epimorphism half is proved here
(`preservesEpimorphisms_toSheaf`) from the general criterion
`preservesEpimorphisms_of_reflection`: if `L : A ⥤ B` is a reflector with fully faithful right
adjoint (a natural isomorphism `ι ⋙ L ≅ 𝟭 B`) preserving monomorphisms, and `T : B ⥤ D` is such
that `L ⋙ T` preserves epimorphisms, then `T` preserves epimorphisms.  For sheaves of modules `L`
is `PresheafOfModules.sheafification (𝟙 R.obj)`, `ι` is the inclusion of sheaves into presheaves
of modules, and `L ⋙ SheafOfModules.toSheaf R` is *definitionally*
`PresheafOfModules.toPresheaf R.obj ⋙ presheafToSheaf J AddCommGrpCat`, a composite of two
colimit-preserving functors.

## The remaining hypotheses

`eulerCharacteristic_add_of_shortExact` keeps as explicit hypotheses the finite-dimensionality of
the six cohomology spaces and the vanishing of `H²(X, S.X₁)`; both are genuine Mathlib gaps
(coherence and properness are not available for `Sheaf.H`), and only the degree-`2` vanishing for
`S.X₁` is needed, not vanishing in all degrees `≥ 2`.
-/

open CategoryTheory Limits Abelian
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe w v' u' u

noncomputable section

variable {X : Scheme.{u}}

/-! ## Mono and middle-exactness -/

/-- For **any** short exact sequence `S` of `𝒪_X`-modules, the image short complex of underlying
abelian sheaves is exact in the middle and `(moduleToSheafAb X).map S.f` is a monomorphism.  This
uses only that `moduleToSheafAb X` preserves finite limits; the epimorphism half, which needs
`moduleToSheafAb_preservesEpimorphisms`, is added in `moduleToSheafAb_map_shortExact` below. -/
theorem moduleToSheafAb_map_exact_and_mono (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (moduleToSheafAb X)).Exact ∧ Mono ((moduleToSheafAb X).map S.f) :=
  (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono (moduleToSheafAb X)).1
    inferInstance S hS

/-! ## The forgetful functor to abelian sheaves preserves epimorphisms -/

/-- **An epimorphism-preservation criterion for a reflection.**  Let `L : A ⥤ B` and `ι : B ⥤ A`
be functors together with a natural isomorphism `e : ι ⋙ L ≅ 𝟭 B` — typically `L` is a reflector,
`ι` the inclusion of the reflective subcategory `B` and `e` the counit of `L ⊣ ι`, which is an
isomorphism exactly when `ι` is fully faithful — and assume `L` preserves monomorphisms.  If
`T : B ⥤ D` is such that `L ⋙ T` preserves epimorphisms, then so does `T`.

Indeed, for an epimorphism `g` of `B`, factor `ι.map g` in `A` as a (strong) epimorphism `p`
followed by a monomorphism `i`.  Then `L.map (ι.map g) = L.map p ≫ L.map i` is an epimorphism (it
is conjugate to `g` through `e`), hence so is `L.map i`, which is also a monomorphism; as `B` is
balanced, `L.map i` is an isomorphism.  Applying `T` to the factorisation writes
`T.map (L.map (ι.map g))` as an epimorphism followed by an isomorphism, and conjugating back with
`e` gives that `T.map g` is an epimorphism. -/
theorem preservesEpimorphisms_of_reflection {A B D : Type*} [Category A] [Category B] [Category D]
    [HasStrongEpiMonoFactorisations A] [Balanced B] (L : A ⥤ B) (ι : B ⥤ A) (T : B ⥤ D)
    (e : ι ⋙ L ≅ 𝟭 B) (hL : L.PreservesMonomorphisms) (hLT : (L ⋙ T).PreservesEpimorphisms) :
    T.PreservesEpimorphisms where
  preserves {M₂ M₃} g hg := by
    have hL' := hL
    have hLT' := hLT
    have hnat := e.hom.naturality g
    simp only [Functor.id_map] at hnat
    have key : (ι ⋙ L).map g = e.hom.app M₂ ≫ g ≫ e.inv.app M₃ := by
      rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    have hLg : Epi ((ι ⋙ L).map g) := by rw [key]; infer_instance
    have hfac : Epi (L.map (Limits.factorThruImage (ι.map g)) ≫
        L.map (Limits.image.ι (ι.map g))) := by
      rw [← L.map_comp, Limits.image.fac]
      exact hLg
    have hepi : Epi (L.map (Limits.image.ι (ι.map g))) :=
      epi_of_epi (L.map (Limits.factorThruImage (ι.map g))) (L.map (Limits.image.ι (ι.map g)))
    have hmono : Mono (L.map (Limits.image.ι (ι.map g))) := L.map_mono _
    have hiso : IsIso (L.map (Limits.image.ι (ι.map g))) := isIso_of_mono_of_epi _
    have hTL : Epi (T.map ((ι ⋙ L).map g)) := by
      change Epi (T.map (L.map (ι.map g)))
      rw [← Limits.image.fac (ι.map g), L.map_comp, T.map_comp]
      have h1 : Epi ((L ⋙ T).map (Limits.factorThruImage (ι.map g))) := (L ⋙ T).map_epi _
      have h2 : Epi (T.map (L.map (Limits.factorThruImage (ι.map g)))) := h1
      infer_instance
    have hg' : e.inv.app M₂ ≫ (ι ⋙ L).map g ≫ e.hom.app M₃ = g := by
      rw [hnat, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    have key2 : T.map g
        = T.map (e.inv.app M₂) ≫ T.map ((ι ⋙ L).map g) ≫ T.map (e.hom.app M₃) := by
      rw [← T.map_comp, ← T.map_comp, hg']
    rw [key2]
    infer_instance

/-- **The forgetful functor from sheaves of modules to sheaves of abelian groups preserves
epimorphisms.**  This is `preservesEpimorphisms_of_reflection` applied to the sheafification
adjunction `PresheafOfModules.sheafification (𝟙 R.obj) ⊣ SheafOfModules.forget R ⋙
PresheafOfModules.restrictScalars (𝟙 R.obj)` (whose counit is an isomorphism), using that
`PresheafOfModules.sheafification (𝟙 R.obj) ⋙ SheafOfModules.toSheaf R` is definitionally
`PresheafOfModules.toPresheaf R.obj ⋙ presheafToSheaf J AddCommGrpCat`, hence preserves finite
colimits. -/
theorem preservesEpimorphisms_toSheaf {D : Type u'} [Category.{v'} D]
    {J : GrothendieckTopology D} (R : CategoryTheory.Sheaf J RingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (SheafOfModules.toSheaf.{u} R).PreservesEpimorphisms := by
  have hLT : PreservesFiniteColimits
      (PresheafOfModules.sheafification.{u} (𝟙 R.obj) ⋙ SheafOfModules.toSheaf.{u} R) :=
    comp_preservesFiniteColimits (PresheafOfModules.toPresheaf.{u} R.obj)
      (presheafToSheaf J AddCommGrpCat.{u})
  exact preservesEpimorphisms_of_reflection _ _ (SheafOfModules.toSheaf.{u} R)
    (asIso (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)).counit)
    inferInstance inferInstance

/-- `moduleToSheafAb X` preserves epimorphisms. -/
instance moduleToSheafAb_preservesEpimorphisms (X : Scheme.{u}) :
    (moduleToSheafAb X).PreservesEpimorphisms :=
  preservesEpimorphisms_toSheaf X.ringCatSheaf

/-- **The underlying short complex of abelian sheaves of a short exact sequence of `𝒪_X`-modules is
short exact.**  The monomorphism half and middle-exactness come from preservation of finite limits,
the epimorphism half from `moduleToSheafAb_preservesEpimorphisms`. -/
theorem moduleToSheafAb_map_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (moduleToSheafAb X)).ShortExact where
  exact := (moduleToSheafAb_map_exact_and_mono S hS).1
  mono_f := (moduleToSheafAb_map_exact_and_mono S hS).2
  epi_g := by
    have := hS.epi_g
    exact (moduleToSheafAb X).map_epi S.g

/-- **`H⁰(X, S.X₁) → H⁰(X, S.X₂)` is always injective**, for any short exact sequence `S` of
`𝒪_X`-modules: this needs only the monomorphism half of `moduleToSheafAb_map_exact_and_mono`. -/
theorem cohomology_zero_injective (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    Function.Injective ((cohomologyFunctor X 0).map S.f).hom := by
  have := (moduleToSheafAb_map_exact_and_mono S hS).2
  exact Ext.postcomp_mk₀_injective_of_mono _ ((moduleToSheafAb X).map S.f)

/-! ## The long exact cohomology sequence -/

/-- The constant abelian sheaf `ULift ℤ`, the fixed left argument of the `Ext`-groups computing
sheaf cohomology (`Sheaf.H F n = Ext (cohomologyExtLeft X) F n`). -/
def cohomologyExtLeft (X : Scheme.{u}) : TopCat.Sheaf Ab.{u} X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))

variable {S : ShortComplex X.Modules}

/-- The **connecting homomorphism** `δ : Hⁿ(X, S.X₃) →+ Hⁿ⁺¹(X, S.X₁)` of the long exact
cohomology sequence attached to a short exact sequence `S` of `𝒪_X`-modules: composition with the
`Ext`-class of the short exact sequence `S.map (moduleToSheafAb X)` of abelian sheaves. -/
def cohomologyConnectingHom (hS : S.ShortExact) (n : ℕ) :
    cohomology X S.X₃ n →+ cohomology X S.X₁ (n + 1) :=
  (moduleToSheafAb_map_shortExact S hS).extClass.postcomp (cohomologyExtLeft X) rfl

/-- Exactness of the long exact cohomology sequence at `Hⁿ(X, S.X₂)`. -/
theorem cohomology_exact_at_X₂ (hS : S.ShortExact) (n : ℕ) :
    Function.Exact ((cohomologyFunctor X n).map S.f).hom ((cohomologyFunctor X n).map S.g).hom := by
  have h := Ext.covariant_sequence_exact₂' (cohomologyExtLeft X)
    (moduleToSheafAb_map_shortExact S hS) n
  rwa [ShortComplex.ab_exact_iff_function_exact] at h

/-- Exactness of the long exact cohomology sequence at `Hⁿ(X, S.X₃)`: the kernel of the
connecting homomorphism is the image of `Hⁿ(X, S.X₂) → Hⁿ(X, S.X₃)`. -/
theorem cohomology_exact_at_X₃ (hS : S.ShortExact) (n : ℕ) :
    Function.Exact ((cohomologyFunctor X n).map S.g).hom (cohomologyConnectingHom hS n) := by
  have h := Ext.covariant_sequence_exact₃' (cohomologyExtLeft X)
    (moduleToSheafAb_map_shortExact S hS) n (n + 1) rfl
  rwa [ShortComplex.ab_exact_iff_function_exact] at h

/-- Exactness of the long exact cohomology sequence at `Hⁿ⁺¹(X, S.X₁)`: the image of the
connecting homomorphism is the kernel of `Hⁿ⁺¹(X, S.X₁) → Hⁿ⁺¹(X, S.X₂)`. -/
theorem cohomology_exact_at_X₁ (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (cohomologyConnectingHom hS n) ((cohomologyFunctor X (n + 1)).map S.f).hom := by
  have h := Ext.covariant_sequence_exact₁' (cohomologyExtLeft X)
    (moduleToSheafAb_map_shortExact S hS) n (n + 1) rfl
  rwa [ShortComplex.ab_exact_iff_function_exact] at h

/-! ## Linearity of the connecting homomorphism -/

/-- The connecting homomorphism is composition with the `Ext`-class of the short exact sequence of
abelian sheaves underlying `S`. -/
theorem cohomologyConnectingHom_apply (hS : S.ShortExact) (n : ℕ)
    (x : cohomology X S.X₃ n) :
    cohomologyConnectingHom hS n x
      = x.comp (moduleToSheafAb_map_shortExact S hS).extClass rfl := rfl

/-- **Naturality of composition with the `Ext`-class of a short exact sequence.**  For a morphism
`φ : S₁ ⟶ S₂` of short exact sequences in an abelian category with `Ext`-groups, pushing an
`Ext`-class `x : Ext L S₁.X₃ n` forward along `φ.τ₃` and then composing with the `Ext`-class of
`S₂` gives the same as composing with the `Ext`-class of `S₁` and then pushing forward along
`φ.τ₁`.  This is `ShortComplex.ShortExact.extClass_naturality` combined with associativity of
`Ext`-composition.

The statement is deliberately made for an *abstract* abelian category `C`: specialising it to
`C := TopCat.Sheaf Ab X` with `exact` lets Lean pick one single instance path for `Abelian C` and
`HasExt C`, which is what makes the concrete corollary `cohomologyConnectingHom_smul` below go
through. -/
theorem extClass_comp_naturality {C : Type u'} [Category.{v'} C] [Abelian C] [HasExt.{w} C]
    {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂)
    (L : C) {n m : ℕ} (hm : n + 1 = m) (x : Ext L S₁.X₃ n) :
    (x.comp (Ext.mk₀ φ.τ₃) (add_zero n)).comp h₂.extClass hm
      = (x.comp h₁.extClass hm).comp (Ext.mk₀ φ.τ₁) (add_zero m) := by
  rw [Ext.comp_assoc _ _ _ (add_zero n) (zero_add 1) (by omega),
    Ext.comp_assoc _ _ _ hm (add_zero 1) (by omega),
    ← ShortComplex.ShortExact.extClass_naturality h₁ h₂ φ]

/-- Multiplication by a global function `a`, applied to every term of `S`, is an endomorphism of
the image short complex `S.map (moduleToSheafAb X)`: this is `sectionSMul_naturality` applied to
`S.f` and `S.g`. -/
def smulShortComplexEndo (a : Γ(X, ⊤)) :
    S.map (moduleToSheafAb X) ⟶ S.map (moduleToSheafAb X) :=
  ShortComplex.homMk (sectionSMul S.X₁ a) (sectionSMul S.X₂ a) (sectionSMul S.X₃ a)
    (sectionSMul_naturality S.f a).symm (sectionSMul_naturality S.g a).symm

/-- **The connecting homomorphism is `Γ(X, 𝒪_X)`-linear**: it commutes with multiplication by a
global function `a`.  This is `extClass_comp_naturality` applied to the endomorphism
`smulShortComplexEndo a` of `S.map (moduleToSheafAb X)`, using that the `Γ(X, 𝒪_X)`-action on
`Hⁿ(X, M)` is by definition composition with `Ext.mk₀ (sectionSMul M a)`. -/
theorem cohomologyConnectingHom_smul (hS : S.ShortExact) (n : ℕ)
    (a : Γ(X, ⊤)) (x : cohomology X S.X₃ n) :
    cohomologyConnectingHom hS n (a • x) = a • cohomologyConnectingHom hS n x :=
  extClass_comp_naturality (moduleToSheafAb_map_shortExact S hS)
    (moduleToSheafAb_map_shortExact S hS) (smulShortComplexEndo a) (cohomologyExtLeft X) rfl x

/-- The connecting homomorphism `δ : Hⁿ(X, S.X₃) → Hⁿ⁺¹(X, S.X₁)` as a `Γ(X, 𝒪_X)`-linear map. -/
def cohomologyConnectingHomLinear (hS : S.ShortExact) (n : ℕ) :
    cohomology X S.X₃ n →ₗ[Γ(X, ⊤)] cohomology X S.X₁ (n + 1) where
  toFun := cohomologyConnectingHom hS n
  map_add' := (cohomologyConnectingHom hS n).map_add
  map_smul' := cohomologyConnectingHom_smul hS n

/-- The connecting homomorphism as a `k`-linear map of `k`-vector spaces, for a `k`-scheme
structure `f` on `X`: the `k`-action on cohomology is the restriction of the `Γ(X, 𝒪_X)`-action
along `baseRingHom k f`. -/
def cohomologyConnectingHomBaseLinear (hS : S.ShortExact)
    (k : Type u) [CommRing k] (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    cohomologyModuleCat k f S.X₃ n →ₗ[k] cohomologyModuleCat k f S.X₁ (n + 1) where
  toFun := cohomologyConnectingHom hS n
  map_add' := (cohomologyConnectingHom hS n).map_add
  map_smul' c x := cohomologyConnectingHom_smul hS n (baseRingHom k f c) x

/-! ## Additivity of the Euler characteristic -/

/-- `cohomologyMapLinear`, restricted along `baseRingHom k f` to a `k`-linear map between the
`k`-vector spaces `cohomologyModuleCat k f M n` (the same construction as
`baseLinearEquivOfCohomology`, but for a plain linear map rather than an equivalence). -/
def cohomologyMapBaseLinear (k : Type u) [CommRing k] (f : X ⟶ Spec (CommRingCat.of k))
    {M N : X.Modules} (φ : M ⟶ N) (n : ℕ) :
    cohomologyModuleCat k f M n →ₗ[k] cohomologyModuleCat k f N n where
  toFun := cohomologyMapLinear φ n
  map_add' := (cohomologyMapLinear φ n).map_add
  map_smul' c x := (cohomologyMapLinear φ n).map_smul (baseRingHom k f c) x

/-- The alternating sum of dimensions along a six-vertex, five-arrow exact sequence of
finite-dimensional vector spaces vanishes: the six-term analogue of
`alternating_sum_eq_zero_of_exact₅` (`Curves/ArithmeticGenusNormalization.lean:52`), proved by the
same rank-nullity bookkeeping. -/
theorem alternating_sum_eq_zero_of_exact₆ {k V₁ V₂ V₃ V₄ V₅ V₆ : Type*} [Field k]
    [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
    [AddCommGroup V₃] [Module k V₃] [FiniteDimensional k V₃]
    [AddCommGroup V₄] [Module k V₄] [FiniteDimensional k V₄]
    [AddCommGroup V₅] [Module k V₅] [FiniteDimensional k V₅]
    [AddCommGroup V₆] [Module k V₆] [FiniteDimensional k V₆]
    (f₁ : V₁ →ₗ[k] V₂) (f₂ : V₂ →ₗ[k] V₃) (f₃ : V₃ →ₗ[k] V₄) (f₄ : V₄ →ₗ[k] V₅)
    (f₅ : V₅ →ₗ[k] V₆)
    (h₁ : LinearMap.ker f₁ = ⊥)
    (h₂ : LinearMap.ker f₂ = LinearMap.range f₁)
    (h₃ : LinearMap.ker f₃ = LinearMap.range f₂)
    (h₄ : LinearMap.ker f₄ = LinearMap.range f₃)
    (h₅ : LinearMap.ker f₅ = LinearMap.range f₄)
    (h₆ : LinearMap.range f₅ = ⊤) :
    (Module.finrank k V₁ : ℤ) - Module.finrank k V₂ + Module.finrank k V₃
      - Module.finrank k V₄ + Module.finrank k V₅ - Module.finrank k V₆ = 0 := by
  have n1 := f₁.finrank_range_add_finrank_ker
  have n2 := f₂.finrank_range_add_finrank_ker
  have n3 := f₃.finrank_range_add_finrank_ker
  have n4 := f₄.finrank_range_add_finrank_ker
  have n5 := f₅.finrank_range_add_finrank_ker
  rw [h₁, finrank_bot] at n1
  rw [h₂] at n2
  rw [h₃] at n3
  rw [h₄] at n4
  rw [h₅, h₆, finrank_top] at n5
  omega

/-- **Additivity of the Euler characteristic** `χ = h⁰ - h¹` along a short exact sequence of
`𝒪_X`-modules whose cohomology vanishes in degree `2` for `S.X₁` and is finite-dimensional in
degrees `0, 1`.  The proof runs the six-term exact sequence
`H⁰(S.X₁) → H⁰(S.X₂) → H⁰(S.X₃) → H¹(S.X₁) → H¹(S.X₂) → H¹(S.X₃)` of `k`-vector spaces through
`alternating_sum_eq_zero_of_exact₆`, the connecting map being the `k`-linear
`cohomologyConnectingHomBaseLinear hS k f 0`. -/
theorem eulerCharacteristic_add_of_shortExact (hS : S.ShortExact)
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k))
    (h2 : Subsingleton (cohomologyModuleCat k f S.X₁ 2))
    [FiniteDimensional k (cohomologyModuleCat k f S.X₁ 0)]
    [FiniteDimensional k (cohomologyModuleCat k f S.X₂ 0)]
    [FiniteDimensional k (cohomologyModuleCat k f S.X₃ 0)]
    [FiniteDimensional k (cohomologyModuleCat k f S.X₁ 1)]
    [FiniteDimensional k (cohomologyModuleCat k f S.X₂ 1)]
    [FiniteDimensional k (cohomologyModuleCat k f S.X₃ 1)] :
    (hDim k f S.X₂ 0 : ℤ) - hDim k f S.X₂ 1 =
      ((hDim k f S.X₁ 0 : ℤ) - hDim k f S.X₁ 1) + ((hDim k f S.X₃ 0 : ℤ) - hDim k f S.X₃ 1) := by
  obtain ⟨Ξ, hΞ⟩ : ∃ Ξ : cohomologyModuleCat k f S.X₃ 0 →ₗ[k] cohomologyModuleCat k f S.X₁ 1,
      ∀ y, (Ξ y : cohomology X S.X₁ 1) = cohomologyConnectingHom hS 0 y :=
    ⟨cohomologyConnectingHomBaseLinear hS k f 0, fun _ ↦ rfl⟩
  have hf1 : Function.Injective (cohomologyMapBaseLinear k f S.f 0) := by
    have : Mono ((moduleToSheafAb X).map S.f) := (moduleToSheafAb_map_exact_and_mono S hS).2
    exact Ext.postcomp_mk₀_injective_of_mono _ ((moduleToSheafAb X).map S.f)
  have hker1 : LinearMap.ker (cohomologyMapBaseLinear k f S.f 0) = ⊥ :=
    LinearMap.ker_eq_bot.2 hf1
  have hker2 : LinearMap.ker (cohomologyMapBaseLinear k f S.g 0) =
      LinearMap.range (cohomologyMapBaseLinear k f S.f 0) :=
    LinearMap.exact_iff.1 (cohomology_exact_at_X₂ hS 0)
  have hker3 : LinearMap.ker Ξ = LinearMap.range (cohomologyMapBaseLinear k f S.g 0) := by
    have hex := cohomology_exact_at_X₃ hS 0
    ext y
    simp only [LinearMap.mem_ker, LinearMap.mem_range, hΞ y]
    exact hex y
  have hker4 : LinearMap.ker (cohomologyMapBaseLinear k f S.f 1) = LinearMap.range Ξ := by
    have hex := cohomology_exact_at_X₁ hS 0
    ext y
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hy
      obtain ⟨z, hz⟩ := (hex y).1 hy
      exact ⟨z, (hΞ z).trans hz⟩
    · rintro ⟨z, rfl⟩
      exact (hex (Ξ z)).2 ⟨z, (hΞ z).symm⟩
  have hker5 : LinearMap.ker (cohomologyMapBaseLinear k f S.g 1) =
      LinearMap.range (cohomologyMapBaseLinear k f S.f 1) :=
    LinearMap.exact_iff.1 (cohomology_exact_at_X₂ hS 1)
  have h2' : Subsingleton (cohomology X S.X₁ (1 + 1)) := h2
  have hrange5 : LinearMap.range (cohomologyMapBaseLinear k f S.g 1) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    exact (cohomology_exact_at_X₃ hS 1 y).1 (h2'.elim _ _)
  have key := alternating_sum_eq_zero_of_exact₆
    (cohomologyMapBaseLinear k f S.f 0) (cohomologyMapBaseLinear k f S.g 0) Ξ
    (cohomologyMapBaseLinear k f S.f 1) (cohomologyMapBaseLinear k f S.g 1)
    hker1 hker2 hker3 hker4 hker5 hrange5
  simp only [hDim]
  omega

end

end GromovWitten.AlgebraicGeometry.Curves
