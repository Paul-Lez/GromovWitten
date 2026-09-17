/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.Curves.CohomologyBaseChange
import GromovWitten.AlgebraicGeometry.Curves.Prestable
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Arithmetic genus of a curve over a field

This file constructs the coherent cohomology `Hⁿ(X, M)` of an `𝒪_X`-module `M` on a scheme `X`
together with its genuine module structure over the ring of global functions, and defines the
arithmetic genus `p_a(X) = dim_k H¹(X, 𝒪_X)` of a scheme over a field `k`.

## Cohomology

`Hⁿ(X, M)` is Mathlib's `Ext`-theoretic sheaf cohomology `CategoryTheory.Sheaf.H` of the
underlying sheaf of abelian groups of `M` on the topological site of `X`; no cover is chosen and
no cohomology theory is assumed.  The functor `cohomologyFunctor X n : X.Modules ⥤ Ab` is additive
because both of its factors are.

## The module structure

Sheaf cohomology as such produces only abelian groups.  The `𝒪_X`-module structure is restored
here from functoriality:  multiplication by a global function `a : Γ(X, 𝒪_X)` is constructed as an
honest endomorphism `sectionSMul M a` of the underlying abelian sheaf of `M`
(`sectionSMulRingHom` assembles these into a ring homomorphism), and an additive functor induces a
ring homomorphism of endomorphism rings (`additiveMapEndRingHom`).  Composing gives a ring
homomorphism `Γ(X, 𝒪_X) →+* End (Hⁿ(X, M))` and hence the module structure `cohomologyModule`.
A `k`-scheme structure `f : X ⟶ Spec k` gives `k →+* Γ(X, 𝒪_X)` and hence the `k`-vector space
`cohomologyModuleCat k f M n`.

## Main definitions

* `cohomology X M n`, `cohomologyFunctor X n` — coherent cohomology of an `𝒪_X`-module;
* `cohomologyModule` — its `Γ(X, 𝒪_X)`-module structure;
* `cohomologyModuleCat k f M n` — its `k`-vector space structure for a `k`-scheme;
* `hDim k f M n` — the dimension `hⁿ(X, M) = dim_k Hⁿ(X, M)`;
* `arithmeticGenus k f = h¹(X, 𝒪_X)` and `eulerCharacteristic k f = h⁰ - h¹`.

The last definition applies verbatim to the curve types of `Curves/Prestable.lean`; this is
recorded as `prestableArithmeticGenus`.

## Main results

* `cohomologyZeroLinearEquiv` — `H⁰(X, M) ≅ Γ(X, M)` as `Γ(X, 𝒪_X)`-modules, obtained from the
  naturality of Mathlib's degree-zero comparison; hence `hDim_zero_eq_finrank_sections`.
* `hDim_eq_of_iso`, `arithmeticGenus_eq_of_iso` — invariance under isomorphism of modules.
* `hDim_succ_eq_zero_of_injective` — vanishing on injective sheaves.
* `finrank_eq_of_baseChangeEquiv`, `arithmeticGenus_eq_of_baseChangeEquiv` — invariance of the
  genus under extension of the base field, given the flat base-change comparison.
* `isLocallyConstant_of_locally_eq_const` — local constancy of a fibrewise genus that is locally
  computed by the rank of a locally free higher direct image.

The normalization formula and its comparison with the dual-graph genus are in
`GromovWitten/AlgebraicGeometry/Curves/ArithmeticGenusNormalization.lean`.

## What is not proved here

Sheaf cohomology of an `𝒪_X`-module is constructed, but Mathlib has neither the long exact
cohomology sequence of a short exact sequence of abelian sheaves in the form
`CategoryTheory.Sheaf.H`, nor the finiteness of coherent cohomology of a proper scheme, nor flat
base change for it, nor the Leray comparison `Γ(S, Rⁿf_*F) ≅ Hⁿ(X, F)`.  Accordingly the flat
base-change comparison, the exactness of the normalization sequence on cohomology, and the
identification of the fibre cohomology with the fibre of `R¹f_*𝒪` enter the statements below as
explicit hypotheses rather than as fields of a structure; everything that does not need them is
proved outright.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u v₁ u₁ v₂ u₂

noncomputable section

variable {X : Scheme.{u}}

/-! ## Endomorphism ring homomorphisms -/

/-- An additive functor induces a ring homomorphism on endomorphism rings.  This upgrades
`CategoryTheory.Functor.mapEnd`, which records only the multiplicative structure. -/
def additiveMapEndRingHom {C : Type u₁} [Category.{v₁} C] [Preadditive C] {D : Type u₂}
    [Category.{v₂} D] [Preadditive D] (F : C ⥤ D) [F.Additive] (A : C) :
    End A →+* End (F.obj A) where
  toFun := F.map
  map_one' := F.map_id A
  map_mul' x y := F.map_comp y x
  map_zero' := F.map_zero _ _
  map_add' _ _ := F.map_add

@[simp]
theorem additiveMapEndRingHom_apply {C : Type u₁} [Category.{v₁} C] [Preadditive C] {D : Type u₂}
    [Category.{v₂} D] [Preadditive D] (F : C ⥤ D) [F.Additive] (A : C) (f : End A) :
    additiveMapEndRingHom F A f = F.map f := rfl

/-- The ring homomorphism from the categorical endomorphism ring of an object of `Ab` to the
endomorphism ring of the underlying additive group. -/
def abEndRingHom (G : Ab.{u}) : End G →+* AddMonoid.End (G : Type u) where
  toFun f := f.hom
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem abEndRingHom_apply (G : Ab.{u}) (f : End G) (x : G) :
    abEndRingHom G f x = f.hom x := rfl

/-- A ring homomorphism into the endomorphism ring of an object of `Ab` makes the underlying
group a module. -/
@[instance_reducible]
def moduleOfEndRingHom (G : Ab.{u}) (R : Type u) [Ring R] (φ : R →+* End G) :
    Module R (G : Type u) :=
  Module.compHom _ ((abEndRingHom G).comp φ)

theorem moduleOfEndRingHom_smul (G : Ab.{u}) (R : Type u) [Ring R] (φ : R →+* End G)
    (r : R) (x : G) :
    letI := moduleOfEndRingHom G R φ
    r • x = (φ r).hom x := rfl

/-! ## Sheaf cohomology of an `𝒪_X`-module -/

/-- Sheaf cohomology `Hⁿ(X, -)` of abelian sheaves on a scheme: Mathlib's `Ext`-theoretic sheaf
cohomology for the topological site of `X`. -/
def sheafCohomologyFunctorAb (X : Scheme.{u}) (n : ℕ) : TopCat.Sheaf Ab.{u} X ⥤ Ab.{u} :=
  Sheaf.functorH (Opens.grothendieckTopology X) n

instance sheafCohomologyFunctorAb_additive (X : Scheme.{u}) (n : ℕ) :
    (sheafCohomologyFunctorAb X n).Additive :=
  inferInstanceAs (Sheaf.functorH (Opens.grothendieckTopology X) n).Additive

/-- The coherent cohomology functor `M ↦ Hⁿ(X, M)` on `𝒪_X`-modules: sheaf cohomology of the
underlying sheaf of abelian groups. -/
def cohomologyFunctor (X : Scheme.{u}) (n : ℕ) : X.Modules ⥤ Ab.{u} :=
  moduleToSheafAb X ⋙ sheafCohomologyFunctorAb X n

instance cohomologyFunctor_additive (X : Scheme.{u}) (n : ℕ) :
    (cohomologyFunctor X n).Additive := by
  unfold cohomologyFunctor
  infer_instance

/-- The cohomology `Hⁿ(X, M)` of an `𝒪_X`-module, as an abelian group. -/
def cohomology (X : Scheme.{u}) (M : X.Modules) (n : ℕ) : Ab.{u} :=
  (cohomologyFunctor X n).obj M

theorem cohomology_eq (X : Scheme.{u}) (M : X.Modules) (n : ℕ) :
    cohomology X M n = (sheafCohomologyFunctorAb X n).obj ((moduleToSheafAb X).obj M) := rfl

/-! ## Multiplication by a global function -/

/-- Restriction of global functions to an open subset, as a ring homomorphism. -/
def restrictTop (X : Scheme.{u}) (U : X.Opens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom

theorem restrictTop_map {U V : X.Opens} (i : V ⟶ U) (a : Γ(X, ⊤)) :
    (X.presheaf.map i.op).hom (restrictTop X U a) = restrictTop X V a := by
  rw [restrictTop, restrictTop, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
  congr 2

@[simp]
theorem restrictTop_top (a : Γ(X, ⊤)) : restrictTop X ⊤ a = a := by
  change (X.presheaf.map (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤).op).hom a = a
  have h : (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤).op = 𝟙 (Opposite.op (⊤ : X.Opens)) := rfl
  rw [h, X.presheaf.map_id]
  rfl

/-- Multiplication by a global function on the underlying abelian presheaf of an
`𝒪_X`-module. -/
def sectionSMulPresheaf (M : X.Modules) (a : Γ(X, ⊤)) :
    Scheme.Modules.presheaf M ⟶ Scheme.Modules.presheaf M where
  app W := Scheme.Modules.smul (M := M) (U := W.unop) (restrictTop X W.unop a)
  naturality := by
    rintro ⟨U⟩ ⟨V⟩ f
    have h := Scheme.Modules.map_comp_smul (M := M) f.unop (restrictTop X U a)
    rw [restrictTop_map] at h
    exact h.symm

/-- Multiplication by a global function, as an endomorphism of the underlying abelian sheaf of an
`𝒪_X`-module. -/
def sectionSMul (M : X.Modules) (a : Γ(X, ⊤)) :
    (moduleToSheafAb X).obj M ⟶ (moduleToSheafAb X).obj M :=
  ⟨sectionSMulPresheaf M a⟩

@[simp]
theorem sectionSMul_app (M : X.Modules) (a : Γ(X, ⊤)) (U : X.Opens) (x : Γ(M, U)) :
    ((sectionSMul M a).hom.app (Opposite.op U)).hom x = restrictTop X U a • x := rfl

/-- Two morphisms of abelian sheaves agreeing on underlying presheaves are equal. -/
theorem sheafAb_hom_ext {A B : TopCat.Sheaf Ab.{u} X} {f g : A ⟶ B}
    (h : f.hom = g.hom) : f = g :=
  Sheaf.homEquiv.injective h

/-- Multiplication by global functions, as a ring homomorphism to the endomorphism ring of the
underlying abelian sheaf of an `𝒪_X`-module. -/
def sectionSMulRingHom (M : X.Modules) : Γ(X, ⊤) →+* End ((moduleToSheafAb X).obj M) where
  toFun := sectionSMul M
  map_one' := by
    refine sheafAb_hom_ext ?_
    ext W x
    simp only [sectionSMul, sectionSMulPresheaf, map_one]
    rfl
  map_mul' a b := by
    refine sheafAb_hom_ext ?_
    ext W x
    simp only [sectionSMul, sectionSMulPresheaf, map_mul]
    rfl
  map_zero' := by
    refine sheafAb_hom_ext ?_
    ext W x
    simp only [sectionSMul, sectionSMulPresheaf, map_zero]
    rfl
  map_add' a b := by
    refine sheafAb_hom_ext ?_
    ext W x
    simp only [sectionSMul, sectionSMulPresheaf, map_add]
    rfl

@[simp]
theorem sectionSMulRingHom_apply (M : X.Modules) (a : Γ(X, ⊤)) :
    sectionSMulRingHom M a = sectionSMul M a := rfl

/-- Multiplication by a global function is natural in the module: every morphism of
`𝒪_X`-modules is `Γ(X, 𝒪_X)`-linear. -/
theorem sectionSMul_naturality {M N : X.Modules} (φ : M ⟶ N) (a : Γ(X, ⊤)) :
    (moduleToSheafAb X).map φ ≫ sectionSMul N a =
      sectionSMul M a ≫ (moduleToSheafAb X).map φ := by
  refine sheafAb_hom_ext ?_
  ext W x
  exact (Scheme.Modules.Hom.app_smul φ (restrictTop X W.unop a) x).symm

/-! ## The module structure on cohomology -/

/-- Multiplication by global functions on `Hⁿ(X, M)`, as a ring homomorphism. -/
def cohomologySMulRingHom (M : X.Modules) (n : ℕ) :
    Γ(X, ⊤) →+* End (cohomology X M n) :=
  (additiveMapEndRingHom (sheafCohomologyFunctorAb X n)
    ((moduleToSheafAb X).obj M)).comp (sectionSMulRingHom M)

/-- The `Γ(X, 𝒪_X)`-module structure on `Hⁿ(X, M)`. -/
instance cohomologyModule (M : X.Modules) (n : ℕ) :
    Module Γ(X, ⊤) (cohomology X M n) :=
  moduleOfEndRingHom _ _ (cohomologySMulRingHom M n)

theorem cohomology_smul_def (M : X.Modules) (n : ℕ) (a : Γ(X, ⊤))
    (x : cohomology X M n) :
    a • x = ((sheafCohomologyFunctorAb X n).map (sectionSMul M a)).hom x := rfl

/-- Functoriality of cohomology is `Γ(X, 𝒪_X)`-linear. -/
def cohomologyMapLinear {M N : X.Modules} (φ : M ⟶ N) (n : ℕ) :
    cohomology X M n →ₗ[Γ(X, ⊤)] cohomology X N n where
  toFun := ((cohomologyFunctor X n).map φ).hom
  map_add' _ _ := map_add _ _ _
  map_smul' a x := by
    have h := congrArg (fun ψ ↦ (sheafCohomologyFunctorAb X n).map ψ)
      (sectionSMul_naturality φ a)
    simp only [Functor.map_comp] at h
    exact congrArg (fun ψ : cohomology X M n ⟶ cohomology X N n ↦ ψ.hom x) h.symm

/-- An isomorphism of `𝒪_X`-modules induces a `Γ(X, 𝒪_X)`-linear isomorphism on cohomology. -/
def cohomologyMapLinearEquiv {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    cohomology X M n ≃ₗ[Γ(X, ⊤)] cohomology X N n where
  __ := cohomologyMapLinear e.hom n
  invFun := ((cohomologyFunctor X n).map e.inv).hom
  left_inv x := by
    have h : (cohomologyFunctor X n).map e.hom ≫ (cohomologyFunctor X n).map e.inv = 𝟙 _ := by
      rw [← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id]
    exact congrArg (fun ψ : cohomology X M n ⟶ cohomology X M n ↦ ψ.hom x) h
  right_inv x := by
    have h : (cohomologyFunctor X n).map e.inv ≫ (cohomologyFunctor X n).map e.hom = 𝟙 _ := by
      rw [← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id]
    exact congrArg (fun ψ : cohomology X N n ⟶ cohomology X N n ↦ ψ.hom x) h

/-! ## Degree zero -/

/-- The whole space is a terminal object of the site of opens. -/
def isTerminal_top (X : Scheme.{u}) : IsTerminal (⊤ : X.Opens) :=
  IsTerminal.ofUnique _

theorem cohomology_smul_apply (M : X.Modules) (n : ℕ) (a : Γ(X, ⊤))
    (x : cohomology X M n) :
    a • x = Sheaf.H.map (sectionSMul M a) n x := rfl

/-- **Degree-zero cohomology is global sections**: Mathlib's degree-zero comparison, as an
additive isomorphism. -/
def cohomologyZeroAddEquiv (M : X.Modules) :
    (cohomology X M 0 : Type u) ≃+ (Γ(M, ⊤) : Type u) :=
  Sheaf.H.equiv₀ ((moduleToSheafAb X).obj M) (isTerminal_top X)

/-- The degree-zero comparison is `Γ(X, 𝒪_X)`-linear; this is the naturality of Mathlib's
comparison applied to multiplication by a global function. -/
theorem cohomologyZeroAddEquiv_smul (M : X.Modules) (a : Γ(X, ⊤))
    (x : cohomology X M 0) :
    cohomologyZeroAddEquiv M (a • x) = a • cohomologyZeroAddEquiv M x := by
  refine (Sheaf.H.equiv₀_naturality (isTerminal_top X) (sectionSMul M a) x).symm.trans ?_
  change restrictTop X ⊤ a • cohomologyZeroAddEquiv M x = a • cohomologyZeroAddEquiv M x
  rw [restrictTop_top]

/-- **Degree-zero cohomology is global sections**, as `Γ(X, 𝒪_X)`-modules. -/
def cohomologyZeroLinearEquiv (M : X.Modules) :
    cohomology X M 0 ≃ₗ[Γ(X, ⊤)] Γ(M, ⊤) where
  toFun := cohomologyZeroAddEquiv M
  map_add' := (cohomologyZeroAddEquiv M).map_add
  map_smul' := cohomologyZeroAddEquiv_smul M
  invFun := (cohomologyZeroAddEquiv M).symm
  left_inv := (cohomologyZeroAddEquiv M).left_inv
  right_inv := (cohomologyZeroAddEquiv M).right_inv

/-- Positive-degree sheaf cohomology of an injective abelian sheaf vanishes. -/
theorem subsingleton_sheafCohomology_succ_of_injective
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    [Injective F] : Subsingleton (Sheaf.H F (n + 1)) := inferInstance

/-- Positive-degree cohomology of a module with injective underlying abelian sheaf vanishes. -/
theorem subsingleton_cohomology_succ_of_injective (M : X.Modules) (n : ℕ)
    (hI : Injective (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      ((moduleToSheafAb X).obj M)) :
    Subsingleton (cohomology X M (n + 1)) :=
  @subsingleton_sheafCohomology_succ_of_injective X ((moduleToSheafAb X).obj M) n hI

/-! ## The `k`-vector space structure and the arithmetic genus -/

/-- The structure ring homomorphism `k → Γ(X, 𝒪_X)` of a scheme over a commutative ring. -/
def baseRingHom (k : Type u) [CommRing k] (f : X ⟶ Spec (CommRingCat.of k)) :
    k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom

/-- The `k`-module structure on `Hⁿ(X, M)` coming from a `k`-scheme structure on `X`. -/
@[instance_reducible]
def cohomologyBaseModule (k : Type u) [CommRing k] (f : X ⟶ Spec (CommRingCat.of k))
    (M : X.Modules) (n : ℕ) : Module k (cohomology X M n) :=
  Module.compHom _ (baseRingHom k f)

/-- `Hⁿ(X, M)` as a `k`-module, bundled. -/
def cohomologyModuleCat (k : Type u) [CommRing k] (f : X ⟶ Spec (CommRingCat.of k))
    (M : X.Modules) (n : ℕ) : ModuleCat.{u} k :=
  @ModuleCat.of k _ (cohomology X M n) _ (cohomologyBaseModule k f M n)

/-- The `k`-module structure on the global sections of an `𝒪_X`-module. -/
@[instance_reducible]
def sectionsBaseModule (k : Type u) [CommRing k] (f : X ⟶ Spec (CommRingCat.of k))
    (M : X.Modules) : Module k Γ(M, ⊤) :=
  Module.compHom _ (baseRingHom k f)

/-- The global sections of an `𝒪_X`-module as a `k`-module, bundled. -/
def sectionsModuleCat (k : Type u) [CommRing k] (f : X ⟶ Spec (CommRingCat.of k))
    (M : X.Modules) : ModuleCat.{u} k :=
  @ModuleCat.of k _ Γ(M, ⊤) _ (sectionsBaseModule k f M)

/-- The dimension `hⁿ(X, M) = dim_k Hⁿ(X, M)` of coherent cohomology.  By the convention of
`Module.finrank` this is `0` when the cohomology is infinite dimensional. -/
def hDim (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) (M : X.Modules) (n : ℕ) : ℕ :=
  Module.finrank k (cohomologyModuleCat k f M n)

/-- A `Γ(X, 𝒪_X)`-linear equivalence is `k`-linear for any `k`-scheme structure, because the
`k`-action is restriction of scalars along `baseRingHom`. -/
def baseLinearEquivOfCohomology (k : Type u) [CommRing k] (f : X ⟶ Spec (CommRingCat.of k))
    {M N : X.Modules} {n : ℕ} (e : cohomology X M n ≃ₗ[Γ(X, ⊤)] cohomology X N n) :
    cohomologyModuleCat k f M n ≃ₗ[k] cohomologyModuleCat k f N n where
  toFun := e
  map_add' := e.map_add
  map_smul' c x := e.map_smul (baseRingHom k f c) x
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv

/-- Cohomology dimensions only depend on the isomorphism class of the module. -/
theorem hDim_eq_of_iso (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k))
    {M N : X.Modules} (e : M ≅ N) (n : ℕ) : hDim k f M n = hDim k f N n :=
  (baseLinearEquivOfCohomology k f (cohomologyMapLinearEquiv e n)).finrank_eq

/-- The degree-zero comparison as a `k`-linear equivalence. -/
def cohomologyZeroBaseLinearEquiv (k : Type u) [CommRing k]
    (f : X ⟶ Spec (CommRingCat.of k)) (M : X.Modules) :
    cohomologyModuleCat k f M 0 ≃ₗ[k] sectionsModuleCat k f M where
  toFun := cohomologyZeroLinearEquiv M
  map_add' := (cohomologyZeroLinearEquiv M).map_add
  map_smul' c x := (cohomologyZeroLinearEquiv M).map_smul (baseRingHom k f c) x
  invFun := (cohomologyZeroLinearEquiv M).symm
  left_inv := (cohomologyZeroLinearEquiv M).left_inv
  right_inv := (cohomologyZeroLinearEquiv M).right_inv

/-- `h⁰(X, M)` is the dimension of the space of global sections. -/
theorem hDim_zero_eq_finrank_sections (k : Type u) [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) (M : X.Modules) :
    hDim k f M 0 = Module.finrank k (sectionsModuleCat k f M) :=
  (cohomologyZeroBaseLinearEquiv k f M).finrank_eq

/-- Cohomology of a module whose underlying abelian sheaf is injective vanishes in positive
degrees. -/
theorem hDim_succ_eq_zero_of_injective (k : Type u) [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) (M : X.Modules) (n : ℕ)
    (hI : Injective (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      ((moduleToSheafAb X).obj M)) :
    hDim k f M (n + 1) = 0 := by
  have _ : Subsingleton (cohomologyModuleCat k f M (n + 1)) :=
    subsingleton_cohomology_succ_of_injective M n hI
  exact Module.finrank_zero_of_subsingleton

/-! ## The arithmetic genus -/

/-- The structure sheaf as an `𝒪_X`-module. -/
def structureModule (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- The **arithmetic genus** `p_a(X) = dim_k H¹(X, 𝒪_X)` of a scheme over a field.  This is the
convention matching the dual-graph genus `DualGraph.arithmeticGenus`, which for a connected
curve equals `dim H¹(𝒪)`. -/
def arithmeticGenus (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) : ℕ :=
  hDim k f (structureModule X) 1

/-- The Euler characteristic `χ(𝒪_X) = h⁰ - h¹`. -/
def eulerCharacteristic (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) : ℤ :=
  (hDim k f (structureModule X) 0 : ℤ) - (hDim k f (structureModule X) 1 : ℤ)

/-- For a scheme with one-dimensional space of global functions — for instance a proper,
geometrically connected and geometrically reduced curve — the genus is `1 - χ(𝒪_X)`. -/
theorem eulerCharacteristic_eq_one_sub_arithmeticGenus (k : Type u) [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) (h0 : hDim k f (structureModule X) 0 = 1) :
    eulerCharacteristic k f = 1 - (arithmeticGenus k f : ℤ) := by
  rw [eulerCharacteristic, arithmeticGenus, h0]
  norm_num

/-- The arithmetic genus only depends on the isomorphism class of the structure sheaf as a
module; in particular it is invariant under isomorphisms of `k`-schemes inducing such an
isomorphism. -/
theorem arithmeticGenus_eq_of_iso (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k))
    {M : X.Modules} (e : structureModule X ≅ M) :
    arithmeticGenus k f = hDim k f M 1 :=
  hDim_eq_of_iso k f e 1

/-- The arithmetic genus of a prestable curve over a field.  The definition of this file applies
verbatim to the curve types of `Curves/Prestable.lean`: a prestable family over `Spec k` is in
particular a scheme over `k`, and its arithmetic genus is `dim_k H¹(X, 𝒪_X)`. -/
def prestableArithmeticGenus (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k))
    [PrestableFamily f] : ℕ :=
  arithmeticGenus k f

@[simp]
theorem prestableArithmeticGenus_eq (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k))
    [PrestableFamily f] : prestableArithmeticGenus k f = arithmeticGenus k f := rfl

/-! ## Invariance under base change of the ground ring -/

/-- If the base change of a free module along a ring map to a field is identified with a vector
space, then the dimension of that vector space is the rank of the module.

This is the linear-algebra core both of the invariance of the arithmetic genus under extension of
the base field (take `A = k` a field, `K = L` an extension, and `e` the flat base-change
comparison `L ⊗_k H¹(X, 𝒪_X) ≅ H¹(X_L, 𝒪_{X_L})`) and of the locally-free-rank characterization
of the genus in a family (take `A` the local ring of the base at a point, `K` its residue field,
and `e` the cohomology-and-base-change comparison for `R¹f_*𝒪`). -/
theorem finrank_eq_of_baseChangeEquiv {A K V W : Type*} [CommRing A] [StrongRankCondition A]
    [Field K] [Algebra A K] [AddCommGroup V] [Module A V] [Module.Free A V]
    [AddCommGroup W] [Module K W] (e : TensorProduct A K V ≃ₗ[K] W) :
    Module.finrank K W = Module.finrank A V := by
  rw [← e.finrank_eq]
  exact Module.finrank_baseChange

/-- **Invariance of cohomology dimensions under extension of the base field**, given the flat
base-change comparison. -/
theorem hDim_eq_of_baseChangeEquiv {k L : Type u} [Field k] [Field L] [Algebra k L]
    {X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of L))
    (M : X.Modules) (M' : X'.Modules) (n : ℕ)
    (e : TensorProduct k L (cohomologyModuleCat k f M n) ≃ₗ[L] cohomologyModuleCat L f' M' n) :
    hDim L f' M' n = hDim k f M n :=
  finrank_eq_of_baseChangeEquiv e

/-- **Invariance of the arithmetic genus under extension of the base field**, given the flat
base-change comparison `L ⊗_k H¹(X, 𝒪_X) ≅ H¹(X_L, 𝒪_{X_L})`. -/
theorem arithmeticGenus_eq_of_baseChangeEquiv {k L : Type u} [Field k] [Field L] [Algebra k L]
    {X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of L))
    (e : TensorProduct k L (cohomologyModuleCat k f (structureModule X) 1) ≃ₗ[L]
      cohomologyModuleCat L f' (structureModule X') 1) :
    arithmeticGenus L f' = arithmeticGenus k f :=
  finrank_eq_of_baseChangeEquiv e

/-! ## Local constancy in a family -/

/-- A natural-number invariant of the points of a topological space that is locally equal to some
constant is locally constant.

Together with `finrank_eq_of_baseChangeEquiv` this is the local constancy of the fibrewise
arithmetic genus in a flat proper family: on an open set where `R¹f_*𝒪` is free of rank `r`,
cohomology and base change identifies every fibre `H¹(X_s, 𝒪)` with `κ(s) ⊗ 𝒪_S^r`, whose
dimension is `r`. -/
theorem isLocallyConstant_of_locally_eq_const {S : Type*} [TopologicalSpace S] (g : S → ℕ)
    (h : ∀ s : S, ∃ (U : Set S) (r : ℕ), IsOpen U ∧ s ∈ U ∧ ∀ t ∈ U, g t = r) :
    IsLocallyConstant g := by
  rw [IsLocallyConstant.iff_exists_open]
  intro s
  obtain ⟨U, r, hU, hsU, hconst⟩ := h s
  exact ⟨U, hU, hsU, fun t ht ↦ (hconst t ht).trans (hconst s hsU).symm⟩

end

end GromovWitten.AlgebraicGeometry.Curves
