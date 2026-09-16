/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib

/-!
# Finite extensions of discrete valuation rings

A finite extension records a finite separable extension of the fraction field together with a
chosen maximal ideal of the integral closure above the closed point.  The extended DVR is the
localization at that ideal.  Its local, DVR, and fraction-field properties are consequences, not
additional structure fields.

The file ends with an unconditional construction of common refinements
(`FiniteDVRExtension.nonempty_commonRefinement`): any two chosen finite DVR extensions of the same
base embed compatibly into a third one.  The construction embeds both extension fields into a
finite Galois extension of the fraction field, lifts both selected primes to the integral closure
there, and moves one of the two lifts onto the other by an automorphism of the Galois extension.
-/

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

open CategoryTheory

universe u

noncomputable section

/-- A bundled field, used so later structure fields can depend on its field instance while
`relaxedAutoImplicit` is disabled. -/
structure FieldCarrier where
  carrier : Type u
  field : Field carrier

attribute [instance] FieldCarrier.field

/-- A finite separable field extension together with a chosen extension of the valuation of `R`.

The integral closure need not be local, so the prime above the maximal ideal is essential data.
The corresponding local ring is defined below as `Localization.AtPrime E.prime`. -/
structure FiniteDVRExtension (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] where
  extension : FieldCarrier.{u}
  [extensionAlgebra : Algebra K extension.carrier]
  [extensionBaseAlgebra : Algebra R extension.carrier]
  [extensionTower : IsScalarTower R K extension.carrier]
  [extensionFinite : FiniteDimensional K extension.carrier]
  [extensionSeparable : Algebra.IsSeparable K extension.carrier]
  prime : Ideal (integralClosure R extension.carrier)
  prime_isMaximal : prime.IsMaximal
  prime_liesOver : prime.LiesOver (IsLocalRing.maximalIdeal R)

attribute [instance] FiniteDVRExtension.extensionAlgebra
  FiniteDVRExtension.extensionBaseAlgebra FiniteDVRExtension.extensionTower
  FiniteDVRExtension.extensionFinite FiniteDVRExtension.extensionSeparable

namespace FiniteDVRExtension

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- The field in a finite DVR extension. -/
abbrev extensionField (E : FiniteDVRExtension R K) : Type u := E.extension.carrier

instance (E : FiniteDVRExtension R K) : E.prime.IsMaximal := E.prime_isMaximal

instance (E : FiniteDVRExtension R K) :
    E.prime.LiesOver (IsLocalRing.maximalIdeal R) := E.prime_liesOver

/-- The integral closure before choosing a local factor. -/
abbrev integralClosureRing (E : FiniteDVRExtension R K) : Type u :=
  integralClosure R E.extensionField

/-- The extension DVR selected by `E.prime`. -/
abbrev localRing (E : FiniteDVRExtension R K) : Type u := Localization.AtPrime E.prime

instance (E : FiniteDVRExtension R K) :
    IsFractionRing E.integralClosureRing E.extensionField :=
  integralClosure.isFractionRing_of_finite_extension K E.extensionField

instance (E : FiniteDVRExtension R K) : IsDedekindDomain E.integralClosureRing :=
  integralClosure.isDedekindDomain R K E.extensionField

/-- The base embeds in its integral closure inside the extension field. -/
lemma algebraMap_integralClosureRing_injective (E : FiniteDVRExtension R K) :
    Function.Injective (algebraMap R E.integralClosureRing) := by
  intro x y h
  apply IsFractionRing.injective R K
  apply (algebraMap K E.extensionField).injective
  rw [← IsScalarTower.algebraMap_apply R K E.extensionField,
    ← IsScalarTower.algebraMap_apply R K E.extensionField]
  simpa only [IsScalarTower.algebraMap_apply R E.integralClosureRing E.extensionField] using
    congrArg (algebraMap E.integralClosureRing E.extensionField) h

instance (E : FiniteDVRExtension R K) : FaithfulSMul R E.integralClosureRing :=
  (faithfulSMul_iff_algebraMap_injective R E.integralClosureRing).mpr
    E.algebraMap_integralClosureRing_injective

/-- A prime above the nonzero maximal ideal of a DVR is nonzero. -/
lemma prime_ne_bot (E : FiniteDVRExtension R K) : E.prime ≠ ⊥ :=
  Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field R) E.prime

instance (E : FiniteDVRExtension R K) : IsDiscreteValuationRing E.localRing :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    E.integralClosureRing (P := E.prime) E.prime_ne_bot E.localRing

/-- The canonical embedding of the selected localization into the extension field. -/
def localRingToExtensionField (E : FiniteDVRExtension R K) :
    E.localRing →+* E.extensionField :=
  IsLocalization.lift (S := E.localRing) (M := E.prime.primeCompl)
    (g := algebraMap E.integralClosureRing E.extensionField) fun y ↦
      isUnit_iff_ne_zero.mpr fun hy ↦ by
    have hy₀ : (y : E.integralClosureRing) = 0 :=
      (IsFractionRing.injective E.integralClosureRing E.extensionField) (by simpa using hy)
    exact y.2 (hy₀ ▸ E.prime.zero_mem)

/-- The extension field as an algebra over the selected localization. -/
instance (E : FiniteDVRExtension R K) : Algebra E.localRing E.extensionField :=
  E.localRingToExtensionField.toAlgebra

instance (E : FiniteDVRExtension R K) :
    IsScalarTower E.integralClosureRing E.localRing E.extensionField := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  exact (IsLocalization.lift_eq (S := E.localRing) (M := E.prime.primeCompl)
    (g := algebraMap E.integralClosureRing E.extensionField) _ x).symm

instance (E : FiniteDVRExtension R K) : IsScalarTower R E.localRing E.extensionField :=
  IsScalarTower.to₁₃₄ R E.integralClosureRing E.localRing E.extensionField

/-- The extension field is the fraction field of the selected extension DVR. -/
instance (E : FiniteDVRExtension R K) : IsFractionRing E.localRing E.extensionField :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization E.prime.primeCompl
    E.localRing E.extensionField

/-- The selected local ring dominates the original DVR. -/
instance (E : FiniteDVRExtension R K) : IsLocalHom (algebraMap R E.localRing) := by
  let _ : (IsLocalRing.maximalIdeal E.localRing).LiesOver E.prime :=
    IsLocalization.AtPrime.liesOver_maximalIdeal E.localRing E.prime
  let _ : (IsLocalRing.maximalIdeal E.localRing).LiesOver
      (IsLocalRing.maximalIdeal R) :=
    Ideal.LiesOver.trans (IsLocalRing.maximalIdeal E.localRing) E.prime
      (IsLocalRing.maximalIdeal R)
  apply ((IsLocalRing.local_hom_TFAE (algebraMap R E.localRing)).out 4 0).mp
  rw [← Ideal.under_def]
  exact Ideal.LiesOver.over.symm

@[simp]
lemma algebraMap_localRing_extensionField (E : FiniteDVRExtension R K) :
    algebraMap E.localRing E.extensionField = E.localRingToExtensionField := rfl

@[simp]
lemma algebraMap_integralClosure_localRing_extensionField
    (E : FiniteDVRExtension R K) (x : E.integralClosureRing) :
    algebraMap E.localRing E.extensionField (algebraMap E.integralClosureRing E.localRing x) =
      algebraMap E.integralClosureRing E.extensionField x :=
  (IsScalarTower.algebraMap_apply E.integralClosureRing E.localRing E.extensionField x).symm

@[simp]
lemma algebraMap_base_localRing_extensionField (E : FiniteDVRExtension R K) (x : R) :
    algebraMap E.localRing E.extensionField (algebraMap R E.localRing x) =
      algebraMap R E.extensionField x :=
  (IsScalarTower.algebraMap_apply R E.localRing E.extensionField x).symm

/-- The base DVR embeds in the selected extension DVR. -/
lemma algebraMap_localRing_injective (E : FiniteDVRExtension R K) :
    Function.Injective (algebraMap R E.localRing) := by
  intro x y h
  apply IsFractionRing.injective R K
  apply (algebraMap K E.extensionField).injective
  rw [← IsScalarTower.algebraMap_apply R K E.extensionField,
    ← IsScalarTower.algebraMap_apply R K E.extensionField,
    ← E.algebraMap_base_localRing_extensionField x,
    ← E.algebraMap_base_localRing_extensionField y, h]

instance (E : FiniteDVRExtension R K) : FaithfulSMul R E.localRing :=
  (faithfulSMul_iff_algebraMap_injective R E.localRing).mpr E.algebraMap_localRing_injective

/-- The selected extension DVR is torsion-free over the base DVR. -/
instance (E : FiniteDVRExtension R K) : Module.IsTorsionFree R E.localRing := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro a x h
  rw [Algebra.smul_def] at h
  rcases mul_eq_zero.mp h with ha | hx
  · left
    apply E.algebraMap_localRing_injective
    simpa using ha
  · exact Or.inr hx

/-- Torsion-free modules over the base DVR are flat. -/
instance (E : FiniteDVRExtension R K) : Module.Flat R E.localRing := by
  infer_instance

/-- The selected local extension is faithfully flat because it is a flat local map of
local rings. -/
instance (E : FiniteDVRExtension R K) : Module.FaithfullyFlat R E.localRing := by
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- A compatible embedding between two choices of finite DVR extension.

Both the finite field extension and the selected local valuation ring are respected.  Locality
is included because an arbitrary embedding of DVRs need not preserve the chosen closed point. -/
structure Hom (E F : FiniteDVRExtension R K) where
  fieldHom : E.extensionField →ₐ[K] F.extensionField
  localRingHom : E.localRing →ₐ[R] F.localRing
  localRingHom_isLocal : IsLocalHom localRingHom.toRingHom
  fraction_commutes (x : E.localRing) :
    algebraMap F.localRing F.extensionField (localRingHom x) =
      fieldHom (algebraMap E.localRing E.extensionField x)

namespace Hom

variable {E F G H : FiniteDVRExtension R K}

instance (f : Hom E F) : IsLocalHom f.localRingHom.toRingHom :=
  f.localRingHom_isLocal

/-- Compatibility with fraction-field embeddings as an equality of ring homomorphisms. -/
lemma fraction_commutes_ringHom (f : Hom E F) :
    (algebraMap F.localRing F.extensionField).comp f.localRingHom.toRingHom =
      f.fieldHom.toRingHom.comp (algebraMap E.localRing E.extensionField) := by
  ext x
  exact f.fraction_commutes x

/-- The local-ring map in a compatible embedding is injective. -/
lemma localRingHom_injective (f : Hom E F) : Function.Injective f.localRingHom := by
  intro x y h
  apply IsFractionRing.injective E.localRing E.extensionField
  apply f.fieldHom.injective
  change f.fieldHom (algebraMap E.localRing E.extensionField x) =
    f.fieldHom (algebraMap E.localRing E.extensionField y)
  rw [← f.fraction_commutes x, ← f.fraction_commutes y, h]

@[ext]
lemma ext {f g : Hom E F} (hfield : f.fieldHom = g.fieldHom)
    (hlocal : f.localRingHom = g.localRingHom) : f = g := by
  cases f
  cases g
  cases hfield
  cases hlocal
  rfl

/-- The identity compatible embedding. -/
def refl (E : FiniteDVRExtension R K) : Hom E E where
  fieldHom := AlgHom.id K _
  localRingHom := AlgHom.id R _
  localRingHom_isLocal := by
    change IsLocalHom (RingHom.id E.localRing)
    infer_instance
  fraction_commutes _ := rfl

/-- Composition of compatible embeddings. -/
def comp (f : Hom E F) (g : Hom F G) : Hom E G where
  fieldHom := g.fieldHom.comp f.fieldHom
  localRingHom := g.localRingHom.comp f.localRingHom
  localRingHom_isLocal := by
    let _ : IsLocalHom f.localRingHom.toRingHom := f.localRingHom_isLocal
    let _ : IsLocalHom g.localRingHom.toRingHom := g.localRingHom_isLocal
    exact RingHom.isLocalHom_comp g.localRingHom.toRingHom f.localRingHom.toRingHom
  fraction_commutes x := by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, g.fraction_commutes, f.fraction_commutes]

end Hom

/-- Chosen finite DVR extensions and compatible embeddings form a category. -/
instance : Category (FiniteDVRExtension R K) where
  Hom := Hom
  id := Hom.refl
  comp := Hom.comp
  id_comp f := by ext <;> rfl
  comp_id f := by ext <;> rfl
  assoc f g h := by ext <;> rfl

@[simp]
lemma id_fieldHom (E : FiniteDVRExtension R K) :
    (𝟙 E : E ⟶ E).fieldHom = AlgHom.id K E.extensionField := rfl

@[simp]
lemma id_localRingHom (E : FiniteDVRExtension R K) :
    (𝟙 E : E ⟶ E).localRingHom = AlgHom.id R E.localRing := rfl

@[simp]
lemma comp_fieldHom {E F G : FiniteDVRExtension R K} (f : E ⟶ F) (g : F ⟶ G) :
    (f ≫ g).fieldHom = g.fieldHom.comp f.fieldHom := rfl

@[simp]
lemma comp_localRingHom {E F G : FiniteDVRExtension R K} (f : E ⟶ F) (g : F ⟶ G) :
    (f ≫ g).localRingHom = g.localRingHom.comp f.localRingHom := rfl

/-- A compatible extension morphism is determined by its map on selected local rings. -/
theorem Hom.ext_localRingHom {E F : FiniteDVRExtension R K} {f g : E ⟶ F}
    (hlocal : f.localRingHom = g.localRingHom) : f = g := by
  apply Hom.ext ?_ hlocal
  apply AlgHom.coe_ringHom_injective
  apply IsFractionRing.ringHom_ext (A := E.localRing)
  intro x
  change f.fieldHom (algebraMap E.localRing E.extensionField x) =
    g.fieldHom (algebraMap E.localRing E.extensionField x)
  rw [← f.fraction_commutes x, ← g.fraction_commutes x, hlocal]

/-- A compatible extension morphism is determined by its map on extension fields. -/
theorem Hom.ext_fieldHom {E F : FiniteDVRExtension R K} {f g : E ⟶ F}
    (hfield : f.fieldHom = g.fieldHom) : f = g := by
  apply Hom.ext hfield
  apply AlgHom.ext
  intro x
  apply IsFractionRing.injective F.localRing F.extensionField
  rw [f.fraction_commutes x, g.fraction_commutes x, hfield]

/-- The extension fields and their compatible embeddings form a commutative-ring-valued
functor. -/
def extensionFieldFunctor : FiniteDVRExtension R K ⥤ CommRingCat.{u} where
  obj E := .of E.extensionField
  map f := CommRingCat.ofHom f.fieldHom.toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The selected extension DVRs and their compatible local embeddings form a
commutative-ring-valued functor. -/
def localRingFunctor : FiniteDVRExtension R K ⥤ CommRingCat.{u} where
  obj E := .of E.localRing
  map f := CommRingCat.ofHom f.localRingHom.toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- Forgetting to the selected local-ring map loses no information about compatible extension
morphisms. -/
instance localRingFunctor_faithful :
    (localRingFunctor (R := R) (K := K)).Faithful where
  map_injective {X Y} f g h := by
    apply Hom.ext_localRingHom
    apply AlgHom.coe_ringHom_injective
    exact congrArg CommRingCat.Hom.hom h

/-- Forgetting to the extension-field map loses no information about compatible extension
morphisms. -/
instance extensionFieldFunctor_faithful :
    (extensionFieldFunctor (R := R) (K := K)).Faithful where
  map_injective {X Y} f g h := by
    apply Hom.ext_fieldHom
    apply AlgHom.coe_ringHom_injective
    exact congrArg CommRingCat.Hom.hom h

/-- Inclusion of each selected extension DVR into its fraction field, natural in compatible
embeddings of finite DVR extensions. -/
def localRingToExtensionFieldNatTrans :
    localRingFunctor (R := R) (K := K) ⟶ extensionFieldFunctor (R := R) (K := K) where
  app E := CommRingCat.ofHom (algebraMap E.localRing E.extensionField)
  naturality _ _ f := by
    ext x
    exact f.fraction_commutes x

/-- Data exhibiting two chosen extensions inside a common compatible refinement.

Such data always exist: see `FiniteDVRExtension.nonempty_commonRefinement` for the existence
theorem and `FiniteDVRExtension.commonRefinement` for a chosen common refinement. -/
structure CommonRefinement (E F : FiniteDVRExtension R K) where
  refinement : FiniteDVRExtension R K
  left : E ⟶ refinement
  right : F ⟶ refinement

namespace CommonRefinement

/-- An extension is a common refinement of itself. -/
def refl (E : FiniteDVRExtension R K) : CommonRefinement E E where
  refinement := E
  left := 𝟙 E
  right := 𝟙 E

/-- A compatible embedding exhibits its target as a common refinement. -/
def ofHom {E F : FiniteDVRExtension R K} (f : E ⟶ F) : CommonRefinement E F where
  refinement := F
  left := f
  right := 𝟙 F

/-- Common-refinement data are symmetric in the two inputs. -/
def swap {E F : FiniteDVRExtension R K} (P : CommonRefinement E F) :
    CommonRefinement F E where
  refinement := P.refinement
  left := P.right
  right := P.left

@[simp]
lemma swap_swap {E F : FiniteDVRExtension R K} (P : CommonRefinement E F) :
    P.swap.swap = P := rfl

/-- A common refinement remains one after a further compatible extension. -/
def postcompose {E F G : FiniteDVRExtension R K} (P : CommonRefinement E F)
    (f : P.refinement ⟶ G) : CommonRefinement E F where
  refinement := G
  left := P.left ≫ f
  right := P.right ≫ f

end CommonRefinement

end FiniteDVRExtension

/-! ### Existence of common refinements

The namespace is reopened so that the auxiliary results below can be stated with exactly the
section variables they need. -/

namespace FiniteDVRExtension

section IntegralClosureMap

variable {R : Type u} [CommRing R]

/-- The map induced on integral closures by a map of `R`-algebras. -/
def integralClosureMap {L M : Type u} [CommRing L] [CommRing M] [Algebra R L] [Algebra R M]
    (f : L →ₐ[R] M) : integralClosure R L →ₐ[R] integralClosure R M :=
  (f.comp (integralClosure R L).val).codRestrict (integralClosure R M) fun x ↦ x.2.map f

@[simp]
lemma coe_integralClosureMap {L M : Type u} [CommRing L] [CommRing M] [Algebra R L] [Algebra R M]
    (f : L →ₐ[R] M) (x : integralClosure R L) :
    ((integralClosureMap f x : integralClosure R M) : M) = f (x : L) := rfl

lemma integralClosureMap_injective {L M : Type u} [CommRing L] [CommRing M] [Algebra R L]
    [Algebra R M] {f : L →ₐ[R] M} (hf : Function.Injective f) :
    Function.Injective (integralClosureMap f) := by
  intro x y h
  apply Subtype.ext
  apply hf
  simpa using congrArg (fun z : integralClosure R M ↦ (z : M)) h

lemma integralClosureMap_comp {L M P : Type u} [CommRing L] [CommRing M] [CommRing P]
    [Algebra R L] [Algebra R M] [Algebra R P] (f : L →ₐ[R] M) (g : M →ₐ[R] P) :
    integralClosureMap (g.comp f) = (integralClosureMap g).comp (integralClosureMap f) := rfl

end IntegralClosureMap

section Compositum

variable {K : Type u} [Field K]

/-- Any two finite separable extensions of `K` embed into a common finite Galois extension of `K`:
take the normal closure of the compositum of two chosen copies inside a separable closure. -/
theorem exists_galois_compositum (L M : Type u) [Field L] [Field M] [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M] [Algebra.IsSeparable K L]
    [Algebra.IsSeparable K M] :
    ∃ (N : Type u) (_ : Field N) (_ : Algebra K N),
      ∃ (_ : FiniteDimensional K N) (_ : IsGalois K N),
        Nonempty (L →ₐ[K] N) ∧ Nonempty (M →ₐ[K] N) := by
  let Ω : Type u := separableClosure K (AlgebraicClosure K)
  let φ : L →ₐ[K] Ω := IsSepClosed.lift
  let ψ : M →ₐ[K] Ω := IsSepClosed.lift
  have hφ : FiniteDimensional K φ.fieldRange := φ.equivFieldRange.toLinearEquiv.finiteDimensional
  have hψ : FiniteDimensional K ψ.fieldRange := ψ.equivFieldRange.toLinearEquiv.finiteDimensional
  refine ⟨IntermediateField.normalClosure K ↥(φ.fieldRange ⊔ ψ.fieldRange) Ω, inferInstance,
    inferInstance, inferInstance, inferInstance, ⟨?_⟩, ⟨?_⟩⟩
  · exact (IntermediateField.inclusion
      (le_trans le_sup_left (IntermediateField.le_normalClosure _))).comp
      φ.equivFieldRange.toAlgHom
  · exact (IntermediateField.inclusion
      (le_trans le_sup_right (IntermediateField.le_normalClosure _))).comp
      ψ.equivFieldRange.toAlgHom

end Compositum

section CommonRefinements

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- A finite DVR extension assembled from an explicit finite separable extension field of `K`
together with a chosen maximal ideal of its integral closure above the closed point. -/
def ofField (N : Type u) [Field N] [Algebra K N] [Algebra R N] [IsScalarTower R K N]
    [FiniteDimensional K N] [Algebra.IsSeparable K N] (Q : Ideal (integralClosure R N))
    (hmax : Q.IsMaximal) (hover : Q.LiesOver (IsLocalRing.maximalIdeal R)) :
    FiniteDVRExtension R K where
  extension := ⟨N, inferInstance⟩
  prime := Q
  prime_isMaximal := hmax
  prime_liesOver := hover

@[simp]
lemma ofField_extensionField (N : Type u) [Field N] [Algebra K N] [Algebra R N]
    [IsScalarTower R K N] [FiniteDimensional K N] [Algebra.IsSeparable K N]
    (Q : Ideal (integralClosure R N)) (hmax : Q.IsMaximal)
    (hover : Q.LiesOver (IsLocalRing.maximalIdeal R)) :
    (ofField (R := R) (K := K) N Q hmax hover).extensionField = N := rfl

/-- A compatible embedding of chosen finite DVR extensions built from an embedding of extension
fields that pulls the selected prime of the target back to the selected prime of the source. -/
def Hom.ofFieldHom {E G : FiniteDVRExtension R K} (f : E.extensionField →ₐ[K] G.extensionField)
    (hf : E.prime = Ideal.comap (integralClosureMap (f.restrictScalars R)) G.prime) :
    E ⟶ G where
  fieldHom := f
  localRingHom :=
    Localization.localAlgHom E.prime G.prime (integralClosureMap (f.restrictScalars R)) hf
  localRingHom_isLocal := Localization.isLocalHom_localRingHom _ _ _ hf
  fraction_commutes x := by
    have h : (algebraMap G.localRing G.extensionField).comp
        (Localization.localAlgHom E.prime G.prime
          (integralClosureMap (f.restrictScalars R)) hf).toRingHom =
        f.toRingHom.comp (algebraMap E.localRing E.extensionField) := by
      refine IsLocalization.ringHom_ext E.prime.primeCompl ?_
      ext y
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, Localization.localAlgHom_apply, Localization.localRingHom_to_map,
        algebraMap_integralClosure_localRing_extensionField]
      change ((integralClosureMap (AlgHom.restrictScalars R f) y : integralClosure R _) :
        G.extensionField) = f ((y : E.extensionField))
      simp
    exact RingHom.congr_fun h x

/-- Every embedding of the extension field of a chosen finite DVR extension into a further
extension field lifts the selected prime to a maximal ideal above the closed point of `R`. -/
theorem exists_prime_over {N : Type u} [Field N] [Algebra K N] [Algebra R N] [IsScalarTower R K N]
    (E : FiniteDVRExtension R K) (f : E.extensionField →ₐ[K] N) :
    ∃ Q : Ideal (integralClosure R N), Q.IsMaximal ∧
      Q.LiesOver (IsLocalRing.maximalIdeal R) ∧
      E.prime = Ideal.comap (integralClosureMap (f.restrictScalars R)) Q := by
  let _ : Algebra E.integralClosureRing (integralClosure R N) :=
    (integralClosureMap (f.restrictScalars R)).toRingHom.toAlgebra
  have _htower : IsScalarTower R E.integralClosureRing (integralClosure R N) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      ((integralClosureMap (f.restrictScalars R)).commutes x).symm
  have _ : Algebra.IsIntegral E.integralClosureRing (integralClosure R N) :=
    Algebra.IsIntegral.tower_top (R := R)
  have hinj : Function.Injective
      (algebraMap E.integralClosureRing (integralClosure R N)) :=
    integralClosureMap_injective (f := f.restrictScalars R) f.toRingHom.injective
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (R := E.integralClosureRing) (S := integralClosure R N) E.prime
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  refine ⟨Q, hQmax, ⟨?_⟩, hQ.symm⟩
  rw [Ideal.under_def, IsScalarTower.algebraMap_eq R E.integralClosureRing (integralClosure R N),
    ← Ideal.comap_comap, hQ]
  exact E.prime_liesOver.over

open scoped Pointwise in
/-- Two primes of the integral closure of `R` in a finite Galois extension of `K` above the closed
point of `R` differ by an automorphism of the extension. -/
theorem exists_algEquiv_comap_eq {N : Type u} [Field N] [Algebra K N] [Algebra R N]
    [IsScalarTower R K N] [FiniteDimensional K N] [IsGalois K N]
    (P Q : Ideal (integralClosure R N)) [P.IsPrime] [Q.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal R)] [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    ∃ σ : N ≃ₐ[K] N,
      Ideal.comap (integralClosureMap (σ.toAlgHom.restrictScalars R)) Q = P := by
  have _ : IsFractionRing (integralClosure R N) N :=
    integralClosure.isFractionRing_of_finite_extension K N
  have _ : IsIntegralClosure (integralClosure R N) R N := integralClosure.isIntegralClosure R N
  let _ := IsIntegralClosure.MulSemiringAction R K N (integralClosure R N)
  have _ : IsGaloisGroup (N ≃ₐ[K] N) R (integralClosure R N) :=
    IsGaloisGroup.of_isFractionRing _ R (integralClosure R N) K N
  have hact : ∀ (τ : N ≃ₐ[K] N) (z : integralClosure R N),
      τ • z = integralClosureMap (τ.toAlgHom.restrictScalars R) z := by
    intro τ z
    apply Subtype.ext
    exact algebraMap_galRestrict_apply R τ z
  obtain ⟨σ, hσ⟩ :=
    Ideal.exists_smul_eq_of_isGaloisGroup (IsLocalRing.maximalIdeal R) P Q (N ≃ₐ[K] N)
  refine ⟨σ, Ideal.ext fun y ↦ ?_⟩
  rw [Ideal.mem_comap, ← hσ, Ideal.mem_pointwise_smul_iff_inv_smul_mem, hact]
  refine iff_of_eq (congrArg (· ∈ P) ?_)
  apply Subtype.ext
  simp

/-- **Existence of common refinements.** Any two chosen finite DVR extensions of the same base
DVR embed compatibly into a third one.

Both extension fields are embedded into a finite Galois extension `N` of `K`, both selected primes
are lifted to maximal ideals of the integral closure of `R` in `N` above the closed point of `R`,
and an automorphism of `N/K` carries one lift onto the other. -/
theorem nonempty_commonRefinement (E F : FiniteDVRExtension R K) :
    Nonempty (CommonRefinement E F) := by
  obtain ⟨N, _, _, _, _, ⟨i⟩, ⟨j⟩⟩ :=
    exists_galois_compositum (K := K) E.extensionField F.extensionField
  let _ : Algebra R N := ((algebraMap K N).comp (algebraMap R K)).toAlgebra
  have _ : IsScalarTower R K N := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨QE, hQEmax, hQEover, hQE⟩ := E.exists_prime_over i
  obtain ⟨QF, hQFmax, hQFover, hQF⟩ := F.exists_prime_over j
  have _ : QE.IsMaximal := hQEmax
  have _ : QF.IsMaximal := hQFmax
  have _ : QE.LiesOver (IsLocalRing.maximalIdeal R) := hQEover
  have _ : QF.LiesOver (IsLocalRing.maximalIdeal R) := hQFover
  obtain ⟨σ, hσ⟩ := exists_algEquiv_comap_eq (R := R) (K := K) QF QE
  refine ⟨{ refinement := ofField N QE hQEmax hQEover
            left := Hom.ofFieldHom i hQE
            right := Hom.ofFieldHom (σ.toAlgHom.comp j) ?_ }⟩
  change F.prime =
    Ideal.comap (integralClosureMap (AlgHom.restrictScalars R (σ.toAlgHom.comp j))) QE
  have key : Ideal.comap (integralClosureMap (AlgHom.restrictScalars R (σ.toAlgHom.comp j))) QE =
      Ideal.comap (integralClosureMap (j.restrictScalars R))
        (Ideal.comap (integralClosureMap (σ.toAlgHom.restrictScalars R)) QE) :=
    Ideal.ext fun _ ↦ Iff.rfl
  rw [key, hσ]
  exact hQF

instance (E F : FiniteDVRExtension R K) : Nonempty (CommonRefinement E F) :=
  nonempty_commonRefinement E F

/-- A chosen common refinement of two finite DVR extensions.

This replaces the previous engine hypothesis: no extra input is needed to compare two chosen
extensions, hence to compare models after a finite extension of the base DVR. -/
def commonRefinement (E F : FiniteDVRExtension R K) : CommonRefinement E F :=
  (nonempty_commonRefinement E F).some

end CommonRefinements

end FiniteDVRExtension

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction
