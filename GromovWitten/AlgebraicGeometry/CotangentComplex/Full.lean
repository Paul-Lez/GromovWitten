/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.AffinePresentation
import GromovWitten.AlgebraicGeometry.CotangentComplex.Derived
import GromovWitten.AlgebraicGeometry.Modules.Derived
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Etale.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The cotangent complex of a ring map

For a ring map `R → S` this file constructs the truncation `τ≥-1 L_{S/R}` as an actual object
`cotangentComplex R S` of `DerivedCategory (ModuleCat S)`, namely the image under the
localisation functor of the two-term presentation complex `I/I² → S ⊗ Ω[P/R]` of the canonical
polynomial presentation `Algebra.Generators.self R S`.

Everything below is a construction or a theorem; no structure in this file has a field whose
content is a result that ought to be proved.

## Main constructions and results

* `map`, `map_id`, `map_comp`: a morphism of `Algebra.Extension`s induces a chain map of
  presentation complexes, functorially.
* `homotopy`: two morphisms of extensions induce chain homotopic maps, the homotopy being
  Mathlib's `Algebra.Extension.Hom.sub`.
* `derivedMap`, `derivedMap_eq`, `derivedIso`, `derivedIso_refl`, `derivedIso_trans`: the
  induced comparison morphisms in the derived category are canonical (independent of the chosen
  morphism of extensions), and their isomorphisms are coherent.
* `cotangentComplex`, `presentationIso`, `generatorsIso`, `generatorsIso_refl`,
  `generatorsIso_trans`, `presentationIso_trans`: presentation independence as an actual
  isomorphism in the derived category, with composition and identity coherence.
* `homologyNegOneIso`, `homologyZeroIso`, `cohomologyNegOne`, `cohomologyZero`,
  `isZero_cohomology`, `hasCohomologicalAmplitude`: `H⁻¹ = H¹(L)` in Mathlib's sense, `H⁰ = Ω`,
  and vanishing elsewhere.
* `formallyUnramified_iff`, `formallySmooth_iff`, `formallyEtale_iff`,
  `formallyEtale_iff_isZero`: the smoothness/unramifiedness/étaleness criteria in terms of the
  cohomology of `L_{S/R}`.
* `isZero_cotangentComplex_of_isLocalization`: the cotangent complex of a localisation vanishes.
* `jzH1Map`, `jzDelta`, `jzBaseChange`, `jzOmegaMap` and `exact_jzH1Map_jzDelta`,
  `exact_jzDelta_jzBaseChange`, `exact_jzBaseChange_jzOmegaMap`, `surjective_jzOmegaMap`: the
  Jacobi--Zariski exact sequence for a tower `R → S → T`, transported to the cohomology of the
  cotangent complexes.
* `baseChangePresentationIso`, `cohomologyNegOneBaseChangeIso`,
  `h1CotangentBaseChangeEquivOfFlat`, `kaehlerBaseChangeEquiv`: base change.
* `cotangentExt`: the `Ext` groups of the cotangent complex.

## Not done here

The Jacobi--Zariski sequence is not yet an actual distinguished triangle, and the full
(non-truncated) simplicial cotangent complex is not constructed: Mathlib v4.33.1 has no
simplicial commutative algebras, no cotangent complex of a simplicial ring, and no
`Algebra.Extension`-level connecting morphism of complexes realising `δ`.
-/

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject TensorProduct

universe u

namespace Full

attribute [local instance] HasDerivedCategory.standard

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The two-term presentation complex of an extension, as a cochain complex in degrees
`-1` and `0`. -/
noncomputable abbrev complex (P : Algebra.Extension.{u} R S) :
    CochainComplex (ModuleCat.{u} S) ℤ :=
  AffinePresentation.cochainComplex R S P

variable {R S}

/-! ### Elementary lemmas on isomorphisms of module objects -/

section IsoLemmas

variable {T : Type u} [CommRing T] {A B : ModuleCat.{u} T}

theorem iso_hom_inv_apply (e : A ≅ B) (x : B) : e.hom.hom (e.inv.hom x) = x := by simp

theorem iso_inv_hom_apply (e : A ≅ B) (x : A) : e.inv.hom (e.hom.hom x) = x := by simp

theorem iso_hom_symm_apply (e : A ≅ B) (x : B) :
    e.hom.hom (e.toLinearEquiv.symm x) = x := by simp

theorem iso_symm_apply_eq_inv (e : A ≅ B) (x : B) :
    e.toLinearEquiv.symm x = e.inv.hom x := by simp

end IsoLemmas

section Map

variable {P P' P'' : Algebra.Extension.{u} R S}

/-- The degreewise map induced on presentation complexes by a morphism of extensions. -/
noncomputable def mapX (f : P.Hom P') (i : ℤ) :
    (complex R S P).X i ⟶ (complex R S P').X i := by
  by_cases h1 : i = -1
  · subst h1
    exact ModuleCat.ofHom (Algebra.Extension.Cotangent.map f)
  · by_cases h0 : i = 0
    · subst h0
      exact ModuleCat.ofHom (Algebra.Extension.CotangentSpace.map f)
    · exact 0

@[simp]
theorem mapX_negOne (f : P.Hom P') :
    mapX f (-1) = ModuleCat.ofHom (Algebra.Extension.Cotangent.map f) := rfl

@[simp]
theorem mapX_zero (f : P.Hom P') :
    mapX f 0 = ModuleCat.ofHom (Algebra.Extension.CotangentSpace.map f) := rfl

/-- The differential of the presentation complex from degree `-1` to degree `0`. -/
@[simp]
theorem complex_d_negOne_zero (P : Algebra.Extension.{u} R S) :
    (complex R S P).d (-1) 0 = ModuleCat.ofHom P.cotangentComplex :=
  (AffinePresentation.twoTerm R S P).toCochainComplex_d_negOne_zero

/-- Outside degree `-1` the presentation complex has vanishing differential. -/
theorem complex_d_eq_zero (P : Algebra.Extension.{u} R S) {i : ℤ} (hi : i ≠ -1) :
    (complex R S P).d i (i + 1) = 0 := by
  change CochainComplex.of.d _ _ i (i + 1) = 0
  rw [CochainComplex.of_d]
  simp only [LinearTwoTermComplex.cochainDifferential, hi, dif_neg, not_false_iff]
  rfl

/-- Terms of the presentation complex outside degrees `-1` and `0` are zero objects. -/
theorem complex_isZero (P : Algebra.Extension.{u} R S) {i : ℤ} (hi : i ≠ -1) (hi' : i ≠ 0) :
    IsZero ((complex R S P).X i) :=
  (AffinePresentation.twoTerm R S P).toCochainComplex_X_isZero i hi hi'

/-- The chain map of presentation complexes induced by a morphism of extensions. -/
noncomputable def map (f : P.Hom P') : complex R S P ⟶ complex R S P' :=
  CochainComplex.ofHom (mapX f) (by
    intro i
    by_cases h1 : i = -1
    · subst h1
      rw [show (-1 : ℤ) + 1 = 0 by ring]
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      exact (Algebra.Extension.CotangentSpace.map_cotangentComplex f x).symm
    · rw [complex_d_eq_zero _ h1, complex_d_eq_zero _ h1, Limits.comp_zero, Limits.zero_comp])

@[simp]
theorem map_f_negOne (f : P.Hom P') :
    (map f).f (-1) = ModuleCat.ofHom (Algebra.Extension.Cotangent.map f) := rfl

@[simp]
theorem map_f_zero (f : P.Hom P') :
    (map f).f 0 = ModuleCat.ofHom (Algebra.Extension.CotangentSpace.map f) := rfl

@[simp]
theorem map_id : map (Algebra.Extension.Hom.id P) = 𝟙 (complex R S P) := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases h1 : i = -1
  · subst h1
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact congrFun (congrArg DFunLike.coe (Algebra.Extension.Cotangent.map_id (P := P))) x
  · by_cases h0 : i = 0
    · subst h0
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      exact congrFun (congrArg DFunLike.coe
        (Algebra.Extension.CotangentSpace.map_id (P := P))) x
    · exact (complex_isZero P h1 h0).eq_of_src _ _

theorem map_comp (f : P.Hom P') (g : P'.Hom P'') :
    map (g.comp f) = map f ≫ map g := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases h1 : i = -1
  · subst h1
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact congrFun (congrArg DFunLike.coe (Algebra.Extension.Cotangent.map_comp P'' f g)) x
  · by_cases h0 : i = 0
    · subst h0
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      exact Algebra.Extension.CotangentSpace.map_comp_apply f g x
    · exact (complex_isZero P h1 h0).eq_of_src _ _

/-! ### The homotopy between the maps induced by two morphisms of extensions -/

/-- The degreewise homotopy datum attached to a pair of morphisms of extensions.  It is
Mathlib's difference map `Algebra.Extension.Hom.sub` in bidegree `(0, -1)` and zero
elsewhere. -/
noncomputable def homotopyX (f g : P.Hom P') (i j : ℤ) :
    (complex R S P).X i ⟶ (complex R S P').X j :=
  if h : i = 0 ∧ j = -1 then
    cast (by rw [h.1, h.2]; rfl) (ModuleCat.ofHom (Algebra.Extension.Hom.sub f g))
  else 0

theorem homotopyX_eq_zero (f g : P.Hom P') {i j : ℤ} (h : ¬(i = 0 ∧ j = -1)) :
    homotopyX f g i j = 0 :=
  dif_neg h

@[simp]
theorem homotopyX_zero_negOne (f g : P.Hom P') :
    homotopyX f g 0 (-1) = ModuleCat.ofHom (Algebra.Extension.Hom.sub f g) := rfl

/-- Two morphisms of extensions induce homotopic maps of presentation complexes; the homotopy
is Mathlib's difference map `Algebra.Extension.Hom.sub`. -/
noncomputable def homotopy (f g : P.Hom P') : Homotopy (map f) (map g) where
  hom := homotopyX f g
  zero i j hij := by
    refine homotopyX_eq_zero f g ?_
    rintro ⟨rfl, rfl⟩
    exact hij (by simp)
  comm i := by
    by_cases h1 : i = -1
    · subst h1
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (-2) (-1) by simp),
        homotopyX_eq_zero (i := (-1 : ℤ)) (j := (-2 : ℤ)) f g (by rintro ⟨h, -⟩; omega),
        Limits.zero_comp, add_zero]
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      have hx : Algebra.Extension.Cotangent.map f x - Algebra.Extension.Cotangent.map g x =
          Algebra.Extension.Hom.sub f g (P.cotangentComplex x) :=
        congrFun (congrArg DFunLike.coe (Algebra.Extension.Cotangent.map_sub_map f g)) x
      exact sub_eq_iff_eq_add.mp hx
    · by_cases h0 : i = 0
      · subst h0
        rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp),
          prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp),
          homotopyX_eq_zero (i := (1 : ℤ)) (j := (0 : ℤ)) f g (by rintro ⟨h, -⟩; omega),
          Limits.comp_zero, zero_add]
        refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
        have hx : Algebra.Extension.CotangentSpace.map f x -
            Algebra.Extension.CotangentSpace.map g x =
              P'.cotangentComplex (Algebra.Extension.Hom.sub f g x) :=
          congrFun (congrArg DFunLike.coe
            (Algebra.Extension.CotangentSpace.map_sub_map f g)) x
        exact sub_eq_iff_eq_add.mp hx
      · exact (complex_isZero P h1 h0).eq_of_src _ _

/-! ### Homotopy equivalences and the derived comparison -/

/-- Homotopic maps of cochain complexes become equal in the derived category. -/
theorem Q_map_eq_of_homotopy {K L : CochainComplex (ModuleCat.{u} S) ℤ} {a b : K ⟶ L}
    (H : Homotopy a b) : DerivedCategory.Q.map a = DerivedCategory.Q.map b := by
  have h1 := DerivedCategory.quotientCompQhIso_hom_naturality (C := ModuleCat.{u} S) a
  have h2 := DerivedCategory.quotientCompQhIso_hom_naturality (C := ModuleCat.{u} S) b
  rw [HomotopyCategory.eq_of_homotopy a b H, h2] at h1
  exact (cancel_epi ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} S)).hom.app K)).mp h1.symm

/-- A pair of morphisms of extensions in opposite directions gives a homotopy equivalence of
presentation complexes. -/
noncomputable def homotopyEquiv (f : P.Hom P') (g : P'.Hom P) :
    HomotopyEquiv (complex R S P) (complex R S P') where
  hom := map f
  inv := map g
  homotopyHomInvId :=
    ((Homotopy.ofEq (map_comp f g).symm).trans
      (homotopy (g.comp f) (Algebra.Extension.Hom.id P))).trans (Homotopy.ofEq map_id)
  homotopyInvHomId :=
    ((Homotopy.ofEq (map_comp g f).symm).trans
      (homotopy (f.comp g) (Algebra.Extension.Hom.id P'))).trans (Homotopy.ofEq map_id)

/-- If there are morphisms of extensions in both directions, the induced map of presentation
complexes is a quasi-isomorphism. -/
theorem quasiIso_map (f : P.Hom P') (g : P'.Hom P) : QuasiIso (map f) :=
  (homotopyEquiv f g).quasiIso_hom

/-- Any two morphisms of extensions induce the same morphism of derived objects: the
comparison of presentations is canonical. -/
theorem Q_map_map_eq (f g : P.Hom P') :
    DerivedCategory.Q.map (map f) = DerivedCategory.Q.map (map g) :=
  Q_map_eq_of_homotopy (homotopy f g)

/-- The canonical comparison morphism of derived objects attached to a morphism of
extensions. -/
noncomputable def derivedMap (f : P.Hom P') :
    AffinePresentation.derivedObject R S P ⟶ AffinePresentation.derivedObject R S P' :=
  DerivedCategory.Q.map (map f)

@[simp]
theorem derivedMap_id : derivedMap (Algebra.Extension.Hom.id P) =
    𝟙 (AffinePresentation.derivedObject R S P) := by
  rw [derivedMap, map_id, CategoryTheory.Functor.map_id]
  rfl

theorem derivedMap_comp (f : P.Hom P') (g : P'.Hom P'') :
    derivedMap (g.comp f) = derivedMap f ≫ derivedMap g := by
  change DerivedCategory.Q.map (map (g.comp f)) = _
  rw [map_comp, CategoryTheory.Functor.map_comp]
  rfl

/-- The comparison morphism does not depend on the chosen morphism of extensions. -/
theorem derivedMap_eq (f g : P.Hom P') : derivedMap f = derivedMap g :=
  Q_map_map_eq f g

/-- The comparison isomorphism of derived objects attached to a pair of morphisms of
extensions in opposite directions. -/
@[simps]
noncomputable def derivedIso (f : P.Hom P') (g : P'.Hom P) :
    AffinePresentation.derivedObject R S P ≅ AffinePresentation.derivedObject R S P' where
  hom := derivedMap f
  inv := derivedMap g
  hom_inv_id := by
    rw [← derivedMap_comp, derivedMap_eq (g.comp f) (Algebra.Extension.Hom.id P), derivedMap_id]
  inv_hom_id := by
    rw [← derivedMap_comp, derivedMap_eq (f.comp g) (Algebra.Extension.Hom.id P'), derivedMap_id]

/-- The comparison isomorphism is independent of the chosen morphisms of extensions. -/
theorem derivedIso_eq (f f' : P.Hom P') (g g' : P'.Hom P) :
    derivedIso f g = derivedIso f' g' :=
  Iso.ext (derivedMap_eq f f')

/-- The comparison isomorphism of a presentation with itself is the identity. -/
theorem derivedIso_refl :
    derivedIso (Algebra.Extension.Hom.id P) (Algebra.Extension.Hom.id P) = Iso.refl _ :=
  Iso.ext derivedMap_id

/-- The comparison isomorphisms compose. -/
theorem derivedIso_trans (f : P.Hom P') (g : P'.Hom P) (f' : P'.Hom P'') (g' : P''.Hom P') :
    derivedIso f g ≪≫ derivedIso f' g' = derivedIso (f'.comp f) (g.comp g') :=
  Iso.ext (derivedMap_comp f f').symm

/-- The comparison isomorphisms are inverse to each other. -/
theorem derivedIso_symm (f : P.Hom P') (g : P'.Hom P) :
    (derivedIso f g).symm = derivedIso g f :=
  rfl

end Map

/-! ### Cohomology of the presentation complex -/

section Homology

variable (P : Algebra.Extension.{u} R S)

/-- The short complex of the presentation complex around degree `-1`. -/
noncomputable abbrev scNegOne : ShortComplex (ModuleCat.{u} S) :=
  (complex R S P).sc' (-2) (-1) 0

/-- The short complex of the presentation complex around degree `0`. -/
noncomputable abbrev scZero : ShortComplex (ModuleCat.{u} S) :=
  (complex R S P).sc' (-1) 0 1

theorem scNegOne_f_eq_zero : (scNegOne P).f = 0 :=
  (complex_isZero (i := (-2 : ℤ)) P (by decide) (by decide)).eq_of_src _ _

theorem scZero_g_eq_zero : (scZero P).g = 0 :=
  (complex_isZero (i := (1 : ℤ)) P (by decide) (by decide)).eq_of_tgt _ _

theorem range_moduleCatToCycles_scNegOne :
    LinearMap.range (scNegOne P).moduleCatToCycles = ⊥ := by
  rw [LinearMap.range_eq_bot]
  refine LinearMap.ext fun x => Subtype.ext ?_
  change ((scNegOne P).f).hom x = 0
  rw [scNegOne_f_eq_zero]
  rfl

theorem ker_scZero_g : LinearMap.ker (scZero P).g.hom = ⊤ := by
  rw [scZero_g_eq_zero]
  exact LinearMap.ker_zero

/-- Degree `-1` cohomology of the presentation complex is Mathlib's `H¹` of the cotangent
complex of the presentation. -/
noncomputable def homologyNegOneIso :
    (complex R S P).homology (-1) ≅ ModuleCat.of S P.H1Cotangent :=
  (complex R S P).homologyIsoSc' (-2) (-1) 0 (by simp) (by simp) ≪≫
    (scNegOne P).moduleCatHomologyIso ≪≫
    LinearEquiv.toModuleIso
      (Submodule.quotEquivOfEqBot _ (range_moduleCatToCycles_scNegOne P))

/-- The canonical identification of the degree-zero cycles of the presentation complex with the
ambient cotangent space. -/
noncomputable def scZeroKerEquiv :
    ↥(LinearMap.ker (scZero P).g.hom) ≃ₗ[S] P.CotangentSpace :=
  (LinearEquiv.ofEq _ _ (ker_scZero_g P)).trans Submodule.topEquiv

theorem map_range_moduleCatToCycles_scZero :
    Submodule.map (scZeroKerEquiv P : _ →ₗ[S] P.CotangentSpace)
        (LinearMap.range (scZero P).moduleCatToCycles) =
      LinearMap.range P.cotangentComplex := by
  rw [← LinearMap.range_comp]
  rfl

/-- The image of the presentation differential is the kernel of the map to Kähler
differentials. -/
theorem range_cotangentComplex_eq_ker_toKaehler :
    LinearMap.range P.cotangentComplex = LinearMap.ker P.toKaehler :=
  (LinearMap.exact_iff.mp P.exact_cotangentComplex_toKaehler).symm

/-- The degree-zero homology of the presentation complex is the module of Kähler
differentials. -/
noncomputable def scZeroHomologyEquiv :
    (↥(LinearMap.ker (scZero P).g.hom) ⧸ LinearMap.range (scZero P).moduleCatToCycles)
      ≃ₗ[S] Ω[S⁄R] :=
  (Submodule.Quotient.equiv _ _ (scZeroKerEquiv P) (map_range_moduleCatToCycles_scZero P)).trans
    ((Submodule.quotEquivOfEq _ _ (range_cotangentComplex_eq_ker_toKaehler P)).trans
      (P.toKaehler.quotKerEquivOfSurjective P.toKaehler_surjective))

/-- Degree `0` cohomology of the presentation complex is the module of Kähler
differentials. -/
noncomputable def homologyZeroIso :
    (complex R S P).homology 0 ≅ ModuleCat.of S Ω[S⁄R] :=
  (complex R S P).homologyIsoSc' (-1) 0 1 (by simp) (by simp) ≪≫
    (scZero P).moduleCatHomologyIso ≪≫ LinearEquiv.toModuleIso (scZeroHomologyEquiv P)

/-- Outside degrees `-1` and `0` the presentation complex is acyclic. -/
theorem isZero_homology (n : ℤ) (hn : n ≠ -1) (hn' : n ≠ 0) :
    Limits.IsZero ((complex R S P).homology n) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    (ShortComplex.exact_of_isZero_X₂ _ (complex_isZero P hn hn'))

end Homology

/-! ### The cotangent complex of a ring map -/

section Canonical

variable (R S)

/-- The canonical presentation of `S` over `R` by all of its elements. -/
noncomputable abbrev selfExtension : Algebra.Extension.{u} R S :=
  (Algebra.Generators.self R S).toExtension

/-- The cotangent complex `L_{S/R}` of a ring map, in its `τ≥-1` truncation, as an actual
object of the derived category of `S`-modules.  It is the presentation complex of the
canonical presentation of `S` by all of its elements; `presentationIso` shows that the
choice of presentation is irrelevant. -/
noncomputable def cotangentComplex : DerivedCategory (ModuleCat.{u} S) :=
  AffinePresentation.derivedObject R S (selfExtension R S)

variable {R S}

/-- The `n`-th cohomology of a derived object of `T`-modules. -/
noncomputable abbrev cohomology {T : Type u} [CommRing T]
    (E : DerivedCategory (ModuleCat.{u} T)) (n : ℤ) : ModuleCat.{u} T :=
  (Modules.Derived.cohomologyFunctor (ModuleCat.{u} T) n).obj E

/-- The canonical comparison morphism from the cotangent complex to the derived object of an
arbitrary presentation, induced by Mathlib's `Algebra.Extension.defaultHom`. -/
noncomputable def comparePresentation (P : Algebra.Extension.{u} R S) :
    cotangentComplex R S ⟶ AffinePresentation.derivedObject R S P :=
  derivedMap (Algebra.Extension.defaultHom R S P)

variable {ι ι' ι'' : Type u}

/-- The comparison isomorphism between the derived objects of two polynomial presentations. -/
noncomputable def generatorsIso (P : Algebra.Generators R S ι) (P' : Algebra.Generators R S ι') :
    AffinePresentation.derivedObject R S P.toExtension ≅
      AffinePresentation.derivedObject R S P'.toExtension :=
  derivedIso (Algebra.Generators.defaultHom P P').toExtensionHom
    (Algebra.Generators.defaultHom P' P).toExtensionHom

/-- The comparison isomorphism of a presentation with itself is the identity. -/
theorem generatorsIso_refl (P : Algebra.Generators R S ι) : generatorsIso P P = Iso.refl _ :=
  (derivedIso_eq _ _ _ _).trans derivedIso_refl

/-- The comparison isomorphisms of polynomial presentations compose. -/
theorem generatorsIso_trans (P : Algebra.Generators R S ι) (P' : Algebra.Generators R S ι')
    (P'' : Algebra.Generators R S ι'') :
    generatorsIso P P' ≪≫ generatorsIso P' P'' = generatorsIso P P'' :=
  (derivedIso_trans _ _ _ _).trans (derivedIso_eq _ _ _ _)

/-- The comparison isomorphisms of polynomial presentations are mutually inverse. -/
theorem generatorsIso_symm (P : Algebra.Generators R S ι) (P' : Algebra.Generators R S ι') :
    (generatorsIso P P').symm = generatorsIso P' P :=
  rfl

/-- The cotangent complex is canonically isomorphic to the derived object of any polynomial
presentation: the construction is independent of the presentation. -/
noncomputable def presentationIso (P : Algebra.Generators R S ι) :
    cotangentComplex R S ≅ AffinePresentation.derivedObject R S P.toExtension :=
  generatorsIso (Algebra.Generators.self R S) P

/-- The presentation-independence isomorphism is the canonical comparison morphism. -/
theorem presentationIso_hom (P : Algebra.Generators R S ι) :
    (presentationIso P).hom = comparePresentation P.toExtension :=
  derivedMap_eq _ _

/-- The presentation-independence isomorphisms are coherent: they compose. -/
theorem presentationIso_trans (P : Algebra.Generators R S ι) (P' : Algebra.Generators R S ι') :
    (presentationIso P).symm ≪≫ presentationIso P' = generatorsIso P P' := by
  have h : (generatorsIso (Algebra.Generators.self R S) P).symm ≪≫
      generatorsIso (Algebra.Generators.self R S) P' = generatorsIso P P' := by
    rw [generatorsIso_symm, generatorsIso_trans]
  exact h

/-- The presentation-independence isomorphism for the canonical presentation is the
identity. -/
theorem presentationIso_self :
    presentationIso (Algebra.Generators.self R S) = Iso.refl (cotangentComplex R S) :=
  generatorsIso_refl _

end Canonical

/-! ### Cohomology of the cotangent complex -/

section CohomologyCanonical

/-- Cohomology of the derived object of a presentation is the homology of the presentation
complex. -/
noncomputable def derivedHomologyIso (P : Algebra.Extension.{u} R S) (n : ℤ) :
    cohomology (AffinePresentation.derivedObject R S P) n ≅ (complex R S P).homology n :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S) n).app (complex R S P)

/-- Degree `-1` cohomology of the derived object of a presentation. -/
noncomputable def cohomologyNegOneIso (P : Algebra.Extension.{u} R S) :
    cohomology (AffinePresentation.derivedObject R S P) (-1) ≅
      ModuleCat.of S P.H1Cotangent :=
  derivedHomologyIso P (-1) ≪≫ homologyNegOneIso P

/-- Degree `0` cohomology of the derived object of a presentation. -/
noncomputable def cohomologyZeroIso (P : Algebra.Extension.{u} R S) :
    cohomology (AffinePresentation.derivedObject R S P) 0 ≅ ModuleCat.of S Ω[S⁄R] :=
  derivedHomologyIso P 0 ≪≫ homologyZeroIso P

/-- The derived object of a presentation has cohomological amplitude `[-1, 0]`. -/
theorem isZero_cohomology_presentation (P : Algebra.Extension.{u} R S) (n : ℤ)
    (hn : n ≠ -1) (hn' : n ≠ 0) :
    Limits.IsZero (cohomology (AffinePresentation.derivedObject R S P) n) :=
  Limits.IsZero.of_iso (isZero_homology P n hn hn') (derivedHomologyIso P n)

variable (R S)

/-- `H⁻¹(L_{S/R})` is Mathlib's `H¹` of the cotangent complex. -/
noncomputable def cohomologyNegOne :
    cohomology (cotangentComplex R S) (-1) ≅ ModuleCat.of S (Algebra.H1Cotangent R S) :=
  cohomologyNegOneIso (selfExtension R S)

/-- `H⁰(L_{S/R})` is the module of Kähler differentials. -/
noncomputable def cohomologyZero :
    cohomology (cotangentComplex R S) 0 ≅ ModuleCat.of S Ω[S⁄R] :=
  cohomologyZeroIso (selfExtension R S)

/-- The cotangent complex has cohomological amplitude `[-1, 0]`. -/
theorem isZero_cohomology (n : ℤ) (hn : n ≠ -1) (hn' : n ≠ 0) :
    Limits.IsZero (cohomology (cotangentComplex R S) n) :=
  isZero_cohomology_presentation (selfExtension R S) n hn hn'

/-- The cotangent complex has cohomological amplitude `[-1,0]` in the sense of
`CotangentComplex.HasCohomologicalAmplitude`. -/
theorem hasCohomologicalAmplitude :
    HasCohomologicalAmplitude (cotangentComplex R S) (-1) 0 := by
  intro i hi
  refine isZero_cohomology R S i ?_ ?_ <;> rintro rfl <;> omega

end CohomologyCanonical

/-! ### Smoothness, unramifiedness and étaleness criteria -/

section Criteria

variable (R S)

/-- Vanishing of `H⁰(L_{S/R})` is vanishing of the module of Kähler differentials. -/
theorem isZero_cohomologyZero_iff :
    Limits.IsZero (cohomology (cotangentComplex R S) 0) ↔ Subsingleton (Ω[S⁄R]) :=
  ((cohomologyZero R S).isZero_iff).trans ModuleCat.isZero_iff_subsingleton

/-- Vanishing of `H⁻¹(L_{S/R})` is vanishing of Mathlib's `H¹` of the cotangent complex. -/
theorem isZero_cohomologyNegOne_iff :
    Limits.IsZero (cohomology (cotangentComplex R S) (-1)) ↔
      Subsingleton (Algebra.H1Cotangent R S) :=
  ((cohomologyNegOne R S).isZero_iff).trans ModuleCat.isZero_iff_subsingleton

/-- Formal unramifiedness is the vanishing of `H⁰(L_{S/R})`. -/
theorem formallyUnramified_iff :
    Algebra.FormallyUnramified R S ↔ Limits.IsZero (cohomology (cotangentComplex R S) 0) :=
  (Algebra.formallyUnramified_iff R S).trans (isZero_cohomologyZero_iff R S).symm

/-- Formal smoothness is projectivity of `H⁰(L_{S/R})` together with the vanishing of
`H⁻¹(L_{S/R})`. -/
theorem formallySmooth_iff :
    Algebra.FormallySmooth R S ↔
      Module.Projective S (cohomology (cotangentComplex R S) 0) ∧
        Limits.IsZero (cohomology (cotangentComplex R S) (-1)) := by
  rw [Algebra.formallySmooth_iff, isZero_cohomologyNegOne_iff]
  refine and_congr (Iff.intro (fun h => ?_) (fun h => ?_)) Iff.rfl
  · exact Module.Projective.of_equiv' (M := Ω[S⁄R]) (cohomologyZero R S).toLinearEquiv.symm
  · exact Module.Projective.of_equiv' (cohomologyZero R S).toLinearEquiv

/-- Formal étaleness is the vanishing of both cohomology groups of `L_{S/R}`. -/
theorem formallyEtale_iff :
    Algebra.FormallyEtale R S ↔
      Limits.IsZero (cohomology (cotangentComplex R S) 0) ∧
        Limits.IsZero (cohomology (cotangentComplex R S) (-1)) := by
  rw [Algebra.formallyEtale_iff, isZero_cohomologyZero_iff, isZero_cohomologyNegOne_iff]

/-- Formal étaleness is the vanishing of the whole cotangent complex. -/
theorem formallyEtale_iff_forall_isZero :
    Algebra.FormallyEtale R S ↔
      ∀ n : ℤ, Limits.IsZero (cohomology (cotangentComplex R S) n) := by
  rw [formallyEtale_iff]
  refine ⟨fun h n => ?_, fun h => ⟨h 0, h (-1)⟩⟩
  by_cases hn : n = -1
  · exact hn ▸ h.2
  · by_cases hn' : n = 0
    · exact hn' ▸ h.1
    · exact isZero_cohomology R S n hn hn'

/-- An acyclic complex has zero image in the derived category. -/
theorem isZero_Q_obj {K : CochainComplex (ModuleCat.{u} S) ℤ}
    (h : ∀ n : ℤ, Limits.IsZero (K.homology n)) :
    Limits.IsZero (DerivedCategory.Q.obj K) := by
  have hzero : Limits.IsZero (0 : CochainComplex (ModuleCat.{u} S) ℤ) := Limits.isZero_zero _
  have hQ : ∀ n : ℤ,
      Limits.IsZero ((0 : CochainComplex (ModuleCat.{u} S) ℤ).homology n) := fun n =>
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℤ) n).map_isZero hzero
  set φ : (0 : CochainComplex (ModuleCat.{u} S) ℤ) ⟶ K := 0 with hφ
  have hqi : QuasiIso φ := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap,
      (hQ n).eq_of_src (HomologicalComplex.homologyMap φ n) ((hQ n).iso (h n)).hom]
    infer_instance
  have : IsIso (DerivedCategory.Q.map φ) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ φ).mpr hqi
  exact (DerivedCategory.Q.map_isZero hzero).of_iso (asIso (DerivedCategory.Q.map φ)).symm

/-- The cotangent complex vanishes exactly when the algebra is formally étale. -/
theorem formallyEtale_iff_isZero :
    Algebra.FormallyEtale R S ↔ Limits.IsZero (cotangentComplex R S) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine isZero_Q_obj S fun n => ?_
    refine Limits.IsZero.of_iso ?_ (derivedHomologyIso (selfExtension R S) n).symm
    exact (formallyEtale_iff_forall_isZero R S).mp h n
  · refine (formallyEtale_iff_forall_isZero R S).mpr fun n => ?_
    exact (Modules.Derived.cohomologyFunctor (ModuleCat.{u} S) n).map_isZero h

end Criteria

/-! ### Localization -/

section Localization

variable (R S) (T : Type u) [CommRing T] [Algebra S T]

/-- The cotangent complex of a localization vanishes. -/
theorem isZero_cotangentComplex_of_isLocalization (M : Submonoid S) [IsLocalization M T] :
    Limits.IsZero (cotangentComplex S T) :=
  (formallyEtale_iff_isZero S T).mp (Algebra.FormallyEtale.of_isLocalization M)

/-- All cohomology of the cotangent complex of a localization vanishes. -/
theorem isZero_cohomology_of_isLocalization (M : Submonoid S) [IsLocalization M T] (n : ℤ) :
    Limits.IsZero (cohomology (cotangentComplex S T) n) :=
  (Modules.Derived.cohomologyFunctor (ModuleCat.{u} T) n).map_isZero
    (isZero_cotangentComplex_of_isLocalization S T M)

end Localization

/-! ### The Jacobi--Zariski sequence -/

section JacobiZariski

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- The first map `H⁻¹(L_{T/R}) ⟶ H⁻¹(L_{T/S})` of the Jacobi--Zariski sequence. -/
noncomputable def jzH1Map :
    cohomology (cotangentComplex R T) (-1) ⟶ cohomology (cotangentComplex S T) (-1) :=
  (cohomologyNegOne R T).hom ≫ ModuleCat.ofHom (Algebra.H1Cotangent.map R S T T) ≫
    (cohomologyNegOne S T).inv

/-- The Jacobi--Zariski connecting map `H⁻¹(L_{T/S}) ⟶ T ⊗[S] H⁰(L_{S/R})`. -/
noncomputable def jzDelta :
    cohomology (cotangentComplex S T) (-1) ⟶ ModuleCat.of T (T ⊗[S] Ω[S⁄R]) :=
  (cohomologyNegOne S T).hom ≫ ModuleCat.ofHom (Algebra.H1Cotangent.δ R S T)

/-- The map `T ⊗[S] H⁰(L_{S/R}) ⟶ H⁰(L_{T/R})` of the Jacobi--Zariski sequence. -/
noncomputable def jzBaseChange :
    ModuleCat.of T (T ⊗[S] Ω[S⁄R]) ⟶ cohomology (cotangentComplex R T) 0 :=
  ModuleCat.ofHom (KaehlerDifferential.mapBaseChange R S T) ≫ (cohomologyZero R T).inv

/-- The last map `H⁰(L_{T/R}) ⟶ H⁰(L_{T/S})` of the Jacobi--Zariski sequence. -/
noncomputable def jzOmegaMap :
    cohomology (cotangentComplex R T) 0 ⟶ cohomology (cotangentComplex S T) 0 :=
  (cohomologyZero R T).hom ≫ ModuleCat.ofHom (KaehlerDifferential.map R S T T) ≫
    (cohomologyZero S T).inv

/-- Exactness of the Jacobi--Zariski sequence at `H⁻¹(L_{T/S})`. -/
theorem exact_jzH1Map_jzDelta :
    Function.Exact (jzH1Map R S T).hom (jzDelta R S T).hom := by
  refine Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := (cohomologyNegOne R T).toLinearEquiv.symm)
    (e₂ := (cohomologyNegOne S T).toLinearEquiv.symm)
    (e₃ := LinearEquiv.refl T (T ⊗[S] Ω[S⁄R])) ?_ ?_
    (Algebra.H1Cotangent.exact_map_δ R S T)
  · refine LinearMap.ext fun x => ?_
    simp only [jzH1Map, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    rw [iso_hom_symm_apply, iso_symm_apply_eq_inv]
  · refine LinearMap.ext fun x => ?_
    simp only [jzDelta, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearEquiv.refl_apply]
    rw [iso_hom_symm_apply]

/-- Exactness of the Jacobi--Zariski sequence at `T ⊗[S] H⁰(L_{S/R})`. -/
theorem exact_jzDelta_jzBaseChange :
    Function.Exact (jzDelta R S T).hom (jzBaseChange R S T).hom := by
  refine Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := (cohomologyNegOne S T).toLinearEquiv.symm)
    (e₂ := LinearEquiv.refl T (T ⊗[S] Ω[S⁄R]))
    (e₃ := (cohomologyZero R T).toLinearEquiv.symm) ?_ ?_
    (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T)
  · refine LinearMap.ext fun x => ?_
    simp only [jzDelta, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearEquiv.refl_apply]
    rw [iso_hom_symm_apply]
  · refine LinearMap.ext fun x => ?_
    simp only [jzBaseChange, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearEquiv.refl_apply]
    rw [iso_symm_apply_eq_inv]

/-- Exactness of the Jacobi--Zariski sequence at `H⁰(L_{T/R})`. -/
theorem exact_jzBaseChange_jzOmegaMap :
    Function.Exact (jzBaseChange R S T).hom (jzOmegaMap R S T).hom := by
  refine Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := LinearEquiv.refl T (T ⊗[S] Ω[S⁄R]))
    (e₂ := (cohomologyZero R T).toLinearEquiv.symm)
    (e₃ := (cohomologyZero S T).toLinearEquiv.symm) ?_ ?_
    (KaehlerDifferential.exact_mapBaseChange_map R S T)
  · refine LinearMap.ext fun x => ?_
    simp only [jzBaseChange, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearEquiv.refl_apply]
    rw [iso_symm_apply_eq_inv]
  · refine LinearMap.ext fun x => ?_
    simp only [jzOmegaMap, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    rw [iso_hom_symm_apply, iso_symm_apply_eq_inv]

/-- The Jacobi--Zariski sequence ends in a surjection onto `H⁰(L_{T/S})`. -/
theorem surjective_jzOmegaMap : Function.Surjective (jzOmegaMap R S T).hom := by
  intro y
  obtain ⟨x, hx⟩ := KaehlerDifferential.map_surjective R S T ((cohomologyZero S T).hom.hom y)
  refine ⟨(cohomologyZero R T).inv.hom x, ?_⟩
  simp only [jzOmegaMap, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
    Function.comp_apply]
  rw [iso_hom_inv_apply, hx, iso_inv_hom_apply]

end JacobiZariski

/-! ### Base change -/

section BaseChange

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (T : Type u) [CommRing T] [Algebra R T]
variable {ι : Type u}

/-- The base change of a polynomial presentation computes the cotangent complex of the base
changed algebra: this is derived base change for the two-term truncation. -/
noncomputable def baseChangePresentationIso (P : Algebra.Generators R S ι) :
    AffinePresentation.derivedObject T (T ⊗[R] S) (P.toExtension.baseChange (T := T)) ≅
      cotangentComplex T (T ⊗[R] S) :=
  derivedIso (P.baseChangeFromBaseChange T) (P.baseChangeToBaseChange T) ≪≫
    (presentationIso (P.baseChange (T := T))).symm

/-- `H⁻¹(L_{(T⊗S)/T})` computed from the base change of the canonical presentation. -/
noncomputable def cohomologyNegOneBaseChangeIso :
    cohomology (cotangentComplex T (T ⊗[R] S)) (-1) ≅
      ModuleCat.of (T ⊗[R] S) ((selfExtension R S).baseChange (T := T)).H1Cotangent :=
  (Modules.Derived.cohomologyFunctor (ModuleCat.{u} (T ⊗[R] S)) (-1)).mapIso
      (baseChangePresentationIso R S T (Algebra.Generators.self R S)).symm ≪≫
    cohomologyNegOneIso ((selfExtension R S).baseChange (T := T))

/-- Flat base change: `H⁻¹(L_{(T⊗S)/T})` is obtained from `H⁻¹(L_{S/R})` by extension of
scalars along `R → T`. -/
noncomputable def h1CotangentBaseChangeEquivOfFlat [Module.Flat R T] :
    (T ⊗[R] Algebra.H1Cotangent R S) ≃ₗ[T]
      ((selfExtension R S).baseChange (T := T)).H1Cotangent :=
  AffinePresentation.tensorHNegOneOfFlat R S (selfExtension R S) T

section Kaehler

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Base change for `H⁰`: `Ω_{(T⊗S)/T}` is obtained from `Ω_{S/R}` by extension of scalars
along `R → T`.  Combined with `cohomologyZero` this computes `H⁰(L_{(T⊗S)/T})`. -/
noncomputable def kaehlerBaseChangeEquiv :
    (T ⊗[R] Ω[S⁄R]) ≃ₗ[T] Ω[(T ⊗[R] S)⁄T] :=
  KaehlerDifferential.tensorKaehlerEquivBase R T S (T ⊗[R] S)

end Kaehler

end BaseChange

/-! ### `Ext` groups of the cotangent complex -/

section Ext

variable (R S)

/-- A module regarded as an object of the derived category, concentrated in degree zero. -/
noncomputable def moduleObject (M : ModuleCat.{u} S) : DerivedCategory (ModuleCat.{u} S) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj M

/-- The group `Extⁿ(L_{S/R}, M)` of the cotangent complex with coefficients in an `S`-module.
Affine deformation theory (`CotangentComplex.SquareZero`) expects its degree-one part. -/
noncomputable abbrev cotangentExt (M : ModuleCat.{u} S) (n : ℤ) : Type _ :=
  DerivedExt (cotangentComplex R S) (moduleObject S M) n

/-- All `Ext` groups of the cotangent complex of a formally étale algebra vanish. -/
theorem subsingleton_cotangentExt_of_formallyEtale [Algebra.FormallyEtale R S]
    (M : ModuleCat.{u} S) (n : ℤ) : Subsingleton (cotangentExt R S M n) :=
  ⟨fun a b => ((formallyEtale_iff_isZero R S).mp inferInstance).eq_of_src a b⟩

end Ext

end Full

end GromovWitten.AlgebraicGeometry.CotangentComplex
