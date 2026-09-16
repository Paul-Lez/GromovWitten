/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Morphisms.Unramified
import GromovWitten.AlgebraicGeometry.Morphisms.Syntomic
import GromovWitten.AlgebraicGeometry.Spaces.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Representable properties of algebraic-space morphisms

Every property in this file is the transfer, through the fppf Yoneda embedding, of the existing
scheme-morphism property.  Thus a single base-change definition controls the scheme and
algebraic-space APIs.  The generic identity, composition, and isomorphism lemmas below are shared
by all the named properties.
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

namespace AlgebraicSpace

/-- Representably smooth morphisms of algebraic spaces. -/
abbrev Smooth : MorphismProperty AlgebraicSpace.{u} :=
  HasRepresentableProperty
    (@_root_.AlgebraicGeometry.Smooth : MorphismProperty _root_.AlgebraicGeometry.Scheme.{u})

/-- Representably flat morphisms of algebraic spaces. -/
abbrev Flat : MorphismProperty AlgebraicSpace.{u} :=
  HasRepresentableProperty
    (@_root_.AlgebraicGeometry.Flat : MorphismProperty _root_.AlgebraicGeometry.Scheme.{u})

/-- Representably unramified morphisms of algebraic spaces. -/
abbrev Unramified : MorphismProperty AlgebraicSpace.{u} :=
  HasRepresentableProperty
    (@GromovWitten.AlgebraicGeometry.Unramified :
      MorphismProperty _root_.AlgebraicGeometry.Scheme.{u})

/-- Representably proper morphisms of algebraic spaces. -/
abbrev Proper : MorphismProperty AlgebraicSpace.{u} :=
  HasRepresentableProperty
    (@_root_.AlgebraicGeometry.IsProper : MorphismProperty _root_.AlgebraicGeometry.Scheme.{u})

/-- Representably separated morphisms of algebraic spaces. -/
abbrev Separated : MorphismProperty AlgebraicSpace.{u} :=
  HasRepresentableProperty
    (@_root_.AlgebraicGeometry.IsSeparated : MorphismProperty _root_.AlgebraicGeometry.Scheme.{u})

/-- Representably locally-finite-type morphisms of algebraic spaces. -/
abbrev LocallyOfFiniteType : MorphismProperty AlgebraicSpace.{u} :=
  HasRepresentableProperty
    (@_root_.AlgebraicGeometry.LocallyOfFiniteType :
      MorphismProperty _root_.AlgebraicGeometry.Scheme.{u})

/-- Representably locally-finitely-presented morphisms of algebraic spaces. -/
abbrev LocallyOfFinitePresentation : MorphismProperty AlgebraicSpace.{u} :=
  HasRepresentableProperty
    (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation :
      MorphismProperty _root_.AlgebraicGeometry.Scheme.{u})

/-- Representably quasi-compact morphisms of algebraic spaces. -/
abbrev QuasiCompact : MorphismProperty AlgebraicSpace.{u} :=
  HasRepresentableProperty
    (@_root_.AlgebraicGeometry.QuasiCompact : MorphismProperty _root_.AlgebraicGeometry.Scheme.{u})

/-- Representably finite-type morphisms: quasi-compact and locally of finite type. -/
abbrev FiniteType : MorphismProperty AlgebraicSpace.{u} :=
  QuasiCompact ⊓ LocallyOfFiniteType

/-- Representably finite-presentation morphisms: quasi-compact and locally finitely
presented. -/
abbrev FinitePresentation : MorphismProperty AlgebraicSpace.{u} :=
  QuasiCompact ⊓ LocallyOfFinitePresentation

/-- Representable immersions of algebraic spaces. -/
abbrev Immersion : MorphismProperty AlgebraicSpace.{u} :=
  HasRepresentableProperty
    (@_root_.AlgebraicGeometry.IsImmersion : MorphismProperty _root_.AlgebraicGeometry.Scheme.{u})

/-- Local immersions use Mathlib's scheme immersion predicate after every scheme base change. -/
abbrev LocalImmersion : MorphismProperty AlgebraicSpace.{u} :=
  Immersion

/-- Representable open immersions of algebraic spaces. -/
abbrev OpenImmersion : MorphismProperty AlgebraicSpace.{u} :=
  HasRepresentableProperty
    (@_root_.AlgebraicGeometry.IsOpenImmersion :
      MorphismProperty _root_.AlgebraicGeometry.Scheme.{u})

/-- Representable closed immersions of algebraic spaces. -/
abbrev ClosedImmersion : MorphismProperty AlgebraicSpace.{u} :=
  HasRepresentableProperty
    (@_root_.AlgebraicGeometry.IsClosedImmersion :
      MorphismProperty _root_.AlgebraicGeometry.Scheme.{u})

/-- Regular immersions are closed local-complete-intersection morphisms after every scheme
base change. -/
abbrev RegularImmersion : MorphismProperty AlgebraicSpace.{u} :=
  HasRepresentableProperty
    ((@_root_.AlgebraicGeometry.IsClosedImmersion ⊓
      @GromovWitten.AlgebraicGeometry.LocallyCompleteIntersection) :
      MorphismProperty _root_.AlgebraicGeometry.Scheme.{u})

/-- An open algebraic subspace of `X`, represented by its actual inclusion morphism. -/
structure OpenSubspace (X : AlgebraicSpace.{u}) where
  carrier : AlgebraicSpace.{u}
  inclusion : carrier ⟶ X
  isOpen : OpenImmersion inclusion

/-- A closed algebraic subspace of `X`, represented by its actual inclusion morphism. -/
structure ClosedSubspace (X : AlgebraicSpace.{u}) where
  carrier : AlgebraicSpace.{u}
  inclusion : carrier ⟶ X
  isClosed : ClosedImmersion inclusion

namespace OpenSubspace

/-- An open immersion of schemes determines an open subspace after applying the fully faithful
scheme-to-space embedding.  Openness is transferred by the proved Yoneda base-change
comparison, rather than supplied separately at the algebraic-space level. -/
noncomputable def ofScheme {U X : _root_.AlgebraicGeometry.Scheme.{u}} (j : U ⟶ X)
    (hj : _root_.AlgebraicGeometry.IsOpenImmersion j) :
    OpenSubspace (AlgebraicSpace.ofScheme.obj X) where
  carrier := AlgebraicSpace.ofScheme.obj U
  inclusion := AlgebraicSpace.ofScheme.map j
  isOpen := (AlgebraicSpace.ofScheme_map_hasRepresentableProperty_iff
    (@_root_.AlgebraicGeometry.IsOpenImmersion :
      MorphismProperty _root_.AlgebraicGeometry.Scheme.{u})).2 hj

@[simp]
theorem ofScheme_carrier {U X : _root_.AlgebraicGeometry.Scheme.{u}} (j : U ⟶ X)
    (hj : _root_.AlgebraicGeometry.IsOpenImmersion j) :
    (ofScheme j hj).carrier = AlgebraicSpace.ofScheme.obj U :=
  rfl

@[simp]
theorem ofScheme_inclusion {U X : _root_.AlgebraicGeometry.Scheme.{u}} (j : U ⟶ X)
    (hj : _root_.AlgebraicGeometry.IsOpenImmersion j) :
    (ofScheme j hj).inclusion = AlgebraicSpace.ofScheme.map j :=
  rfl

end OpenSubspace

namespace ClosedSubspace

/-- A closed immersion of schemes determines a closed subspace after applying the fully faithful
scheme-to-space embedding. -/
noncomputable def ofScheme {Z X : _root_.AlgebraicGeometry.Scheme.{u}} (j : Z ⟶ X)
    (hj : _root_.AlgebraicGeometry.IsClosedImmersion j) :
    ClosedSubspace (AlgebraicSpace.ofScheme.obj X) where
  carrier := AlgebraicSpace.ofScheme.obj Z
  inclusion := AlgebraicSpace.ofScheme.map j
  isClosed := (AlgebraicSpace.ofScheme_map_hasRepresentableProperty_iff
    (@_root_.AlgebraicGeometry.IsClosedImmersion :
      MorphismProperty _root_.AlgebraicGeometry.Scheme.{u})).2 hj

@[simp]
theorem ofScheme_carrier {Z X : _root_.AlgebraicGeometry.Scheme.{u}} (j : Z ⟶ X)
    (hj : _root_.AlgebraicGeometry.IsClosedImmersion j) :
    (ofScheme j hj).carrier = AlgebraicSpace.ofScheme.obj Z :=
  rfl

@[simp]
theorem ofScheme_inclusion {Z X : _root_.AlgebraicGeometry.Scheme.{u}} (j : Z ⟶ X)
    (hj : _root_.AlgebraicGeometry.IsClosedImmersion j) :
    (ofScheme j hj).inclusion = AlgebraicSpace.ofScheme.map j :=
  rfl

end ClosedSubspace

/-- A representable property containing identities transfers identities to algebraic spaces. -/
theorem hasRepresentableProperty_id
    (P : MorphismProperty _root_.AlgebraicGeometry.Scheme.{u})
    [P.IsMultiplicative] [P.RespectsIso] (X : AlgebraicSpace.{u}) :
    HasRepresentableProperty P (𝟙 X) := by
  change P.relative fppfYoneda (𝟙 X.toSheaf)
  exact MorphismProperty.id_mem _ _

/-- A composition-stable representable property transfers composition to algebraic spaces. -/
theorem hasRepresentableProperty_comp
    (P : MorphismProperty _root_.AlgebraicGeometry.Scheme.{u})
    [P.IsStableUnderComposition]
    {X Y Z : AlgebraicSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasRepresentableProperty P f) (hg : HasRepresentableProperty P g) :
    HasRepresentableProperty P (f ≫ g) := by
  exact MorphismProperty.comp_mem (P.relative fppfYoneda) f.hom g.hom hf hg

/-- Representable properties are preserved by every cartesian base change of algebraic spaces.
The square is stated explicitly, so this theorem applies before a global pullback constructor for
algebraic spaces has been chosen. -/
theorem hasRepresentableProperty_of_isPullback
    (P : MorphismProperty _root_.AlgebraicGeometry.Scheme.{u})
    {X Y Y' S : AlgebraicSpace.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f'.hom g'.hom g.hom f.hom)
    (hg : HasRepresentableProperty P g) :
    HasRepresentableProperty P g' := by
  exact (MorphismProperty.relative_isStableUnderBaseChange P).of_isPullback
    sq hg

/-- The first projection from the constructed pullback inherits every representable property
of the second leg by base change. -/
theorem hasRepresentableProperty_pullback_fst
    (P : MorphismProperty _root_.AlgebraicGeometry.Scheme.{u})
    {X Y S : AlgebraicSpace.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (hg : HasRepresentableProperty P g) :
    HasRepresentableProperty P (Limits.pullback.fst f g) := by
  exact hasRepresentableProperty_of_isPullback P
    ((IsPullback.of_hasPullback f g).map forget).flip hg

/-- The second projection from the constructed pullback inherits every representable property
of the first leg by base change. -/
theorem hasRepresentableProperty_pullback_snd
    (P : MorphismProperty _root_.AlgebraicGeometry.Scheme.{u})
    {X Y S : AlgebraicSpace.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (hf : HasRepresentableProperty P f) :
    HasRepresentableProperty P (Limits.pullback.snd f g) := by
  exact hasRepresentableProperty_of_isPullback P
    ((IsPullback.of_hasPullback f g).map forget) hf

namespace OpenSubspace

/-- The inverse image of an open subspace along an arbitrary algebraic-space morphism.  Its
carrier is the categorical pullback and its inclusion is the actual second projection. -/
noncomputable def pullback {X Y : AlgebraicSpace.{u}} (U : OpenSubspace X) (f : Y ⟶ X) :
    OpenSubspace Y where
  carrier := Limits.pullback U.inclusion f
  inclusion := Limits.pullback.snd U.inclusion f
  isOpen := hasRepresentableProperty_pullback_snd
    (@_root_.AlgebraicGeometry.IsOpenImmersion :
      MorphismProperty _root_.AlgebraicGeometry.Scheme.{u}) U.inclusion f U.isOpen

/-- The inverse-image subspace maps canonically to the original subspace. -/
noncomputable def pullbackToCarrier {X Y : AlgebraicSpace.{u}} (U : OpenSubspace X)
    (f : Y ⟶ X) : (U.pullback f).carrier ⟶ U.carrier :=
  Limits.pullback.fst U.inclusion f

/-- The square defining the inverse image of an open subspace is cartesian. -/
theorem pullback_isPullback {X Y : AlgebraicSpace.{u}} (U : OpenSubspace X) (f : Y ⟶ X) :
    IsPullback (U.pullbackToCarrier f) (U.pullback f).inclusion U.inclusion f :=
  IsPullback.of_hasPullback U.inclusion f

/-- Scheme-theoretic and algebraic-space inverse images of an open immersion have canonically
isomorphic carriers.  This is the pullback comparison of the fully faithful scheme embedding. -/
noncomputable def pullbackOfSchemeCarrierIso
    {U X Y : _root_.AlgebraicGeometry.Scheme.{u}} (j : U ⟶ X) (f : Y ⟶ X)
    (hj : _root_.AlgebraicGeometry.IsOpenImmersion j) :
    ((ofScheme j hj).pullback (AlgebraicSpace.ofScheme.map f)).carrier ≅
      AlgebraicSpace.ofScheme.obj (Limits.pullback j f) :=
  (PreservesPullback.iso AlgebraicSpace.ofScheme j f).symm

/-- The scheme-comparison isomorphism respects the projection to the original open subspace. -/
theorem pullbackOfSchemeCarrierIso_hom_fst
    {U X Y : _root_.AlgebraicGeometry.Scheme.{u}} (j : U ⟶ X) (f : Y ⟶ X)
    (hj : _root_.AlgebraicGeometry.IsOpenImmersion j) :
    (pullbackOfSchemeCarrierIso j f hj).hom ≫
        AlgebraicSpace.ofScheme.map (Limits.pullback.fst j f) =
      (ofScheme j hj).pullbackToCarrier (AlgebraicSpace.ofScheme.map f) := by
  change (PreservesPullback.iso AlgebraicSpace.ofScheme j f).inv ≫
      AlgebraicSpace.ofScheme.map (Limits.pullback.fst j f) =
    Limits.pullback.fst (AlgebraicSpace.ofScheme.map j) (AlgebraicSpace.ofScheme.map f)
  exact PreservesPullback.iso_inv_fst AlgebraicSpace.ofScheme j f

/-- The scheme-comparison isomorphism respects the inclusion in the base scheme. -/
theorem pullbackOfSchemeCarrierIso_hom_snd
    {U X Y : _root_.AlgebraicGeometry.Scheme.{u}} (j : U ⟶ X) (f : Y ⟶ X)
    (hj : _root_.AlgebraicGeometry.IsOpenImmersion j) :
    (pullbackOfSchemeCarrierIso j f hj).hom ≫
        AlgebraicSpace.ofScheme.map (Limits.pullback.snd j f) =
      ((ofScheme j hj).pullback (AlgebraicSpace.ofScheme.map f)).inclusion := by
  change (PreservesPullback.iso AlgebraicSpace.ofScheme j f).inv ≫
      AlgebraicSpace.ofScheme.map (Limits.pullback.snd j f) =
    Limits.pullback.snd (AlgebraicSpace.ofScheme.map j) (AlgebraicSpace.ofScheme.map f)
  exact PreservesPullback.iso_inv_snd AlgebraicSpace.ofScheme j f

end OpenSubspace

namespace ClosedSubspace

/-- The inverse image of a closed subspace along an arbitrary algebraic-space morphism. -/
noncomputable def pullback {X Y : AlgebraicSpace.{u}} (Z : ClosedSubspace X) (f : Y ⟶ X) :
    ClosedSubspace Y where
  carrier := Limits.pullback Z.inclusion f
  inclusion := Limits.pullback.snd Z.inclusion f
  isClosed := hasRepresentableProperty_pullback_snd
    (@_root_.AlgebraicGeometry.IsClosedImmersion :
      MorphismProperty _root_.AlgebraicGeometry.Scheme.{u}) Z.inclusion f Z.isClosed

/-- The inverse-image subspace maps canonically to the original subspace. -/
noncomputable def pullbackToCarrier {X Y : AlgebraicSpace.{u}} (Z : ClosedSubspace X)
    (f : Y ⟶ X) : (Z.pullback f).carrier ⟶ Z.carrier :=
  Limits.pullback.fst Z.inclusion f

/-- The square defining the inverse image of a closed subspace is cartesian. -/
theorem pullback_isPullback {X Y : AlgebraicSpace.{u}} (Z : ClosedSubspace X) (f : Y ⟶ X) :
    IsPullback (Z.pullbackToCarrier f) (Z.pullback f).inclusion Z.inclusion f :=
  IsPullback.of_hasPullback Z.inclusion f

/-- Scheme-theoretic and algebraic-space inverse images of a closed immersion have canonically
isomorphic carriers. -/
noncomputable def pullbackOfSchemeCarrierIso
    {Z X Y : _root_.AlgebraicGeometry.Scheme.{u}} (j : Z ⟶ X) (f : Y ⟶ X)
    (hj : _root_.AlgebraicGeometry.IsClosedImmersion j) :
    ((ofScheme j hj).pullback (AlgebraicSpace.ofScheme.map f)).carrier ≅
      AlgebraicSpace.ofScheme.obj (Limits.pullback j f) :=
  (PreservesPullback.iso AlgebraicSpace.ofScheme j f).symm

/-- The closed-subspace comparison isomorphism respects the projection to the original
subspace. -/
theorem pullbackOfSchemeCarrierIso_hom_fst
    {Z X Y : _root_.AlgebraicGeometry.Scheme.{u}} (j : Z ⟶ X) (f : Y ⟶ X)
    (hj : _root_.AlgebraicGeometry.IsClosedImmersion j) :
    (pullbackOfSchemeCarrierIso j f hj).hom ≫
        AlgebraicSpace.ofScheme.map (Limits.pullback.fst j f) =
      (ofScheme j hj).pullbackToCarrier (AlgebraicSpace.ofScheme.map f) := by
  change (PreservesPullback.iso AlgebraicSpace.ofScheme j f).inv ≫
      AlgebraicSpace.ofScheme.map (Limits.pullback.fst j f) =
    Limits.pullback.fst (AlgebraicSpace.ofScheme.map j) (AlgebraicSpace.ofScheme.map f)
  exact PreservesPullback.iso_inv_fst AlgebraicSpace.ofScheme j f

/-- The closed-subspace comparison isomorphism respects the inclusion in the base scheme. -/
theorem pullbackOfSchemeCarrierIso_hom_snd
    {Z X Y : _root_.AlgebraicGeometry.Scheme.{u}} (j : Z ⟶ X) (f : Y ⟶ X)
    (hj : _root_.AlgebraicGeometry.IsClosedImmersion j) :
    (pullbackOfSchemeCarrierIso j f hj).hom ≫
        AlgebraicSpace.ofScheme.map (Limits.pullback.snd j f) =
      ((ofScheme j hj).pullback (AlgebraicSpace.ofScheme.map f)).inclusion := by
  change (PreservesPullback.iso AlgebraicSpace.ofScheme j f).inv ≫
      AlgebraicSpace.ofScheme.map (Limits.pullback.snd j f) =
    Limits.pullback.snd (AlgebraicSpace.ofScheme.map j) (AlgebraicSpace.ofScheme.map f)
  exact PreservesPullback.iso_inv_snd AlgebraicSpace.ofScheme j f

end ClosedSubspace

set_option linter.style.haveILetI false in
/-- A representable property respecting isomorphisms holds on every algebraic-space
isomorphism. -/
theorem hasRepresentableProperty_of_isIso
    (P : MorphismProperty _root_.AlgebraicGeometry.Scheme.{u})
    [P.IsMultiplicative] [P.RespectsIso]
    {X Y : AlgebraicSpace.{u}} (f : X ⟶ Y) [IsIso f] :
    HasRepresentableProperty P f := by
  change P.relative fppfYoneda (forget.map f)
  haveI : IsIso (forget.map f) := Functor.map_isIso forget f
  exact (P.relative fppfYoneda).of_isIso _

end AlgebraicSpace

end GromovWitten.AlgebraicGeometry
