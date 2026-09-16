/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.Algebraic
import GromovWitten.AlgebraicGeometry.Stacks.Discrete
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Schemes as groupoid-valued stacks

The fppf sheaf represented by a scheme is promoted to a stack of discrete groupoids using the
effective-descent theorem in `Stacks.Discrete`.  Morphisms are promoted to strong
transformations.  Conversely, every strong transformation between two such stacks determines
a unique scheme morphism, and the reconstructed strong transformation is connected to the
original one by an invertible modification.  This is the bicategorical fully-faithful statement
for schemes required by the stack foundation.
-/

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace GromovWitten.AlgebraicGeometry

universe u

namespace FppfStack

/-- A sheaf of types on the fppf site as a stack of discrete groupoids. -/
noncomputable def ofSheaf (P : FppfSheaf.{u}) : FppfStack.{u} :=
  StackInGroupoids.ofSheafOfTypes
    (_root_.AlgebraicGeometry.Scheme.fppfTopology : GrothendieckTopology Scheme.{u}) P

/-- The representable fppf stack associated to a scheme. -/
noncomputable def ofScheme (X : Scheme.{u}) : FppfStack.{u} :=
  ofSheaf (fppfYoneda.obj X)

/-- The induced bicategory on fppf stacks, specialized to the universes used by
`FppfStack`.  Its 1-morphisms are strong transformations and its 2-morphisms are
modifications. -/
abbrev FppfBicategory :=
  StackBicategory.{u, u, u + 1, u} Scheme.{u}
    (_root_.AlgebraicGeometry.Scheme.fppfTopology : GrothendieckTopology Scheme.{u})

/-- View an fppf stack as an object of its induced bicategory. -/
def asBicategory (X : FppfStack.{u}) : FppfBicategory.{u} := X

/-- The representable stack associated to a scheme, viewed as an object of the full bicategory
of fppf stacks. -/
noncomputable def ofSchemeObj (X : Scheme.{u}) : FppfBicategory.{u} :=
  asBicategory (ofScheme X)

/-- A morphism of fppf sheaves induces a strong morphism of their discrete stacks. -/
def mapOfSheafHom {P Q : FppfSheaf.{u}} (η : P ⟶ Q) :
    StackHom (ofSheaf P) (ofSheaf Q) :=
  Pseudofunctor.strongTransOfNatTrans η.hom

/-- A scheme morphism induces a strong morphism between its representable stacks. -/
def mapOfSchemeHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    StackHom (ofScheme X) (ofScheme Y) :=
  mapOfSheafHom (fppfYoneda.map f)

/-- Extract the unique sheaf morphism represented by a strong morphism of discrete stacks. -/
def sheafHomOfMap {P Q : FppfSheaf.{u}}
    (η : StackHom (ofSheaf P) (ofSheaf Q)) : P ⟶ Q :=
  ObjectProperty.homMk (Pseudofunctor.natTransOfStrongTrans η)

/-- Extract the unique scheme morphism represented by a strong morphism of representable
stacks. -/
noncomputable def schemeHomOfMap {X Y : Scheme.{u}}
    (η : StackHom (ofScheme X) (ofScheme Y)) : X ⟶ Y :=
  fppfYoneda.preimage (sheafHomOfMap η)

/-- Extracting the scheme map of a promoted scheme morphism recovers the original map. -/
@[simp]
theorem schemeHomOfMap_mapOfSchemeHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    schemeHomOfMap (mapOfSchemeHom f) = f := by
  apply fppfYoneda.map_injective
  change fppfYoneda.map (fppfYoneda.preimage _) = _
  rw [fppfYoneda.map_preimage]
  apply ObjectProperty.hom_ext
  exact Pseudofunctor.natTransOfStrongTrans_strongTransOfNatTrans _

/-- The scheme morphism extracted from the identity strong transformation is the identity. -/
@[simp]
theorem schemeHomOfMap_id (X : Scheme.{u}) :
    schemeHomOfMap
      (Pseudofunctor.StrongTrans.id (ofScheme X).toPseudofunctor) = 𝟙 X := by
  apply fppfYoneda.map_injective
  change fppfYoneda.map (fppfYoneda.preimage _) = fppfYoneda.map (𝟙 X)
  rw [fppfYoneda.map_preimage]
  apply ObjectProperty.hom_ext
  ext T f
  rfl

/-- Every strong morphism between representable discrete stacks is invertibly 2-isomorphic to
the one obtained from its unique underlying scheme morphism. -/
def mapOfSchemeHom_schemeHomOfMap_iso {X Y : Scheme.{u}}
    (η : StackHom (ofScheme X) (ofScheme Y)) :
    StackIso2 (mapOfSchemeHom (schemeHomOfMap η)) η := by
  rw [mapOfSchemeHom, schemeHomOfMap, mapOfSheafHom,
    fppfYoneda.map_preimage]
  exact {
    hom := Pseudofunctor.discreteCounitHom η
    inv := Pseudofunctor.discreteCounitInv η
    hom_inv_id := (Pseudofunctor.discreteCounitIso2 η).hom_inv_id
    inv_hom_id := (Pseudofunctor.discreteCounitIso2 η).inv_hom_id }

/-- Promotion of the identity scheme morphism is invertibly 2-isomorphic to the identity stack
morphism. -/
noncomputable def mapOfSchemeHom_id_iso (X : Scheme.{u}) :
    StackIso2 (mapOfSchemeHom (𝟙 X))
      (Pseudofunctor.StrongTrans.id (ofScheme X).toPseudofunctor) := by
  simpa only [schemeHomOfMap_id] using
    mapOfSchemeHom_schemeHomOfMap_iso
      (Pseudofunctor.StrongTrans.id (ofScheme X).toPseudofunctor)

/-- The representable-stack embedding is faithful even after allowing invertible
2-morphisms: 2-isomorphic promoted maps are equal as scheme morphisms. -/
theorem mapOfSchemeHom_injective_up_to_iso {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (e : StackIso2 (mapOfSchemeHom f) (mapOfSchemeHom g)) : f = g := by
  apply fppfYoneda.map_injective
  apply ObjectProperty.hom_ext
  exact Pseudofunctor.natTransOfStrongTrans_eq_of_modification e.hom

private theorem schemeHom_vcomp_mapOfSchemeHom {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    schemeHomOfMap
      (Pseudofunctor.StrongTrans.vcomp (mapOfSchemeHom f) (mapOfSchemeHom g)) =
        f ≫ g := by
  apply fppfYoneda.map_injective
  change fppfYoneda.map (fppfYoneda.preimage _) = fppfYoneda.map (f ≫ g)
  rw [fppfYoneda.map_preimage]
  apply ObjectProperty.hom_ext
  ext T x
  rfl

/-- Promotion of a composite scheme morphism agrees, by an invertible modification, with the
composite of the promoted morphisms. -/
noncomputable def mapOfSchemeHom_comp_iso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp (mapOfSchemeHom f) (mapOfSchemeHom g))
      (mapOfSchemeHom (f ≫ g)) := by
  let c := Pseudofunctor.StrongTrans.vcomp (mapOfSchemeHom f) (mapOfSchemeHom g)
  have e := mapOfSchemeHom_schemeHomOfMap_iso c
  rw [schemeHom_vcomp_mapOfSchemeHom f g] at e
  exact e.symm

/-- Regard a directly constructed invertible modification as an isomorphism in the hom-category
of the induced bicategory of fppf stacks. -/
def stackIso2ToBicategoryIso
    {X Y : FppfStack.{u}} {f g : StackHom X Y} (e : StackIso2 f g) :
    InducedBicategory.mkHom f ≅
      (InducedBicategory.mkHom g : asBicategory X ⟶ asBicategory Y) where
  hom := InducedBicategory.mkHom₂ (Pseudofunctor.StrongTrans.Hom.of e.hom)
  inv := InducedBicategory.mkHom₂ (Pseudofunctor.StrongTrans.Hom.of e.inv)
  hom_inv_id := by
    apply InducedBicategory.hom₂_ext
    apply Pseudofunctor.StrongTrans.Hom.ext
    exact e.hom_inv_id
  inv_hom_id := by
    apply InducedBicategory.hom₂_ext
    apply Pseudofunctor.StrongTrans.Hom.ext
    exact e.inv_hom_id

/-- Modifications between arbitrary strong transformations of representable discrete stacks are
unique when they exist.  The proof uses only discreteness of representable fibres. -/
theorem schemeModification_subsingleton {X Y : Scheme.{u}}
    (f g : ofSchemeObj X ⟶ ofSchemeObj Y) : Subsingleton (f ⟶ g) :=
  ⟨fun m n ↦ by
    apply InducedBicategory.hom₂_ext
    apply Pseudofunctor.StrongTrans.homCategory.ext
    intro a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    change @Eq (ULift (PLift (_ = _))) _ _
    exact Subsingleton.elim _ _⟩

/-- On every pair of schemes, the Yoneda promotion maps their discrete morphism category into
the full hom-category of strong transformations and modifications. -/
noncomputable def schemeHomFunctor (X Y : Scheme.{u}) :
    Discrete (X ⟶ Y) ⥤ (ofSchemeObj X ⟶ ofSchemeObj Y) where
  obj f := InducedBicategory.mkHom (mapOfSchemeHom f.as)
  map {f g} m := by
    exact eqToHom (InducedBicategory.hom_ext
      (congrArg mapOfSchemeHom (Discrete.eq_of_hom m)))
  map_id := by
    intro f
    apply (schemeModification_subsingleton _ _).elim
  map_comp := by
    intro f g h m n
    apply (schemeModification_subsingleton _ _).elim

/-- The local scheme-to-stack hom functor is fully faithful at the modification level. -/
noncomputable def schemeHomFunctorFullyFaithful (X Y : Scheme.{u}) :
    (schemeHomFunctor X Y).FullyFaithful where
  preimage {f g} m := Discrete.eqToHom (by
    apply fppfYoneda.map_injective
    apply ObjectProperty.hom_ext
    exact Pseudofunctor.natTransOfStrongTrans_eq_of_modification m.hom.as)
  map_preimage {f g} m := (schemeModification_subsingleton _ _).elim _ _
  preimage_map {f g} m := Subsingleton.elim _ _

theorem schemeHomFunctorEssSurj (X Y : Scheme.{u}) :
    (schemeHomFunctor X Y).EssSurj where
  mem_essImage η :=
    ⟨Discrete.mk (schemeHomOfMap η.hom),
      ⟨stackIso2ToBicategoryIso
        (mapOfSchemeHom_schemeHomOfMap_iso η.hom)⟩⟩

/-- Yoneda promotion induces an equivalence from the discrete category of scheme morphisms to
the complete hom-category between their representable fppf stacks. -/
noncomputable def schemeHomEquivalence (X Y : Scheme.{u}) :
    Discrete (X ⟶ Y) ≌ (ofSchemeObj X ⟶ ofSchemeObj Y) := by
  let F := schemeHomFunctor X Y
  letI : F.IsEquivalence :=
    { faithful := (schemeHomFunctorFullyFaithful X Y).faithful
      full := (schemeHomFunctorFullyFaithful X Y).full
      essSurj := schemeHomFunctorEssSurj X Y }
  exact F.asEquivalence

/-- Schemes embed into fppf stacks by a bundled pseudofunctor.  Its unitor, compositor, and all
coherence laws are built from Yoneda and the proved uniqueness of modifications between
representable discrete stacks. -/
noncomputable def schemeEmbedding :
    LocallyDiscrete Scheme.{u} ⥤ᵖ FppfBicategory.{u} :=
  LocallyDiscrete.mkPseudofunctor
    ofSchemeObj
    (fun f ↦ InducedBicategory.mkHom (mapOfSchemeHom f))
    (fun X ↦ stackIso2ToBicategoryIso (mapOfSchemeHom_id_iso X))
    (fun f g ↦ stackIso2ToBicategoryIso (mapOfSchemeHom_comp_iso f g).symm)
    (by
      intro X Y Z W f g h
      apply (schemeModification_subsingleton _ _).elim)
    (by
      intro X Y f
      apply (schemeModification_subsingleton _ _).elim)
    (by
      intro X Y f
      apply (schemeModification_subsingleton _ _).elim)

private theorem schemeHom_vcomp_iso_hom_inv {X Y : Scheme.{u}} (e : X ≅ Y) :
    schemeHomOfMap
      (Pseudofunctor.StrongTrans.vcomp
        (mapOfSchemeHom e.hom) (mapOfSchemeHom e.inv)) = 𝟙 X := by
  apply fppfYoneda.map_injective
  change fppfYoneda.map (fppfYoneda.preimage _) = fppfYoneda.map (𝟙 X)
  rw [fppfYoneda.map_preimage]
  apply ObjectProperty.hom_ext
  ext T f
  change (f ≫ e.hom) ≫ e.inv = f
  rw [Category.assoc, e.hom_inv_id, Category.comp_id]

private theorem schemeHom_vcomp_iso_inv_hom {X Y : Scheme.{u}} (e : X ≅ Y) :
    schemeHomOfMap
      (Pseudofunctor.StrongTrans.vcomp
        (mapOfSchemeHom e.inv) (mapOfSchemeHom e.hom)) = 𝟙 Y := by
  apply fppfYoneda.map_injective
  change fppfYoneda.map (fppfYoneda.preimage _) = fppfYoneda.map (𝟙 Y)
  rw [fppfYoneda.map_preimage]
  apply ObjectProperty.hom_ext
  ext T f
  change (f ≫ e.inv) ≫ e.hom = f
  rw [Category.assoc, e.inv_hom_id, Category.comp_id]

/-- A scheme isomorphism induces an equivalence of the corresponding representable fppf
stacks.  Both inverse 2-cells are constructed from the Yoneda image of the actual inverse laws. -/
noncomputable def stackEquivalenceOfSchemeIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    StackEquivalenceData (ofScheme X) (ofScheme Y) where
  hom := mapOfSchemeHom e.hom
  inv := mapOfSchemeHom e.inv
  homInv := by
    let c := Pseudofunctor.StrongTrans.vcomp
      (mapOfSchemeHom e.hom) (mapOfSchemeHom e.inv)
    have h := mapOfSchemeHom_schemeHomOfMap_iso c
    rw [schemeHom_vcomp_iso_hom_inv e] at h
    exact h.symm.trans (mapOfSchemeHom_id_iso X)
  invHom := by
    let c := Pseudofunctor.StrongTrans.vcomp
      (mapOfSchemeHom e.inv) (mapOfSchemeHom e.hom)
    have h := mapOfSchemeHom_schemeHomOfMap_iso c
    rw [schemeHom_vcomp_iso_inv_hom e] at h
    exact h.symm.trans (mapOfSchemeHom_id_iso Y)

/-- The identity chart of the representable stack of a scheme. -/
noncomputable def schemeChart (X : Scheme.{u}) : StackChart (ofScheme X) where
  scheme := X
  map := mapOfSchemeHom (𝟙 X)

/-- Every base change of the identity chart is represented by the test scheme itself. -/
noncomputable def schemeChartPullbackPresentation (X T : Scheme.{u})
    (x : StackFiber (ofScheme X) T) :
    (schemeChart X).PullbackPresentation T x where
  space := T
  fst := 𝟙 T
  snd := x.as
  comparison := Discrete.eqToIso (by
    change x.as = (𝟙 T) ≫ x.as
    simp)
  lift toBase toChart comparison := toBase
  lift_fst toBase toChart comparison := by simp
  lift_snd toBase toChart comparison := by
    change toBase ≫ x.as = toChart
    exact (Discrete.eq_of_hom comparison.hom).symm
  lift_compatible toBase toChart comparison := by
    refine ⟨by simp, ?_, ?_⟩
    · change toBase ≫ x.as = toChart
      exact (Discrete.eq_of_hom comparison.hom).symm
    · apply Iso.ext
      change @Eq (ULift (PLift (_ = _))) _ _
      apply Subsingleton.elim
  lift_unique toBase toChart comparison m compatible := by
    obtain ⟨hm₁, -, -⟩ := compatible
    simpa using hm₁

/-- Every presentation of a base change of the identity chart is canonically isomorphic to the
test scheme.  The inverse is the presentation's classifying map for the test object; both inverse
laws follow from the full universal property, including its comparison 2-cell. -/
noncomputable def schemeChartPullbackPresentationIso (X T : Scheme.{u})
    (x : StackFiber (ofScheme X) T)
    (p : (schemeChart X).PullbackPresentation T x) : p.space ≅ T := by
  let q := schemeChartPullbackPresentation X T x
  let inv : T ⟶ p.space := p.lift q.fst q.snd q.comparison
  have hinv_fst : inv ≫ p.fst = q.fst := by
    exact p.lift_fst q.fst q.snd q.comparison
  have hinv_snd : inv ≫ p.snd = q.snd := by
    exact p.lift_snd q.fst q.snd q.comparison
  have hpEq : p.snd = p.fst ≫ x.as :=
    Discrete.eq_of_hom p.comparison.hom
  have hidCompatible :
      (schemeChart X).Classifies p.fst p.snd p.comparison
        p.fst p.snd p.comparison (𝟙 p.space) := by
    refine ⟨by simp, by simp, ?_⟩
    apply Iso.ext
    change @Eq (ULift (PLift (_ = _))) _ _
    apply Subsingleton.elim
  have hcompCompatible :
      (schemeChart X).Classifies p.fst p.snd p.comparison
        p.fst p.snd p.comparison (p.fst ≫ inv) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Category.assoc, hinv_fst]
      simp only [q, schemeChartPullbackPresentation, Category.comp_id]
    · rw [Category.assoc, hinv_snd]
      change p.fst ≫ x.as = p.snd
      exact hpEq.symm
    · apply Iso.ext
      change @Eq (ULift (PLift (_ = _))) _ _
      apply Subsingleton.elim
  have hid := p.lift_unique p.fst p.snd p.comparison
    (𝟙 p.space) hidCompatible
  have hcomp := p.lift_unique p.fst p.snd p.comparison
    (p.fst ≫ inv) hcompCompatible
  exact
    { hom := p.fst
      inv := inv
      hom_inv_id := hcomp.trans hid.symm
      inv_hom_id := by
        have hq_fst : q.fst = 𝟙 T := by
          simp only [q, schemeChartPullbackPresentation]
        exact hinv_fst.trans hq_fst }

/-- A property containing all scheme isomorphisms holds representably for the identity chart. -/
theorem schemeChart_hasRepresentableProperty
    (P : MorphismProperty Scheme.{u})
    (hP : ∀ {S T : Scheme.{u}} (f : S ⟶ T), IsIso f → P f)
    (X : Scheme.{u}) : (schemeChart X).HasRepresentableProperty P := by
  constructor
  · intro T x
    exact ⟨schemeChartPullbackPresentation X T x⟩
  · intro T x p
    let e := schemeChartPullbackPresentationIso X T x p
    exact hP p.fst e.isIso_hom

/-- The identity chart is a smooth surjective atlas. -/
theorem schemeChart_isSmoothSurjective (X : Scheme.{u}) :
    (schemeChart X).IsSmoothSurjective := by
  let hsmooth := schemeChart_hasRepresentableProperty
    (@_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u})
    (fun _ hf ↦ let _ := hf; inferInstance) X
  let hsurjective := schemeChart_hasRepresentableProperty
    (@_root_.AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u})
    (fun _ hf ↦ let _ := hf; inferInstance) X
  exact ⟨hsmooth.1, fun T x p ↦ ⟨hsmooth.2 T x p, hsurjective.2 T x p⟩⟩

/-- The identity chart is an étale surjective atlas. -/
theorem schemeChart_isEtaleSurjective (X : Scheme.{u}) :
    (schemeChart X).IsEtaleSurjective := by
  let hetale := schemeChart_hasRepresentableProperty
    (@_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})
    (fun _ hf ↦ let _ := hf; inferInstance) X
  let hsurjective := schemeChart_hasRepresentableProperty
    (@_root_.AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u})
    (fun _ hf ↦ let _ := hf; inferInstance) X
  exact ⟨hetale.1, fun T x p ↦ ⟨hetale.2 T x p, hsurjective.2 T x p⟩⟩

/-- Every presentation of the represented scheme's identity chart has pure relative dimension
zero, because its first projection is the hom of the canonical presentation isomorphism. -/
theorem schemeChart_hasPureRelativeDimension_zero (X : Scheme.{u}) :
    (schemeChart X).HasPureRelativeDimension 0 := by
  refine ⟨StackChart.isRepresentable_of_hasRepresentableProperty
    (schemeChart X) _ (schemeChart_isEtaleSurjective X), ?_⟩
  intro T x p
  let e := schemeChartPullbackPresentationIso X T x p
  let _ : IsIso p.fst := e.isIso_hom
  exact schemeMorphismPureRelativeDimension_of_isIso p.fst

private theorem diagonalPullback_fst
    (X T : Scheme.{u}) (x y : StackFiber (ofScheme X) T) :
    pullback.fst (prod.lift x.as y.as) (Limits.diag X) ≫ x.as =
      pullback.snd (prod.lift x.as y.as) (Limits.diag X) := by
  have h₀ : pullback.fst (prod.lift x.as y.as) (Limits.diag X) ≫
      prod.lift x.as y.as =
      pullback.snd (prod.lift x.as y.as) (Limits.diag X) ≫ Limits.diag X :=
    pullback.condition
  have h := congrArg (fun q => q ≫ Limits.prod.fst) h₀
  simpa only [Category.assoc, prod.lift_fst, Category.comp_id] using h

private theorem diagonalPullback_snd
    (X T : Scheme.{u}) (x y : StackFiber (ofScheme X) T) :
    pullback.fst (prod.lift x.as y.as) (Limits.diag X) ≫ y.as =
      pullback.snd (prod.lift x.as y.as) (Limits.diag X) := by
  have h₀ : pullback.fst (prod.lift x.as y.as) (Limits.diag X) ≫
      prod.lift x.as y.as =
      pullback.snd (prod.lift x.as y.as) (Limits.diag X) ≫ Limits.diag X :=
    pullback.condition
  have h := congrArg (fun q => q ≫ Limits.prod.snd) h₀
  simpa only [Category.assoc, prod.lift_snd, Category.comp_id] using h

/-- The isomorphism sheaf between two maps `T ⟶ X` is represented by the scheme-theoretic
pullback of the diagonal of `X`. -/
noncomputable def schemeDiagonalPresentation
    (X T : Scheme.{u}) (x y : StackFiber (ofScheme X) T) :
    DiagonalPresentation (ofScheme X) T x y where
  space := pullback (prod.lift x.as y.as) (Limits.diag X)
  map := pullback.fst (prod.lift x.as y.as) (Limits.diag X)
  universalIso := Discrete.eqToIso <| (diagonalPullback_fst X T x y).trans
    (diagonalPullback_snd X T x y).symm
  lift {S} f e := pullback.lift f (f ≫ x.as) (by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, Category.comp_id]
    · simp only [Category.assoc, prod.lift_snd]
      have he := Discrete.eq_of_hom e.hom
      change f ≫ x.as = f ≫ y.as at he
      exact he.symm)
  lift_map f e := pullback.lift_fst _ _ _
  lift_compatible f e := by
    refine ⟨pullback.lift_fst _ _ _, ?_⟩
    apply Iso.ext
    change @Eq (ULift (PLift (_ = _))) _ _
    apply Subsingleton.elim
  lift_unique {S} f e g compatible := by
    obtain ⟨hg, -⟩ := compatible
    apply pullback.hom_ext
    · calc
        g ≫ pullback.fst (prod.lift x.as y.as) (Limits.diag X) = f := hg
        _ = pullback.lift f (f ≫ x.as) _ ≫
            pullback.fst (prod.lift x.as y.as) (Limits.diag X) :=
          (pullback.lift_fst _ _ _).symm
    · rw [pullback.lift_snd]
      calc
        g ≫ pullback.snd (prod.lift x.as y.as) (Limits.diag X) =
            g ≫ pullback.fst (prod.lift x.as y.as) (Limits.diag X) ≫ x.as := by
              have h := congrArg (fun q => g ≫ q) (diagonalPullback_fst X T x y)
              simpa only [Category.assoc] using h.symm
        _ = f ≫ x.as := by
          simpa only [Category.assoc] using congrArg (fun q => q ≫ x.as) hg

/-- The diagonal of a representable scheme stack is represented by schemes. -/
theorem ofScheme_hasRepresentableDiagonal (X : Scheme.{u}) :
    HasRepresentableDiagonal (ofScheme X) := by
  intro T x y
  exact ⟨schemeDiagonalPresentation X T x y⟩

/-- The diagonal of a representable scheme stack is unramified.  On every test scheme it is
the pullback of the ordinary scheme diagonal, which is an immersion. -/
theorem ofScheme_diagonal_unramified (X : Scheme.{u}) :
    DiagonalHasProperty (ofScheme X)
      (@GromovWitten.AlgebraicGeometry.Unramified : MorphismProperty Scheme.{u}) := by
  intro T x y
  refine ⟨⟨schemeDiagonalPresentation X T x y, ?_⟩⟩
  change GromovWitten.AlgebraicGeometry.Unramified
    (pullback.fst (prod.lift x.as y.as) (Limits.diag X))
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @GromovWitten.AlgebraicGeometry.Unramified)
    (IsPullback.of_hasPullback (prod.lift x.as y.as) (Limits.diag X)).flip inferInstance

/-- A separated scheme has proper diagonal after passage to its represented stack.  Each
scheme-valued isomorphism fibre is the actual base change of the scheme diagonal. -/
theorem ofScheme_diagonal_proper (X : Scheme.{u}) [X.IsSeparated] :
    DiagonalHasProperty (ofScheme X)
      (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u}) := by
  intro T x y
  refine ⟨⟨schemeDiagonalPresentation X T x y, ?_⟩⟩
  change _root_.AlgebraicGeometry.IsProper
    (pullback.fst (prod.lift x.as y.as) (Limits.diag X))
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @_root_.AlgebraicGeometry.IsProper)
    (IsPullback.of_hasPullback (prod.lift x.as y.as) (Limits.diag X)).flip inferInstance

/-- A scheme, regarded as a discrete fppf stack, is algebraic. -/
noncomputable def ofSchemeAlgebraicStack (X : Scheme.{u}) : AlgebraicStack.{u} where
  toStack := ofScheme X
  diagonal_representable := ofScheme_hasRepresentableDiagonal X
  smoothAtlas := ⟨schemeChart X, schemeChart_isSmoothSurjective X⟩

/-- The represented spectrum of a field has pure stack dimension zero, witnessed by its
identity atlas and the proved zero-dimensional fibres of that atlas. -/
theorem ofSchemeAlgebraicStack_specField_pureDimension
    (k : Type u) [Field k] :
    PureStackDimension
      (ofSchemeAlgebraicStack (_root_.AlgebraicGeometry.Spec (.of k))) 0 := by
  refine ⟨
    { atlas := schemeChart (_root_.AlgebraicGeometry.Spec (.of k))
      isSmoothSurjective := schemeChart_isSmoothSurjective _
      atlasDimension := 0
      atlasPureDimension := schemePureDimension_spec_field k
      relativeDimension := 0
      atlasPureRelativeDimension := schemeChart_hasPureRelativeDimension_zero _ }, ?_⟩
  rfl

/-- A scheme, regarded as a discrete fppf stack, is Deligne--Mumford. -/
noncomputable def ofSchemeDeligneMumfordStack (X : Scheme.{u}) :
    DeligneMumfordStack.{u} where
  toAlgebraicStack := ofSchemeAlgebraicStack X
  etaleAtlas := ⟨schemeChart X, schemeChart_isEtaleSurjective X⟩

end FppfStack

end GromovWitten.AlgebraicGeometry
