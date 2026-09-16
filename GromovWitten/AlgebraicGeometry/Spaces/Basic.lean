/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Spaces.Representable
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.InducedCategory
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Algebraic spaces

An algebraic space is an fppf sheaf of types with representable diagonal and a representable,
surjective étale atlas by a scheme.  The category is the full category induced from fppf
sheaves, so a morphism of algebraic spaces is exactly a morphism of their functors of points.

Representable morphism properties are transferred from schemes using Mathlib's
`MorphismProperty.relative`; no second versions of étale, flat, proper, or related properties
are introduced.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

namespace FppfSheaf

/-- The diagonal of an fppf sheaf. -/
noncomputable abbrev diagonal (X : FppfSheaf.{u}) : X ⟶ X ⨯ X :=
  Limits.diag X

/-- Representably étale morphisms of fppf sheaves. -/
abbrev Etale : MorphismProperty FppfSheaf.{u} :=
  HasRepresentableProperty (@_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})

/-- Representably surjective morphisms of fppf sheaves. -/
abbrev Surjective : MorphismProperty FppfSheaf.{u} :=
  HasRepresentableProperty (@_root_.AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u})

/-- Representable, surjective étale morphisms of fppf sheaves. -/
abbrev SurjectiveEtale : MorphismProperty FppfSheaf.{u} :=
  HasRepresentableProperty
    ((@_root_.AlgebraicGeometry.Etale ⊓ @_root_.AlgebraicGeometry.Surjective) :
      MorphismProperty Scheme.{u})

end FppfSheaf

set_option linter.checkUnivs false in
/-- The data and axioms of an algebraic space over the big fppf site of schemes. -/
structure AlgebraicSpaceData where
  /-- The functor of points, already bundled with its fppf sheaf condition. -/
  toSheaf : FppfSheaf.{u}
  /-- The diagonal is representable by schemes after every scheme base change. -/
  diagonal_representable : FppfSheaf.IsRepresentable (FppfSheaf.diagonal toSheaf)
  /-- A scheme atlas which is representable, surjective, and étale. -/
  atlas : ∃ (U : Scheme.{u}) (p : fppfYoneda.obj U ⟶ toSheaf),
    FppfSheaf.SurjectiveEtale p

/-- The category of algebraic spaces, with all morphisms of their fppf functors of points. -/
abbrev AlgebraicSpace :=
  InducedCategory FppfSheaf.{u} (fun X : AlgebraicSpaceData.{u} ↦ X.toSheaf)

namespace AlgebraicSpace

/-- Forget an algebraic space to its fppf functor of points. -/
abbrev forget : AlgebraicSpace.{u} ⥤ FppfSheaf.{u} :=
  inducedFunctor (fun X : AlgebraicSpaceData.{u} ↦ X.toSheaf)

/-- The forgetful functor is fully faithful: algebraic spaces have no extra notion of
morphism beyond maps of their fppf sheaves. -/
def forgetFullyFaithful : forget.{u}.FullyFaithful :=
  fullyFaithfulInducedFunctor _

/-- Construct a morphism of algebraic spaces from a morphism of the underlying fppf sheaves. -/
abbrev homMk {X Y : AlgebraicSpace.{u}} (f : X.toSheaf ⟶ Y.toSheaf) : X ⟶ Y :=
  InducedCategory.homMk f

/-- The underlying morphism of fppf sheaves. -/
abbrev Hom.toSheafMap {X Y : AlgebraicSpace.{u}} (f : X ⟶ Y) : X.toSheaf ⟶ Y.toSheaf :=
  f.hom

/-- A morphism of algebraic spaces is representable when its map of fppf sheaves is. -/
abbrev Representable : MorphismProperty AlgebraicSpace.{u} :=
  fun _ _ f ↦ FppfSheaf.IsRepresentable f.hom

/-- Transfer a scheme-morphism property to representable morphisms of algebraic spaces. -/
abbrev HasRepresentableProperty (P : MorphismProperty Scheme.{u}) :
    MorphismProperty AlgebraicSpace.{u} :=
  fun _ _ f ↦ FppfSheaf.HasRepresentableProperty P f.hom

/-- Representably étale morphisms of algebraic spaces. -/
abbrev Etale : MorphismProperty AlgebraicSpace.{u} :=
  HasRepresentableProperty (@_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})

/-- Representably surjective morphisms of algebraic spaces. -/
abbrev Surjective : MorphismProperty AlgebraicSpace.{u} :=
  HasRepresentableProperty (@_root_.AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u})

end AlgebraicSpace

/-- The product with an identity map is also a pullback in the second coordinate.  Mathlib
provides the first-coordinate form; this is its direct product-universal-property analogue. -/
theorem FppfSheaf.isPullback_prod_snd_with_id
    {A B X : FppfSheaf.{u}} (f : A ⟶ B) :
    IsPullback (prod.snd : X ⨯ A ⟶ A) (prod.map (𝟙 X) f) f
      (prod.snd : X ⨯ B ⟶ B) := by
  apply IsPullback.mk'
  · exact (prod.map_snd (𝟙 X) f).symm
  · intro T a b h₁ h₂
    apply prod.hom_ext
    · simpa using congrArg (fun k ↦ k ≫ prod.fst) h₂
    · exact h₁
  · intro T a b h
    refine ⟨prod.lift (b ≫ prod.fst) a, ?_, ?_⟩
    · exact prod.lift_snd _ _
    · apply prod.hom_ext
      · simpa only [Category.assoc, prod.map_fst, Category.comp_id] using
          (prod.lift_fst (b ≫ prod.fst) a)
      · simpa only [Category.assoc, prod.map_snd, prod.lift_snd_assoc] using h

/-- A product of two relatively representable sheaf morphisms is relatively representable.
The proof factors the product map into two actual cartesian base changes. -/
theorem FppfSheaf.isRepresentable_prod_map
    {A B C D : FppfSheaf.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (hf : FppfSheaf.IsRepresentable f)
    (hg : FppfSheaf.IsRepresentable g) :
    FppfSheaf.IsRepresentable (prod.map f g) := by
  have hleft : FppfSheaf.IsRepresentable (prod.map f (𝟙 C)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_prod_fst_with_id f C) hf
  have hright : FppfSheaf.IsRepresentable (prod.map (𝟙 B) g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (FppfSheaf.isPullback_prod_snd_with_id g) hg
  simpa using FppfSheaf.IsRepresentable.comp_mem _ _ hleft hright

/-- A pair of relatively representable maps with a representable source diagonal gives a
relatively representable map to the product. -/
theorem FppfSheaf.isRepresentable_prod_lift
    {T X Y : FppfSheaf.{u}} (f : T ⟶ X) (g : T ⟶ Y)
    (hf : FppfSheaf.IsRepresentable f)
    (hg : FppfSheaf.IsRepresentable g)
    (hdiag : FppfSheaf.IsRepresentable (Limits.diag T)) :
    FppfSheaf.IsRepresentable (prod.lift f g) := by
  have hfactor : Limits.diag T ≫ prod.map f g = prod.lift f g := by
    apply prod.hom_ext <;> simp
  rw [← hfactor]
  exact FppfSheaf.IsRepresentable.comp_mem _ _ hdiag
    (FppfSheaf.isRepresentable_prod_map f g hf hg)

/-- The diagonal of the represented fppf sheaf of a scheme is representable. -/
theorem FppfSheaf.yoneda_obj_diagonal_isRepresentable
    (T : _root_.AlgebraicGeometry.Scheme.{u}) :
    FppfSheaf.IsRepresentable (Limits.diag (fppfYoneda.obj T)) := by
  have hcomparison :
      fppfYoneda.map (Limits.diag T) ≫
          (PreservesLimitPair.iso fppfYoneda T T).hom =
        Limits.diag (fppfYoneda.obj T) := by
    apply prod.hom_ext
    · simp only [Category.assoc, PreservesLimitPair.iso_hom, prodComparison_fst]
      rw [← fppfYoneda.map_comp]
      simpa only [prod.lift_fst, Functor.map_id] using fppfYoneda.map_id T
    · simp only [Category.assoc, PreservesLimitPair.iso_hom, prodComparison_snd]
      rw [← fppfYoneda.map_comp]
      simpa only [prod.lift_snd, Functor.map_id] using fppfYoneda.map_id T
  rw [← hcomparison]
  exact FppfSheaf.IsRepresentable.comp_mem _ _
    (FppfSheaf.yoneda_map_isRepresentable (Limits.diag T))
    (Functor.relativelyRepresentable.of_isIso fppfYoneda _)

/-- Products preserve any multiplicative representable scheme-morphism property. -/
theorem FppfSheaf.hasRepresentableProperty_prod_map
    (P : MorphismProperty _root_.AlgebraicGeometry.Scheme.{u})
    [P.IsMultiplicative]
    {A B C D : FppfSheaf.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (hf : FppfSheaf.HasRepresentableProperty P f)
    (hg : FppfSheaf.HasRepresentableProperty P g) :
    FppfSheaf.HasRepresentableProperty P (prod.map f g) := by
  let _ : P.IsStableUnderComposition :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have hleft : (P.relative fppfYoneda) (prod.map f (𝟙 C)) :=
    (MorphismProperty.relative_isStableUnderBaseChange P).of_isPullback
      (IsPullback.of_prod_fst_with_id f C) hf
  have hright : (P.relative fppfYoneda) (prod.map (𝟙 B) g) :=
    (MorphismProperty.relative_isStableUnderBaseChange P).of_isPullback
      (FppfSheaf.isPullback_prod_snd_with_id g) hg
  change (P.relative fppfYoneda) (prod.map f g)
  simpa using (MorphismProperty.relative_isStableUnderComposition P).comp_mem
    (prod.map f (𝟙 C)) (prod.map (𝟙 B) g) hleft hright

/-- The product of two algebraic spaces.  Its representable diagonal and product atlas are
constructed from those of the factors using actual cartesian squares. -/
noncomputable def AlgebraicSpaceData.prod
    (X Y : AlgebraicSpaceData.{u}) : AlgebraicSpaceData.{u} where
  toSheaf := X.toSheaf ⨯ Y.toSheaf
  diagonal_representable := by
    apply (Functor.relativelyRepresentable.diag_iff).2
    intro T h
    have hx : FppfSheaf.IsRepresentable (h ≫ prod.fst) :=
      Functor.relativelyRepresentable.of_diag X.diagonal_representable _
    have hy : FppfSheaf.IsRepresentable (h ≫ prod.snd) :=
      Functor.relativelyRepresentable.of_diag Y.diagonal_representable _
    have heq : h = prod.lift (h ≫ prod.fst) (h ≫ prod.snd) := by
      symm
      rw [← prod.comp_lift, prod.lift_fst_snd, Category.comp_id]
    rw [heq]
    exact FppfSheaf.isRepresentable_prod_lift _ _ hx hy
      (FppfSheaf.yoneda_obj_diagonal_isRepresentable T)
  atlas := by
    obtain ⟨U, p, hp⟩ := X.atlas
    obtain ⟨V, q, hq⟩ := Y.atlas
    let comparison := (PreservesLimitPair.iso fppfYoneda U V).hom
    refine ⟨U ⨯ V, comparison ≫ prod.map p q, ?_⟩
    change (((@_root_.AlgebraicGeometry.Etale ⊓
      @_root_.AlgebraicGeometry.Surjective) :
        MorphismProperty _root_.AlgebraicGeometry.Scheme.{u}).relative fppfYoneda)
          (comparison ≫ prod.map p q)
    let _ : ((@_root_.AlgebraicGeometry.Etale ⊓
        @_root_.AlgebraicGeometry.Surjective) :
          MorphismProperty _root_.AlgebraicGeometry.Scheme.{u}).IsMultiplicative :=
      MorphismProperty.IsMultiplicative.inf
    have hprod := FppfSheaf.hasRepresentableProperty_prod_map
      ((@_root_.AlgebraicGeometry.Etale ⊓
        @_root_.AlgebraicGeometry.Surjective) :
          MorphismProperty _root_.AlgebraicGeometry.Scheme.{u}) p q hp hq
    exact MorphismProperty.RespectsIso.precomp
      (((@_root_.AlgebraicGeometry.Etale ⊓
        @_root_.AlgebraicGeometry.Surjective) :
          MorphismProperty _root_.AlgebraicGeometry.Scheme.{u}).relative fppfYoneda)
      comparison (prod.map p q) hprod

namespace AlgebraicSpace

/-- The product algebraic space, whose underlying sheaf is the categorical product. -/
noncomputable def productObj (X Y : AlgebraicSpace.{u}) : AlgebraicSpace.{u} :=
  AlgebraicSpaceData.prod X Y

/-- First projection from the constructed product algebraic space. -/
noncomputable def productFst (X Y : AlgebraicSpace.{u}) : productObj X Y ⟶ X :=
  homMk prod.fst

/-- Second projection from the constructed product algebraic space. -/
noncomputable def productSnd (X Y : AlgebraicSpace.{u}) : productObj X Y ⟶ Y :=
  homMk prod.snd

/-- The constructed product sheaf satisfies the product universal property in algebraic
spaces. -/
noncomputable def productIsProduct (X Y : AlgebraicSpace.{u}) :
    IsLimit (BinaryFan.mk (productFst X Y) (productSnd X Y)) :=
  BinaryFan.isLimitMk
    (fun s ↦ homMk (prod.lift s.fst.hom s.snd.hom))
    (fun s ↦ by
      apply InducedCategory.hom_ext
      exact prod.lift_fst _ _)
    (fun s ↦ by
      apply InducedCategory.hom_ext
      exact prod.lift_snd _ _)
    (fun s m hfst hsnd ↦ by
      apply InducedCategory.hom_ext
      have hfst' := congrArg InducedCategory.Hom.hom hfst
      have hsnd' := congrArg InducedCategory.Hom.hom hsnd
      change m.hom ≫ prod.fst = s.fst.hom at hfst'
      change m.hom ≫ prod.snd = s.snd.hom at hsnd'
      apply prod.hom_ext
      · exact hfst'.trans (prod.lift_fst _ _).symm
      · exact hsnd'.trans (prod.lift_snd _ _).symm)

/-- Every pair of algebraic spaces has the explicitly constructed product above. -/
noncomputable instance hasBinaryProduct (X Y : AlgebraicSpace.{u}) :
    HasBinaryProduct X Y :=
  ⟨⟨⟨BinaryFan.mk (productFst X Y) (productSnd X Y), productIsProduct X Y⟩⟩⟩

/-- Algebraic spaces admit binary categorical products. -/
noncomputable instance : HasBinaryProducts AlgebraicSpace.{u} :=
  hasBinaryProducts_of_hasLimit_pair AlgebraicSpace.{u}

end AlgebraicSpace

/-- A map from a represented scheme into the source of a representable morphism to an algebraic
space is representable.  The proof constructs its factorization through the represented base
change and uses the actual classifying lift. -/
theorem FppfSheaf.isRepresentable_map_to_source
    (X : AlgebraicSpaceData.{u}) {Y : FppfSheaf.{u}}
    (f : Y ⟶ X.toSheaf) (hf : FppfSheaf.IsRepresentable f)
    {T : Scheme.{u}} (h : fppfYoneda.obj T ⟶ Y) :
    FppfSheaf.IsRepresentable h := by
  have hbase : FppfSheaf.IsRepresentable (h ≫ f) :=
    Functor.relativelyRepresentable.of_diag X.diagonal_representable _
  have hprojection : FppfSheaf.IsRepresentable (hf.fst (h ≫ f)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (hf.isPullback (h ≫ f)).flip hbase
  let sec := hf.lift (g := h ≫ f) h (𝟙 T) (by simp)
  have hsection : fppfYoneda.map sec ≫ hf.fst (h ≫ f) = h := by
    exact hf.lift_fst (g := h ≫ f) h (𝟙 T) (by simp)
  rw [← hsection]
  exact FppfSheaf.IsRepresentable.comp_mem _ _
    (FppfSheaf.yoneda_map_isRepresentable sec) hprojection

/-- The source of a relatively representable morphism to an algebraic space is algebraic.  Its
diagonal and atlas are constructed from the representing pullbacks, not supplied as additional
fields. -/
noncomputable def AlgebraicSpaceData.ofRepresentable
    (X : AlgebraicSpaceData.{u}) {Y : FppfSheaf.{u}}
    (f : Y ⟶ X.toSheaf) (hf : FppfSheaf.IsRepresentable f) :
    AlgebraicSpaceData.{u} where
  toSheaf := Y
  diagonal_representable := by
    apply (Functor.relativelyRepresentable.diag_iff).2
    intro T h
    exact FppfSheaf.isRepresentable_map_to_source X f hf h
  atlas := by
    obtain ⟨U, p, hp⟩ := X.atlas
    refine ⟨hf.pullback p, hf.fst p, ?_⟩
    change (((@_root_.AlgebraicGeometry.Etale ⊓
      @_root_.AlgebraicGeometry.Surjective) : MorphismProperty Scheme.{u}).relative
        fppfYoneda) (hf.fst p)
    exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (hf.isPullback p).flip hp

/-- The canonical inclusion of a pullback into the product of its two sources. -/
noncomputable def FppfSheaf.pullbackToProduct
    {X Y Z : FppfSheaf.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullback f g ⟶ X ⨯ Y :=
  prod.lift (pullback.fst f g) (pullback.snd f g)

/-- The inclusion of `X ×_Z Y` into `X × Y` is the base change of the diagonal of `Z`. -/
theorem FppfSheaf.pullbackToProduct_isPullback
    {X Y Z : FppfSheaf.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsPullback (pullback.fst f g ≫ f) (FppfSheaf.pullbackToProduct f g)
      (Limits.diag Z) (prod.map f g) := by
  apply IsPullback.mk'
  · apply prod.hom_ext
    · simp only [prod.comp_diag, FppfSheaf.pullbackToProduct,
        Category.assoc, prod.map_fst, prod.lift_fst, prod.lift_fst_assoc]
    · simpa only [prod.comp_diag, FppfSheaf.pullbackToProduct,
        Category.assoc, prod.map_snd, prod.lift_snd, prod.lift_snd_assoc] using
        (pullback.condition : pullback.fst f g ≫ f = pullback.snd f g ≫ g)
  · intro T a b h₁ h₂
    apply pullback.hom_ext
    · have h := congrArg (fun k ↦ k ≫ prod.fst) h₂
      simpa only [Category.assoc, FppfSheaf.pullbackToProduct,
        prod.lift_fst] using h
    · have h := congrArg (fun k ↦ k ≫ prod.snd) h₂
      simpa only [Category.assoc, FppfSheaf.pullbackToProduct,
        prod.lift_snd] using h
  · intro T a b h
    have hfst : a = (b ≫ prod.fst) ≫ f := by
      have h' := congrArg (fun k ↦ k ≫ prod.fst) h
      simpa only [prod.comp_diag, Category.assoc, prod.lift_fst,
        prod.map_fst] using h'
    have hsnd : a = (b ≫ prod.snd) ≫ g := by
      have h' := congrArg (fun k ↦ k ≫ prod.snd) h
      simpa only [prod.comp_diag, Category.assoc, prod.lift_snd,
        prod.map_snd] using h'
    have hcondition : (b ≫ prod.fst) ≫ f = (b ≫ prod.snd) ≫ g :=
      hfst.symm.trans hsnd
    let lift := pullback.lift (b ≫ prod.fst) (b ≫ prod.snd)
      hcondition
    refine ⟨lift, ?_, ?_⟩
    · simpa only [lift, pullback.lift_fst_assoc] using hfst.symm
    · apply prod.hom_ext
      · simpa only [Category.assoc, FppfSheaf.pullbackToProduct,
          prod.lift_fst] using (pullback.lift_fst
            (b ≫ prod.fst) (b ≫ prod.snd) hcondition)
      · simpa only [Category.assoc, FppfSheaf.pullbackToProduct,
          prod.lift_snd] using (pullback.lift_snd
            (b ≫ prod.fst) (b ≫ prod.snd) hcondition)

/-- The pullback of two algebraic-space morphisms, built as the sheaf pullback and proved
algebraic through the representable base change of the target diagonal. -/
noncomputable def AlgebraicSpaceData.pullback
    (X Y Z : AlgebraicSpaceData.{u})
    (f : X.toSheaf ⟶ Z.toSheaf) (g : Y.toSheaf ⟶ Z.toSheaf) :
    AlgebraicSpaceData.{u} :=
  AlgebraicSpaceData.ofRepresentable (AlgebraicSpaceData.prod X Y)
    (FppfSheaf.pullbackToProduct f g)
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (FppfSheaf.pullbackToProduct_isPullback f g) Z.diagonal_representable)

namespace AlgebraicSpace

/-- The sheaf pullback of two algebraic-space morphisms, equipped with the algebraic-space
structure constructed above. -/
noncomputable def pullbackObj {X Y Z : AlgebraicSpace.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) : AlgebraicSpace.{u} :=
  AlgebraicSpaceData.pullback X Y Z f.hom g.hom

/-- First projection from the constructed pullback. -/
noncomputable def pullbackFst {X Y Z : AlgebraicSpace.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) : pullbackObj f g ⟶ X :=
  homMk (Limits.pullback.fst f.hom g.hom)

/-- Second projection from the constructed pullback. -/
noncomputable def pullbackSnd {X Y Z : AlgebraicSpace.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) : pullbackObj f g ⟶ Y :=
  homMk (Limits.pullback.snd f.hom g.hom)

/-- The constructed sheaf pullback satisfies the pullback universal property in algebraic
spaces. -/
theorem pullbackIsPullback {X Y Z : AlgebraicSpace.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsPullback (pullbackFst f g) (pullbackSnd f g) f g := by
  apply IsPullback.mk'
  · apply InducedCategory.hom_ext
    exact Limits.pullback.condition
  · intro T a b h₁ h₂
    apply InducedCategory.hom_ext
    apply Limits.pullback.hom_ext
    · have h := congrArg InducedCategory.Hom.hom h₁
      change a.hom ≫ Limits.pullback.fst f.hom g.hom =
        b.hom ≫ Limits.pullback.fst f.hom g.hom at h
      exact h
    · have h := congrArg InducedCategory.Hom.hom h₂
      change a.hom ≫ Limits.pullback.snd f.hom g.hom =
        b.hom ≫ Limits.pullback.snd f.hom g.hom at h
      exact h
  · intro T a b h
    refine ⟨homMk (Limits.pullback.lift a.hom b.hom ?_), ?_, ?_⟩
    · exact congrArg InducedCategory.Hom.hom h
    · apply InducedCategory.hom_ext
      exact Limits.pullback.lift_fst _ _ _
    · apply InducedCategory.hom_ext
      exact Limits.pullback.lift_snd _ _ _

/-- Every cospan of algebraic spaces has the explicitly constructed pullback above. -/
noncomputable instance hasPullback {X Y Z : AlgebraicSpace.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g :=
  (pullbackIsPullback f g).hasPullback

/-- Algebraic spaces admit all categorical pullbacks. -/
noncomputable instance : HasPullbacks AlgebraicSpace.{u} :=
  hasPullbacks_of_hasLimit_cospan AlgebraicSpace.{u}

/-- Forgetting an algebraic space preserves the constructed pullbacks: both the object and its
projections are the corresponding sheaf pullback. -/
noncomputable instance : PreservesLimitsOfShape WalkingCospan forget.{u} := by
  apply preservesLimitsOfShape_walkingCospan_of_forall_isPullback
  intro X Y Z f g
  exact ⟨pullbackObj f g, pullbackFst f g, pullbackSnd f g,
    pullbackIsPullback f g, IsPullback.of_hasPullback f.hom g.hom⟩

end AlgebraicSpace

end GromovWitten.AlgebraicGeometry
