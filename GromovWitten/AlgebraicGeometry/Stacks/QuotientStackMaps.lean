/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.QuotientStackPullback

/-!
# Morphisms of action-torsor pseudofunctors from equivariant maps

An equivariant morphism `q : U ⟶ V` of algebraic spaces with `G`-action induces, over every
test scheme, the functor `ActionTorsor.mapTargetFunctor q` which postcomposes the equivariant
map of a torsor with `q`.  This file proves that these functors are compatible with base change
along an arbitrary scheme morphism and assembles them into an honest strong transformation

`ActionTorsor.mapTargetStrongTrans q :
  pullbackPseudofunctor G U ⟶ pullbackPseudofunctor G V`

of pseudofunctors on the locally discrete bicategory of schemes.  The naturality cells are
identity 2-cells: postcomposition with `q` commutes strictly with base change of torsors,
because both operations leave the underlying fibre-product sheaf and its action untouched.  The
three coherence laws of a strong transformation (`naturality_naturality`, `naturality_id` and
`naturality_comp`) are proved, the last one using `FppfTorsor.pullbackMap_id`.

Nothing here assumes fppf descent: the pseudofunctors involved are not yet known to be stacks,
so this is a morphism of prestacks.
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

namespace ActionTorsor

variable {G : AlgebraicSpaceGroup.{u}} {U V : AlgebraicSpaceAction G}
  {T T' T'' : Scheme.{u}}

/-- Base change commutes with postcomposition of the target map, on objects. -/
noncomputable def mapTargetPullbackIsoApp (q : U ⟶ V) (b : T' ⟶ T)
    (P : ActionTorsor G U T) :
    mapTarget q (pullbackObj b P) ≅ pullbackObj b (mapTarget q P) :=
  asIso
    { iso := Iso.refl _
      over := Category.id_comp _
      equivariant := by rfl
      target := by
        change (𝟙 _) ≫ Limits.pullback.fst P.projection (fppfYoneda.map b) ≫
            (P.target ≫ q.hom.hom) =
          (Limits.pullback.fst P.projection (fppfYoneda.map b) ≫ P.target) ≫ q.hom.hom
        simp }

/-- Base change commutes with postcomposition of the target map. -/
noncomputable def mapTargetPullbackIso (q : U ⟶ V) (b : T' ⟶ T) :
    pullbackFunctor (U := U) b ⋙ mapTargetFunctor (T := T') q ≅
      mapTargetFunctor (T := T) q ⋙ pullbackFunctor (U := V) b :=
  NatIso.ofComponents (mapTargetPullbackIsoApp q b) (fun {P Q} f ↦ by
    apply Hom.ext
    change (FppfTorsor.pullbackMap b f.iso.hom f.over) ≫ 𝟙 _ =
      𝟙 _ ≫ (FppfTorsor.pullbackMap b f.iso.hom f.over)
    simp)

@[simp]
theorem mapTargetPullbackIsoApp_hom_iso_hom (q : U ⟶ V) (b : T' ⟶ T)
    (P : ActionTorsor G U T) :
    (mapTargetPullbackIsoApp q b P).hom.iso.hom =
      𝟙 (FppfTorsor.pullbackSheaf P.toFppfTorsor b) :=
  rfl

@[simp]
theorem mapTargetPullbackIso_hom_app_iso_hom (q : U ⟶ V) (b : T' ⟶ T)
    (P : ActionTorsor G U T) :
    ((mapTargetPullbackIso q b).hom.app P).iso.hom =
      𝟙 (FppfTorsor.pullbackSheaf P.toFppfTorsor b) :=
  rfl

/-- The `map` of the action-torsor pseudofunctor is base change. -/
theorem pullbackPseudofunctor_map {a b : LocallyDiscrete Scheme.{u}ᵒᵖ} (f : a ⟶ b) :
    (pullbackPseudofunctor G U).map f = (pullbackFunctor (U := U) f.as.unop).toCatHom :=
  rfl

/-- The unit comparison of the action-torsor pseudofunctor. -/
theorem pullbackPseudofunctor_mapId (a : LocallyDiscrete Scheme.{u}ᵒᵖ) :
    (pullbackPseudofunctor G U).mapId a =
      Cat.Hom.isoMk (pullbackFunctorIdIso (U := U) (T := a.as.unop)) :=
  rfl

/-- The composition comparison of the action-torsor pseudofunctor. -/
theorem pullbackPseudofunctor_mapComp {a b c : LocallyDiscrete Scheme.{u}ᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) :
    (pullbackPseudofunctor G U).mapComp f g =
      Cat.Hom.isoMk (pullbackFunctorCompIso (U := U) g.as.unop f.as.unop) :=
  rfl

/-- Postcomposition by an equivariant map commutes with the identity comparison of base
change. -/
theorem mapTargetFunctor_whiskerLeft_pullbackFunctorIdIso (q : U ⟶ V) :
    Functor.whiskerLeft (mapTargetFunctor (T := T) q) (pullbackFunctorIdIso (U := V)).hom =
      Functor.whiskerRight (pullbackFunctorIdIso (U := U)).hom
        (mapTargetFunctor (T := T) q) := by
  ext P
  apply Hom.ext
  rfl

/-- Postcomposition by an equivariant map commutes with the composition comparison of base
change. -/
theorem mapTargetFunctor_whiskerLeft_pullbackFunctorCompIso (q : U ⟶ V)
    (a : T'' ⟶ T') (b : T' ⟶ T) :
    Functor.whiskerLeft (mapTargetFunctor (T := T) q)
        (pullbackFunctorCompIso (U := V) a b).hom =
      Functor.whiskerRight (pullbackFunctorCompIso (U := U) a b).hom
        (mapTargetFunctor (T := T'') q) := by
  ext P
  apply Hom.ext
  rfl

/-- An equivariant morphism of `G`-algebraic spaces induces a strong transformation between the
corresponding action-torsor pseudofunctors.  Its naturality cells are identities: base change
of torsors commutes strictly with postcomposition of the target map. -/
noncomputable def mapTargetStrongTrans (q : U ⟶ V) :
    Pseudofunctor.StrongTrans (pullbackPseudofunctor G U) (pullbackPseudofunctor G V) where
  app a := (mapTargetFunctor (T := a.as.unop) q).toCatHom
  naturality {_ _} _ := Iso.refl _
  naturality_naturality {_ _ _ _} eta := by
    obtain rfl := obj_ext_of_isDiscrete eta
    ext1
    ext P
    apply Hom.ext
    rfl
  naturality_id _ := by
    ext1
    ext P
    apply Hom.ext
    rfl
  naturality_comp {a b c} f g := by
    ext1
    ext P
    apply Hom.ext
    change (FppfTorsor.pullbackCompIso P.toFppfTorsor g.as.unop f.as.unop).hom =
      (FppfTorsor.pullbackCompIso P.toFppfTorsor g.as.unop f.as.unop).hom ≫
        𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫
          FppfTorsor.pullbackMap g.as.unop (𝟙 _) (Category.id_comp _) ≫ 𝟙 _
    simp only [Category.comp_id, Category.id_comp]
    apply Limits.pullback.hom_ext <;> simp [FppfTorsor.pullbackMap]

end ActionTorsor

end GromovWitten.AlgebraicGeometry
