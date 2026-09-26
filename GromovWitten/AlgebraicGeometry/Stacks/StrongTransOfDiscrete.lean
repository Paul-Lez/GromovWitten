/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Cat

/-!
# Strong transformations out of a locally discrete bicategory

A `Pseudofunctor.StrongTrans F G` between pseudofunctors `F G : B ⥤ᵖ Cat` carries three coherence
laws (`naturality_naturality`, `naturality_id`, `naturality_comp`).  When the source bicategory
`B` is locally discrete (`IsLocallyDiscrete B`, e.g. `B = LocallyDiscrete Cᵒᵖ`, which is the shape
of every stack in this repository) the first of them is vacuous, because the only 2-morphisms of
`B` are identities.  The other two are genuine conditions, but for `Cat`-valued pseudofunctors
they can be checked one object of a fibre at a time, the whiskerings, unitors and associators of
`Cat` contributing only identities.

`CategoryTheory.Pseudofunctor.StrongTrans.mkCatOfComponents` packages exactly this: it builds a
strong transformation from the fibrewise functors, the fibrewise naturality isomorphisms and the
two coherence laws *in componentwise form*.

Both declarations are stated for an **abstract** bicategory `B` and **abstract** pseudofunctors
`F`, `G`, on purpose: instantiating them at a concrete stack is then a cheap type-check, whereas
discharging the same coherence laws inside an anonymous `StrongTrans` structure literal at a
concrete fibre category forces the kernel to unfold that fibre and runs into a `whnf`
deterministic timeout.  This is the same design (and the same reason) as
`CategoryTheory.discreteFunctorOfSubsingleton` and
`CategoryTheory.LocallyDiscrete.mkPseudofunctorOfSubsingleton` in
`GromovWitten/AlgebraicGeometry/Stacks/Discrete.lean`.

## Main declarations

* `CategoryTheory.Pseudofunctor.StrongTrans.naturality_naturality_of_isLocallyDiscrete`:
  the 2-cell naturality law of a strong transformation holds automatically when the source
  bicategory is locally discrete.
* `CategoryTheory.Pseudofunctor.StrongTrans.mkCatOfComponents`: a strong transformation of
  `Cat`-valued pseudofunctors from a locally discrete bicategory, built from componentwise data.
-/

open CategoryTheory CategoryTheory.Bicategory

universe w w₁ v₁ u₁

namespace CategoryTheory.Pseudofunctor.StrongTrans

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] [IsLocallyDiscrete B]
  {F X : Pseudofunctor B Cat.{w, w}}

/-- **Naturality in the 2-morphisms is automatic over a locally discrete source**: every
2-morphism of `B` is an identity, so the naturality square of the strong naturality constraint
of a prospective strong transformation commutes for free. -/
theorem naturality_naturality_of_isLocallyDiscrete
    (app : ∀ a : B, F.obj a ⟶ X.obj a)
    (naturality : ∀ {a b : B} (f : a ⟶ b), F.map f ≫ app b ≅ app a ≫ X.map f)
    {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    F.map₂ η ▷ app b ≫ (naturality g).hom =
      (naturality f).hom ≫ app a ◁ X.map₂ η := by
  obtain rfl := obj_ext_of_isDiscrete η
  obtain rfl : η = 𝟙 f := Subsingleton.elim _ _
  simp

/-- **A strong transformation of `Cat`-valued pseudofunctors from a locally discrete
bicategory, from componentwise data.**  The data are the fibrewise functors `app a`, the
fibrewise naturality isomorphisms `naturality f`, and the two coherence laws evaluated at an
object `y` of the fibre `F.obj a`:

* `nat_id` says that the naturality isomorphism at an identity 1-morphism agrees with the unit
  comparisons `F.mapId`, `X.mapId` of the two pseudofunctors;
* `nat_comp` says that the naturality isomorphism at a composite agrees with the composition
  comparisons `F.mapComp`, `X.mapComp`.

The remaining law `naturality_naturality` is automatic
(`naturality_naturality_of_isLocallyDiscrete`). -/
def mkCatOfComponents
    (app : ∀ a : B, F.obj a ⟶ X.obj a)
    (naturality : ∀ {a b : B} (f : a ⟶ b), F.map f ≫ app b ≅ app a ≫ X.map f)
    (nat_id : ∀ (a : B) (y : (F.obj a : Type w)),
      (naturality (𝟙 a)).hom.toNatTrans.app y ≫
          (X.mapId a).hom.toNatTrans.app ((app a).toFunctor.obj y) =
        (app a).toFunctor.map ((F.mapId a).hom.toNatTrans.app y))
    (nat_comp : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (y : (F.obj a : Type w)),
      (naturality (f ≫ g)).hom.toNatTrans.app y ≫
          (X.mapComp f g).hom.toNatTrans.app ((app a).toFunctor.obj y) =
        (app c).toFunctor.map ((F.mapComp f g).hom.toNatTrans.app y) ≫
          (naturality g).hom.toNatTrans.app ((F.map f).toFunctor.obj y) ≫
            (X.map g).toFunctor.map ((naturality f).hom.toNatTrans.app y)) :
    StrongTrans F X where
  app := app
  naturality := naturality
  naturality_naturality η := naturality_naturality_of_isLocallyDiscrete app naturality η
  naturality_id a := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext y
    simpa using nat_id a y
  naturality_comp f g := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext y
    simpa using nat_comp f g y

end CategoryTheory.Pseudofunctor.StrongTrans
