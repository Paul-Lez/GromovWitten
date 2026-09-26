/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import GromovWitten.AlgebraicGeometry.RelativeSpecAffineHom
import GromovWitten.AlgebraicGeometry.RelativeSpecFunctoriality
import GromovWitten.AlgebraicGeometry.RelativeSpecPolynomial
import GromovWitten.AlgebraicGeometry.Cones.NormalConeGlobal
import GromovWitten.AlgebraicGeometry.Stacks.SchemeAtlasRefinement

/-!
# Relative `Spec` as a morphism of stacks

The relative `Spec` `relativeSpec X 𝒜` of a quasi-coherent algebra `𝒜` on a scheme `X`
(`RelativeSpec.AlgebraData`) is promoted here to a morphism of represented fppf stacks
`stackSpec X 𝒜 : StackHom (representedStack (relativeSpec X 𝒜)) (representedStack X)`, the image
of the affine structure morphism `toBase X 𝒜` under the functoriality of `representedStack`. This
morphism is representable by affine morphisms of schemes, exhibiting `relativeSpec X 𝒜` as an
"affine morphism of stacks" over `X` in the sense of `Stacks.Algebraic`.

* `AlgebraData.pullback 𝒜 f` is the pullback of `𝒜` along a test morphism `f : T ⟶ X`, obtained
  from the fact that affine morphisms are stable under base change
  (`isAffineHom_pullback_snd_toBase`) applied to the base change of `toBase X 𝒜` along `f`.
* `isPullback_relativeSpecPullback` exhibits `relativeSpec T (𝒜.pullback f)`, together with its
  structure map to `T` and the comparison map `relativeSpecPullbackFst` to `relativeSpec X 𝒜`, as
  the scheme-theoretic pullback square of `toBase X 𝒜` along `f`.
* `stackSpec X 𝒜` is the induced morphism of represented stacks, and
  `stackSpec_hasRepresentableProperty_isAffineHom` shows it is representable by affine morphisms
  (through the scheme-theoretic pullback of `toBase X 𝒜`); `𝒜.pullback` identifies that pullback
  with the relative `Spec` of the pulled-back algebra, which the universal property below uses.
* `relativeSpecPullbackCompIso` and `relativeSpecPullbackIdIso` record the coherence of
  `AlgebraData.pullback` with composition and identities of test morphisms, at the level of the
  represented relative Specs.
-/

open CategoryTheory Limits AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace GromovWitten.AlgebraicGeometry

open RelativeSpec

universe u

noncomputable section

variable {X T T' : Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
/-- Affine morphisms are stable under base change: the structure morphism of a relative `Spec`
remains affine after pulling back along any test morphism `f : T ⟶ X`. -/
instance isAffineHom_pullback_snd_toBase (𝒜 : AlgebraData X) (f : T ⟶ X) :
    _root_.AlgebraicGeometry.IsAffineHom (pullback.snd (toBase X 𝒜) f) :=
  MorphismProperty.pullback_snd _ _ (toBase_isAffineHom X 𝒜)

/-- The pullback of a quasi-coherent algebra `𝒜` on `X` along a test morphism `f : T ⟶ X`: the
quasi-coherent algebra on `T` attached to the (affine) base change of the structure morphism
of `𝒜` along `f`. -/
def AlgebraData.pullback (𝒜 : AlgebraData X) (f : T ⟶ X) : AlgebraData T :=
  RelativeSpec.AlgebraData.ofAffineHom (pullback.snd (toBase X 𝒜) f)

/-- The relative `Spec` of the pullback of `𝒜` along `f` is the scheme-theoretic pullback of
`relativeSpec X 𝒜` along `f`, since every affine morphism is the relative `Spec` of its own
quasi-coherent algebra of sections (`relativeSpecOfAffineHomIso`). -/
def relativeSpecPullbackIso (𝒜 : AlgebraData X) (f : T ⟶ X) :
    relativeSpec T (𝒜.pullback f) ≅ pullback (toBase X 𝒜) f :=
  relativeSpecOfAffineHomIso (pullback.snd (toBase X 𝒜) f)

@[reassoc]
theorem relativeSpecPullbackIso_hom_comp (𝒜 : AlgebraData X) (f : T ⟶ X) :
    (relativeSpecPullbackIso 𝒜 f).hom ≫ pullback.snd (toBase X 𝒜) f = toBase T (𝒜.pullback f) :=
  relativeSpecOfAffineHomIso_hom_comp (pullback.snd (toBase X 𝒜) f)

/-- The comparison map from the relative `Spec` of the pullback of `𝒜` along `f` to
`relativeSpec X 𝒜`, covering `f`. -/
def relativeSpecPullbackFst (𝒜 : AlgebraData X) (f : T ⟶ X) :
    relativeSpec T (𝒜.pullback f) ⟶ relativeSpec X 𝒜 :=
  (relativeSpecPullbackIso 𝒜 f).hom ≫ pullback.fst (toBase X 𝒜) f

/-- The relative `Spec` of the pullback of `𝒜` along `f`, together with its structure map to `T`
and its comparison map to `relativeSpec X 𝒜`, is the scheme-theoretic pullback square of the
structure morphism `toBase X 𝒜` along `f`. -/
theorem isPullback_relativeSpecPullback (𝒜 : AlgebraData X) (f : T ⟶ X) :
    IsPullback (relativeSpecPullbackFst 𝒜 f) (toBase T (𝒜.pullback f)) (toBase X 𝒜) f := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ (relativeSpecPullbackIso 𝒜 f) rfl
    (relativeSpecPullbackIso_hom_comp 𝒜 f)
  rw [relativeSpecPullbackFst, Category.assoc, pullback.condition, ← Category.assoc,
    relativeSpecPullbackIso_hom_comp]

/-- The morphism of represented stacks induced by the structure map of a relative `Spec`: the
image of `toBase X 𝒜` under the functoriality of `representedStack`. -/
def stackSpec (X : Scheme.{u}) (𝒜 : AlgebraData X) :
    StackHom (representedStack (relativeSpec X 𝒜)) (representedStack X) :=
  FppfStack.mapOfSchemeHom (toBase X 𝒜)

/-- The structure morphism of a relative `Spec`, viewed as a morphism of represented stacks, is
representable by affine morphisms: every base change by a test object over a scheme `T` is
represented by the scheme-theoretic pullback of `toBase X 𝒜`, whose structure map to `T` is
affine; `isPullback_relativeSpecPullback` identifies it with the relative `Spec` of the
pulled-back algebra. -/
theorem stackSpec_hasRepresentableProperty_isAffineHom (X : Scheme.{u}) (𝒜 : AlgebraData X) :
    (stackSpec X 𝒜).HasRepresentableProperty
      (@_root_.AlgebraicGeometry.IsAffineHom : MorphismProperty Scheme.{u}) :=
  FppfStack.mapOfSchemeHom_hasRepresentableProperty
    (@_root_.AlgebraicGeometry.IsAffineHom : MorphismProperty Scheme.{u})
    (toBase X 𝒜) (toBase_isAffineHom X 𝒜)

/-- The structure morphism of a relative `Spec`, viewed as a morphism of represented stacks, is
representable by schemes. -/
theorem stackSpec_isRepresentable (X : Scheme.{u}) (𝒜 : AlgebraData X) :
    (stackSpec X 𝒜).IsRepresentable :=
  StackHom.isRepresentable_of_hasRepresentableProperty _ _
    (stackSpec_hasRepresentableProperty_isAffineHom X 𝒜)

/-- Pulling back `𝒜` along `f : T ⟶ X` and then along `g : T' ⟶ T` gives (the relative `Spec`
of) the same algebra data, up to a canonical isomorphism over `T'`, as pulling back `𝒜` directly
along the composite `g ≫ f`. This is the pasting of two pullback squares of
`isPullback_relativeSpecPullback`. -/
def relativeSpecPullbackCompIso (𝒜 : AlgebraData X) (f : T ⟶ X) (g : T' ⟶ T) :
    relativeSpec T' ((𝒜.pullback f).pullback g) ≅ relativeSpec T' (𝒜.pullback (g ≫ f)) :=
  ((isPullback_relativeSpecPullback (𝒜.pullback f) g).paste_horiz
    (isPullback_relativeSpecPullback 𝒜 f)).isoIsPullback _ _
    (isPullback_relativeSpecPullback 𝒜 (g ≫ f))

/-- `relativeSpecPullbackCompIso` is a morphism over `T'`. -/
theorem relativeSpecPullbackCompIso_hom_comp (𝒜 : AlgebraData X) (f : T ⟶ X) (g : T' ⟶ T) :
    (relativeSpecPullbackCompIso 𝒜 f g).hom ≫ toBase T' (𝒜.pullback (g ≫ f)) =
      toBase T' ((𝒜.pullback f).pullback g) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- Pulling `𝒜` back along the identity of `X` recovers (the relative `Spec` of) `𝒜` itself, up
to a canonical isomorphism over `X`. -/
def relativeSpecPullbackIdIso (𝒜 : AlgebraData X) :
    relativeSpec X (𝒜.pullback (𝟙 X)) ≅ relativeSpec X 𝒜 :=
  (isPullback_relativeSpecPullback 𝒜 (𝟙 X)).isoIsPullback _ _ IsPullback.of_id_fst

/-- `relativeSpecPullbackIdIso` is a morphism over `X`. -/
theorem relativeSpecPullbackIdIso_hom_comp (𝒜 : AlgebraData X) :
    (relativeSpecPullbackIdIso 𝒜).hom ≫ toBase X 𝒜 = toBase X (𝒜.pullback (𝟙 X)) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _


/-! ### Item (a): the universal property in stack language -/

/-- Lifts of a chart `x : T ⟶ X` through `stackSpec X 𝒜` — morphisms `T ⟶ relativeSpec X 𝒜`
over `x` — correspond to sections over `T` of the structure map of the pulled-back algebra
`𝒜.pullback x`, via the pullback universal property of `isPullback_relativeSpecPullback`. -/
def liftEquivSection (𝒜 : AlgebraData X) (x : T ⟶ X) :
    {h : T ⟶ relativeSpec X 𝒜 // h ≫ toBase X 𝒜 = x} ≃
      {s : T ⟶ relativeSpec T (𝒜.pullback x) // s ≫ toBase T (𝒜.pullback x) = 𝟙 T} where
  toFun h := ⟨(isPullback_relativeSpecPullback 𝒜 x).lift h.1 (𝟙 T)
      (by rw [Category.id_comp]; exact h.2),
    (isPullback_relativeSpecPullback 𝒜 x).lift_snd _ _ _⟩
  invFun s := ⟨s.1 ≫ relativeSpecPullbackFst 𝒜 x, by
    rw [Category.assoc, (isPullback_relativeSpecPullback 𝒜 x).w, ← Category.assoc, s.2,
      Category.id_comp]⟩
  left_inv h := Subtype.ext ((isPullback_relativeSpecPullback 𝒜 x).lift_fst _ _ _)
  right_inv s := Subtype.ext <| by
    dsimp only
    exact (isPullback_relativeSpecPullback 𝒜 x).hom_ext (by simp) (by simp [s.2])

/-- The comparison map from the affine chart of `relativeSpec X 𝒜` over an affine open `U`
agrees, via `gammaHom`, with the algebraic-geometric `fromSpec` of the preimage of `U` in
`relativeSpec X 𝒜`. -/
theorem specMap_gammaHom_comp_fromSpec (𝒜 : AlgebraData X) (U : X.affineOpens) :
    Spec.map (gammaHom X 𝒜 U) ≫ (U.2.preimage (toBase X 𝒜)).fromSpec = affineι X 𝒜 U := by
  have i' : (⊤ : (Spec (.of (𝒜.ring U))).Opens) ≤
      affineι X 𝒜 U ⁻¹ᵁ (toBase X 𝒜 ⁻¹ᵁ U.1) :=
    (affineι_preimage_toBase_preimage X 𝒜 U).ge
  have key := IsAffineOpen.SpecMap_appLE_fromSpec (affineι X 𝒜 U)
    (U.2.preimage (toBase X 𝒜)) (isAffineOpen_top _) i'
  rw [IsAffineOpen.fromSpec_top] at key
  have hisoSpec : (Spec (.of (𝒜.ring U))).isoSpec.inv =
      Spec.map (Scheme.ΓSpecIso (.of (𝒜.ring U))).inv :=
    IsIso.inv_eq_of_hom_inv_id (toSpecΓ_SpecMap_ΓSpecIso_inv (.of (𝒜.ring U)))
  rw [hisoSpec] at key
  have hgamma : gammaHom X 𝒜 U = (affineι X 𝒜 U).appLE (toBase X 𝒜 ⁻¹ᵁ U.1) ⊤ i' ≫
      (Scheme.ΓSpecIso (.of (𝒜.ring U))).hom := rfl
  have happLE : (affineι X 𝒜 U).appLE (toBase X 𝒜 ⁻¹ᵁ U.1) ⊤ i' =
      gammaHom X 𝒜 U ≫ (Scheme.ΓSpecIso (.of (𝒜.ring U))).inv := by
    rw [hgamma, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [happLE, Spec.map_comp, Category.assoc] at key
  exact (cancel_epi (Spec.map (Scheme.ΓSpecIso (.of (𝒜.ring U))).inv)).mp key

-- `X.affineOpens` is not reducibly the subtype `{U // IsAffineOpen U}` it is defeq to (as in
-- Mathlib's own development of relative gluing), so the unifier must not respect transparency
-- when checking the rewritten goal below.
set_option backward.isDefEq.respectTransparency false in
/-- The morphism of relative spectra induced by `Hom.ofOverRelativeSpec` recovers `h` itself
after transporting along `relativeSpecOfAffineHomIso g`. This is the exact inverse identity that
upgrades the universal property of `Hom.ofOverRelativeSpec` to a two-sided correspondence,
proved by comparing both sides on every affine chart of `X` via `RelativeSpec.hom_ext`,
`IsAffineOpen.SpecMap_appLE_fromSpec` and `specMap_gammaHom_comp_fromSpec`. -/
theorem relativeSpecOfAffineHomIso_hom_comp_map {C : Scheme.{u}} (𝒜 : AlgebraData X)
    {g : C ⟶ X} [_root_.AlgebraicGeometry.IsAffineHom g] (h : C ⟶ relativeSpec X 𝒜)
    (hh : h ≫ toBase X 𝒜 = g) :
    (relativeSpecOfAffineHomIso g).hom ≫ h =
      (RelativeSpec.Hom.ofOverRelativeSpec 𝒜 h hh).map := by
  apply RelativeSpec.hom_ext
  intro U
  have hUX : IsAffineOpen U.1 := U.2
  have hUC : IsAffineOpen (g ⁻¹ᵁ U.1) := hUX.preimage g
  have hUY : IsAffineOpen (toBase X 𝒜 ⁻¹ᵁ U.1) := hUX.preimage (toBase X 𝒜)
  have hinv : Spec.map (inv (gammaHom X 𝒜 U)) ≫ affineι X 𝒜 U = hUY.fromSpec := by
    rw [← specMap_gammaHom_comp_fromSpec 𝒜 U, ← Category.assoc, ← Spec.map_comp]
    simp
  have happ : CommRingCat.ofHom
      ((RelativeSpec.Hom.ofOverRelativeSpec 𝒜 h hh).app U).toRingHom =
      inv (gammaHom X 𝒜 U) ≫
        h.appLE (toBase X 𝒜 ⁻¹ᵁ U.1) (g ⁻¹ᵁ U.1)
          (preimage_le_preimage_of_over h hh U.1) := rfl
  have hhom : (relativeSpecOfAffineHomIso g).hom = RelativeSpec.ofAffineHomHom g := rfl
  have hspec : Spec.map (h.appLE (toBase X 𝒜 ⁻¹ᵁ U.1) (g ⁻¹ᵁ U.1)
        (preimage_le_preimage_of_over h hh U.1)) ≫ hUY.fromSpec =
      hUC.fromSpec ≫ h :=
    IsAffineOpen.SpecMap_appLE_fromSpec h hUY hUC (preimage_le_preimage_of_over h hh U.1)
  rw [← Category.assoc, hhom, affineι_ofAffineHomHom, RelativeSpec.Hom.affineι_map, happ,
    Spec.map_comp, Category.assoc, hinv, hspec]

/-- Sections over `T` of the structure map of an algebra `ℬ` on `T` correspond to `T`-algebra
maps out of `ℬ` into the tautological "sections of `T`" algebra `AlgebraData.ofAffineHom (𝟙 T)`,
via `Hom.ofOverRelativeSpec` and its inverse identity `relativeSpecOfAffineHomIso_hom_comp_map`.
Both round trips reduce to that one identity, using `Hom.map_injective` for the algebra-map
side. -/
def sectionEquivAlgebraHom (ℬ : AlgebraData T) :
    {s : T ⟶ relativeSpec T ℬ // s ≫ toBase T ℬ = 𝟙 T} ≃
      RelativeSpec.Hom T (RelativeSpec.AlgebraData.ofAffineHom (𝟙 T)) ℬ where
  toFun s := RelativeSpec.Hom.ofOverRelativeSpec ℬ s.1 s.2
  invFun φ := ⟨(relativeSpecOfAffineHomIso (𝟙 T)).inv ≫ φ.map, by
    rw [Category.assoc, φ.map_toBase, ← relativeSpecOfAffineHomIso_hom_comp (𝟙 T),
      Category.comp_id, Iso.inv_hom_id]⟩
  left_inv s := Subtype.ext <| by
    dsimp only
    rw [← relativeSpecOfAffineHomIso_hom_comp_map ℬ s.1 s.2, Iso.inv_hom_id_assoc]
  right_inv φ := by
    apply RelativeSpec.Hom.map_injective
    dsimp only
    rw [← relativeSpecOfAffineHomIso_hom_comp_map ℬ _ _, Iso.hom_inv_id_assoc]

/-- **The universal property in stack language.** Lifts of a chart `x : T ⟶ X` through
`stackSpec X 𝒜` — morphisms `T ⟶ relativeSpec X 𝒜` over `x` — correspond to `T`-algebra maps out
of the pulled-back algebra data `𝒜.pullback x` into the "sections of `T`" algebra, via
`liftEquivSection` (the pullback universal property) composed with `sectionEquivAlgebraHom`
(the affine universal property of `Hom.ofOverRelativeSpec`). -/
def liftEquivAlgebraHom (𝒜 : AlgebraData X) (x : T ⟶ X) :
    {h : T ⟶ relativeSpec X 𝒜 // h ≫ toBase X 𝒜 = x} ≃
      RelativeSpec.Hom T (RelativeSpec.AlgebraData.ofAffineHom (𝟙 T)) (𝒜.pullback x) :=
  (liftEquivSection 𝒜 x).trans (sectionEquivAlgebraHom (𝒜.pullback x))


/-! ### Item (b): the scheme case -/

/-- For an affine morphism `g : C ⟶ X`, the structure-morphism stack map of the tautological
algebra `AlgebraData.ofAffineHom g` agrees, after transporting along the promoted comparison
isomorphism `relativeSpecOfAffineHomIso g`, with the promoted scheme morphism `g` itself. -/
def stackIso2_stackSpec_ofAffineHom (X C : Scheme.{u}) (g : C ⟶ X)
    [_root_.AlgebraicGeometry.IsAffineHom g] :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp
        (FppfStack.mapOfSchemeHom (relativeSpecOfAffineHomIso g).inv)
        (stackSpec X (RelativeSpec.AlgebraData.ofAffineHom g)))
      (FppfStack.mapOfSchemeHom g) := by
  have hg : (relativeSpecOfAffineHomIso g).inv ≫
      toBase X (RelativeSpec.AlgebraData.ofAffineHom g) = g :=
    (Iso.inv_comp_eq _).mpr (relativeSpecOfAffineHomIso_hom_comp g).symm
  have key := FppfStack.mapOfSchemeHom_comp_iso (relativeSpecOfAffineHomIso g).inv
    (toBase X (RelativeSpec.AlgebraData.ofAffineHom g))
  rw [hg] at key
  exact key


/-! ### Item (c): functoriality -/

/-- A morphism of quasi-coherent algebras induces a 2-commutative triangle of structure-morphism
stack maps over `representedStack X`: composing the promoted induced scheme morphism `φ.map`
with `stackSpec X ℬ` agrees with `stackSpec X 𝒜`, via `Hom.map_toBase`. -/
def stackSpec_triangle {𝒜 ℬ : AlgebraData X} (φ : RelativeSpec.Hom X 𝒜 ℬ) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp (FppfStack.mapOfSchemeHom φ.map) (stackSpec X ℬ))
      (stackSpec X 𝒜) := by
  have key := FppfStack.mapOfSchemeHom_comp_iso φ.map (toBase X ℬ)
  rw [φ.map_toBase] at key
  exact key

/-- The triangle 2-isomorphism for the identity algebra map, via `Hom.map_id`. -/
def stackSpec_triangle_id (𝒜 : AlgebraData X) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp
        (FppfStack.mapOfSchemeHom (𝟙 (relativeSpec X 𝒜))) (stackSpec X 𝒜))
      (stackSpec X 𝒜) := by
  have key := stackSpec_triangle (RelativeSpec.Hom.id 𝒜)
  rw [RelativeSpec.Hom.map_id] at key
  exact key

/-- The triangle 2-isomorphism for a composite algebra map, via `Hom.map_comp`. -/
def stackSpec_triangle_comp {𝒜 ℬ 𝒞 : AlgebraData X}
    (φ : RelativeSpec.Hom X 𝒜 ℬ) (ψ : RelativeSpec.Hom X ℬ 𝒞) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp (FppfStack.mapOfSchemeHom (φ.map ≫ ψ.map)) (stackSpec X 𝒞))
      (stackSpec X 𝒜) := by
  have key := stackSpec_triangle (φ.comp ψ)
  rw [RelativeSpec.Hom.map_comp] at key
  exact key


/-! ### Item (d): examples -/

/-- The normal sheaf `Sym(I/I²)` of a quasi-coherent ideal sheaf, viewed as a morphism of
represented stacks, is representable by affine morphisms. -/
theorem normalSheaf_stackSpec_hasRepresentableProperty_isAffineHom
    (X : Scheme.{u}) (I : X.IdealSheafData) :
    (stackSpec X (NormalSheaf.algebraData X I)).HasRepresentableProperty
      (@_root_.AlgebraicGeometry.IsAffineHom : MorphismProperty Scheme.{u}) :=
  stackSpec_hasRepresentableProperty_isAffineHom X (NormalSheaf.algebraData X I)

/-- The relative `Spec` of the polynomial extension of a quasi-coherent algebra, viewed as a
morphism of represented stacks, is representable by affine morphisms. -/
theorem polynomial_stackSpec_hasRepresentableProperty_isAffineHom (𝒜 : AlgebraData X) :
    (stackSpec X 𝒜.polynomial).HasRepresentableProperty
      (@_root_.AlgebraicGeometry.IsAffineHom : MorphismProperty Scheme.{u}) :=
  stackSpec_hasRepresentableProperty_isAffineHom X 𝒜.polynomial

end

end GromovWitten.AlgebraicGeometry
