/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.DerivedPicard

/-!
# Functoriality of `h¹/h⁰` on arbitrary derived morphisms

`Cones/DerivedPicard.lean` shows that any two global two-term resolutions of the *same*
derived object have equivalent Picard groupoids `h¹/h⁰`, via a chain map realizing the
identity comparison isomorphism.  This file extends the realization step to an arbitrary
(not necessarily invertible) morphism `f : E ⟶ E'` of the derived category, and uses it to
build an induced functor of Picard groupoids for every such `f`.

## Main declarations

* `GlobalTwoTermResolution.exists_chain_realization_of_hom`: every morphism between the
  images of two global two-term resolutions in the derived category is realized by an actual
  chain map; this generalizes `exists_chain_realization` (which only treats the specific
  comparison isomorphism attached to a shared resolved object) to an arbitrary morphism,
  using only K-projectivity of the source.
* `GlobalTwoTermResolution.realize`/`realize_spec`: a chosen chain-map realization of a
  derived morphism `f : E ⟶ E'` between two resolutions `F`, `F'`.
* `GlobalTwoTermResolution.realize_unique_upto_homotopy`: any two chain maps realizing the
  same derived morphism (in particular, two realizations produced by `realize`, or a
  realization compared with `realize f` itself) are chain homotopic.
* `GlobalTwoTermResolution.picardMap`: the induced functor `F.picard ⥤ F'.picard` on Picard
  groupoids attached to a derived morphism `f : E ⟶ E'` and a choice of resolutions `F`, `F'`.
* `GlobalTwoTermResolution.picardMap_id`, `GlobalTwoTermResolution.picardMap_comp`: the
  induced functor of the identity morphism is naturally isomorphic to the identity functor,
  and the induced functor of a composite is naturally isomorphic to the composite of the
  induced functors, both produced from `realize_unique_upto_homotopy` via
  `LinearTwoTermComplex.ChainHomotopy.natIso`.
* `GlobalTwoTermResolution.picardEquivOfIso`: when `f` is an isomorphism, `picardMap f.hom` is
  promoted to an honest equivalence of Picard groupoids, with quasi-inverse `picardMap f.inv`,
  using `Equivalence.mk` together with `picardMap_id`/`picardMap_comp`.

## What is not proved

The chain map `realize f` is chosen arbitrarily among the (in general more than one) chain
maps realizing `f`, and is therefore not canonical; correspondingly the natural isomorphisms
`picardMap_id`/`picardMap_comp` are built from an arbitrarily chosen chain homotopy witness
(`realize_unique_upto_homotopy` only produces a `Nonempty` statement). Distinct chain
homotopies between the same pair of chain maps can induce distinct natural isomorphisms on
Picard groupoids (a self-homotopy of a fixed chain map need not be trivial: it need only kill
the differential on both sides, and that is generally a nontrivial condition already noted as
unresolved in `Cones/DerivedPicard.lean`'s "What is not proved" section). Consequently no
pentagon/unit coherence statement for `picardMap_comp`/`picardMap_id` (i.e. genuine
pseudofunctoriality on the nose, beyond the individual comparison isomorphisms proved here) is
attempted: such a statement would either have to specify a canonical choice of `realize` and of
the comparison homotopies (not done anywhere in this development) or be reformulated at the
level of homotopy classes, which is beyond the scope of this file.
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry.CotangentComplex.PerfectComplex

universe u

variable {R : Type u} [CommRing R]

attribute [local instance] HasDerivedCategory.standard

namespace GlobalTwoTermResolution

variable {E E' E'' : DerivedCategory (ModuleCat.{u} R)}

/-! ## Realizing an arbitrary derived morphism by a chain map -/

/-- **Realization of a general derived morphism.**  Every morphism between the images of two
global two-term resolutions in the derived category is realized by an actual chain map between
the resolving complexes.  This is the same argument as `exists_chain_realization`, generalized
from the specific comparison isomorphism `F.iso ≪≫ F'.iso.symm` to an arbitrary morphism `g`;
only K-projectivity of the source complex `F.complex` is used. -/
theorem exists_chain_realization_of_hom {F : GlobalTwoTermResolution E}
    {F' : GlobalTwoTermResolution E'}
    (g : DerivedCategory.Q.obj F.complex ⟶ DerivedCategory.Q.obj F'.complex) :
    ∃ φ : F.complex ⟶ F'.complex, DerivedCategory.Q.map φ = g := by
  have hK := F.isKProjective
  obtain ⟨γ, hγ⟩ :=
    (CochainComplex.IsKProjective.Qh_map_bijective F.complex
      ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj
        F'.complex)).surjective
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app F.complex ≫
        g ≫
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app F'.complex)
  obtain ⟨φ, rfl⟩ :=
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map_surjective γ
  refine ⟨φ, ?_⟩
  have hnat := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.naturality φ
  rw [Functor.comp_map, hγ] at hnat
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at hnat
  exact ((cancel_epi _).mp hnat).symm

/-- A chosen chain map realizing a derived morphism `f : E ⟶ E'`, relative to global two-term
resolutions `F` of `E` and `F'` of `E'`.  See `realize_spec` for what it realizes and
`realize_unique_upto_homotopy` for what is canonical about it. -/
noncomputable def realize {F : GlobalTwoTermResolution E} {F' : GlobalTwoTermResolution E'}
    (f : E ⟶ E') : F.complex ⟶ F'.complex :=
  (exists_chain_realization_of_hom (F.iso.hom ≫ f ≫ F'.iso.inv)).choose

/-- The chain map `realize f` realizes `f` after transporting along the resolution
isomorphisms. -/
theorem realize_spec {F : GlobalTwoTermResolution E} {F' : GlobalTwoTermResolution E'}
    (f : E ⟶ E') :
    DerivedCategory.Q.map (realize f) = F.iso.hom ≫ f ≫ F'.iso.inv :=
  (exists_chain_realization_of_hom (F.iso.hom ≫ f ≫ F'.iso.inv)).choose_spec

/-- **Uniqueness up to homotopy.**  Two chain maps between the same pair of resolutions which
realize the same derived morphism are chain homotopic.  This is the injectivity of the same
bijection `CochainComplex.IsKProjective.Qh_map_bijective` used for existence, combined with the
identification of morphisms in the homotopy category with homotopy classes of chain maps
(`HomotopyCategory.homotopyOfEq`). -/
theorem realize_unique_upto_homotopy {F : GlobalTwoTermResolution E}
    {F' : GlobalTwoTermResolution E'} {φ₁ φ₂ : F.complex ⟶ F'.complex}
    (h : DerivedCategory.Q.map φ₁ = DerivedCategory.Q.map φ₂) :
    Nonempty (Homotopy φ₁ φ₂) := by
  have hK := F.isKProjective
  have h1 := DerivedCategory.quotientCompQhIso_hom_naturality φ₁
  have h2 := DerivedCategory.quotientCompQhIso_hom_naturality φ₂
  rw [h] at h1
  have hQh :
      DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map φ₁) =
        DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map φ₂) :=
    (cancel_mono _).mp (h1.trans h2.symm)
  have hquot :
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map φ₁ =
        (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map φ₂ :=
    (CochainComplex.IsKProjective.Qh_map_bijective F.complex
      ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj
        F'.complex)).injective hQh
  exact ⟨HomotopyCategory.homotopyOfEq φ₁ φ₂ hquot⟩

/-! ## The induced functor on Picard groupoids -/

/-- The two-term chain map underlying `realize f`. -/
noncomputable def realizeHom {F : GlobalTwoTermResolution E} {F' : GlobalTwoTermResolution E'}
    (f : E ⟶ E') : LinearTwoTermComplex.Hom F.linearComplex F'.linearComplex :=
  LinearTwoTermComplex.ofCochainComplexHom (realize f)

/-- **The functor induced on Picard groupoids by a derived morphism.**  Given a derived morphism
`f : E ⟶ E'` and global two-term resolutions `F` of `E`, `F'` of `E'`, this is the functor of
translation groupoids `h¹/h⁰(E) ⥤ h¹/h⁰(E')` induced by the chain-level realization
`realizeHom f`; it agrees with `LinearTwoTermComplex.picardFunctor.map (realizeHom f)` up to the
trivial identification of `Cat`-morphisms with functors. -/
noncomputable def picardMap {F : GlobalTwoTermResolution E} {F' : GlobalTwoTermResolution E'}
    (f : E ⟶ E') : F.picard ⥤ F'.picard :=
  (realizeHom f).quotientFunctor

/-- **Identity coherence.**  The functor induced by the identity derived morphism is naturally
isomorphic to the identity functor of the Picard groupoid, via the chain homotopy between
`realize (𝟙 E)` and the identity chain map furnished by `realize_unique_upto_homotopy`. -/
noncomputable def picardMap_id (F : GlobalTwoTermResolution E) :
    picardMap (F := F) (F' := F) (𝟙 E) ≅ 𝟭 F.picard := by
  have H : Homotopy (realize (F := F) (F' := F) (𝟙 E)) (𝟙 F.complex) :=
    Classical.choice (realize_unique_upto_homotopy (by simp [realize_spec]))
  have HC := LinearTwoTermComplex.ofHomotopy (F.supported 1 (Or.inr (by norm_num)))
    (F.supported (-2) (Or.inl (by norm_num))) H
  exact HC.natIso.symm ≪≫ eqToIso (by simp)

/-- **Composition coherence.**  The functor induced by a composite derived morphism `f ≫ g` is
naturally isomorphic to the composite of the induced functors, via the chain homotopy between
`realize (f ≫ g)` and `realize f ≫ realize g` furnished by `realize_unique_upto_homotopy`. -/
noncomputable def picardMap_comp {F : GlobalTwoTermResolution E} {F' : GlobalTwoTermResolution E'}
    {F'' : GlobalTwoTermResolution E''} (f : E ⟶ E') (g : E' ⟶ E'') :
    picardMap (F := F) (F' := F'') (f ≫ g) ≅
      picardMap (F := F) (F' := F') f ⋙ picardMap (F := F') (F' := F'') g := by
  have H : Homotopy (realize (F := F) (F' := F'') (f ≫ g))
      (realize (F := F) (F' := F') f ≫ realize (F := F') (F' := F'') g) :=
    Classical.choice (realize_unique_upto_homotopy (by
      simp [realize_spec, Category.assoc, Iso.inv_hom_id_assoc]))
  have HC := LinearTwoTermComplex.ofHomotopy (F.supported 1 (Or.inr (by norm_num)))
    (F''.supported (-2) (Or.inl (by norm_num))) H
  exact HC.natIso.symm ≪≫ eqToIso (by simp [picardMap, realizeHom])

/-! ## Compatibility with isomorphisms -/

/-- **When `f` is an isomorphism, `picardMap f.hom` is an equivalence.**  The quasi-inverse is
`picardMap f.inv`, and the unit/counit isomorphisms come from `picardMap_comp`/`picardMap_id`
applied to `f.hom_inv_id`/`f.inv_hom_id`; `Equivalence.mk` supplies the triangle identity. -/
noncomputable def picardEquivOfIso {F : GlobalTwoTermResolution E}
    {F' : GlobalTwoTermResolution E'} (f : E ≅ E') : F.picard ≌ F'.picard :=
  CategoryTheory.Equivalence.mk (picardMap (F := F) (F' := F') f.hom)
    (picardMap (F := F') (F' := F) f.inv)
    ((picardMap_id F).symm ≪≫
      eqToIso (congrArg (fun h : E ⟶ E => picardMap (F := F) (F' := F) h) f.hom_inv_id.symm) ≪≫
      picardMap_comp f.hom f.inv)
    ((picardMap_comp f.inv f.hom).symm ≪≫
      eqToIso (congrArg (fun h : E' ⟶ E' => picardMap (F := F') (F' := F') h) f.inv_hom_id) ≪≫
      picardMap_id F')

/-- The equivalence `picardEquivOfIso f` has forward functor `picardMap f.hom`, so `picardMap
f.hom` is an equivalence of categories whenever `f` is an isomorphism of the derived
category. -/
instance isEquivalence_picardMap_of_iso {F : GlobalTwoTermResolution E}
    {F' : GlobalTwoTermResolution E'} (f : E ≅ E') :
    (picardMap (F := F) (F' := F') f.hom).IsEquivalence :=
  CategoryTheory.Equivalence.isEquivalence_functor (picardEquivOfIso f)

end GlobalTwoTermResolution

end GromovWitten.AlgebraicGeometry.CotangentComplex.PerfectComplex
