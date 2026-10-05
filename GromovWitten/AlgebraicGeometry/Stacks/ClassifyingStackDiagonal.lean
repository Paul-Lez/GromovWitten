/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Stacks.TorsorIsomSheaf
import GromovWitten.AlgebraicGeometry.Stacks.ConstantGroup
import GromovWitten.AlgebraicGeometry.Stacks.TorsorIsomRepresentable

/-!
# The diagonal of `BG` and the Deligne–Mumford stack `BG`

Let `x y : ActionTorsor G U T` be two objects of the quotient stack `[U/G]` over `T` whose
underlying torsors are represented by schemes (`RP`, `RQ`), and let the isomorphism sheaf
`isomSheaf x y RP RQ` (`Stacks/TorsorIsomSheaf.lean`) be represented by a scheme `W` over `T`:
`e : fppfYoneda.obj W ≅ isomSheaf x y RP RQ` with `e.hom ≫ isomProjection x y RP RQ =
fppfYoneda.map w`.  This file packages such a representation as a `DiagonalPresentation
[U/G] T x y`: the universal isomorphism is the fibre isomorphism attached (by
`isomPointEquiv`) to the `W`-point `fppfJ.yonedaEquiv e.hom`, the lift of an isomorphism
`f^* x ≅ f^* y` over `S` is the `S`-point of `W` corresponding to it under `e`, and the
classification property `DiagonalClassifies` is the naturality of `isomPointEquiv`
(`isomPointEquiv_restrict`).

For `G = affineGroup R grp` with `R` finite étale over `ℤ` and `Spec R → Spec ℤ` surjective,
every torsor is represented by a scheme and every isomorphism sheaf is represented by a scheme
(`exists_isomRepresentation`, `Stacks/TorsorIsomRepresentable.lean`), so the diagonal of
`BG = classifyingStack G` is representable; together with the étale surjective atlas `pt → BG`
this makes `BG` an algebraic and indeed a Deligne–Mumford stack.  The specialisation to the
constant finite group `constantGroup Γ` of `Stacks/ConstantGroup.lean` is
`constantClassifyingDeligneMumfordStack Γ`.

## Main results

* `DiagonalClassifies.of_sigma_eq` / `DiagonalClassifies.sigma_eq`: the classification
  property `DiagonalClassifies X map univ f e g` is the equality of the pairs
  `(g ≫ map, stackPullbackIso X g map univ)` and `(f, e)` in `Σ f, (f^* x ≅ f^* y)`.
* `ActionTorsor.isomUniversalPoint`, `ActionTorsor.isomLift`: the universal point of a
  representation of the isomorphism sheaf, and the lift of a fibre isomorphism to the
  representing scheme; `ActionTorsor.isomUniversalPoint_restrict_isomLift`,
  `ActionTorsor.isomLift_map`.
* `ActionTorsor.isomDiagonalPresentationOfRepresentation x y RP RQ e w he :
    DiagonalPresentation (quotientStack G U) T x y`, and its restatement
  `ActionTorsor.isomDiagonalPresentationClassifying` for `BG = classifyingStack G`;
  `ActionTorsor.hasRepresentableDiagonal_quotientStack_of_isomRepresentation`: the diagonal of
  `[U/G]` is representable once all torsors and all isomorphism sheaves are represented.
* `StackChart.isSmoothSurjective_of_isEtaleSurjective`: an étale surjective chart is smooth
  surjective.
* Using the representability theorem `ActionTorsor.exists_isomRepresentation` of
  `Stacks/TorsorIsomRepresentable.lean`:
  `ActionTorsor.hasRepresentableDiagonal_classifyingStack` (`HasRepresentableDiagonal
  (classifyingStack (affineGroup R grp))` for `R` finite étale over `ℤ` with `Spec R → Spec ℤ`
  surjective), `ActionTorsor.classifyingAlgebraicStack`,
  `ActionTorsor.classifyingDeligneMumfordStack` (`BG` as an algebraic and as a Deligne–Mumford
  stack, atlas `classifyingAtlasChart G`), and `constantClassifyingDeligneMumfordStack Γ` (`BΓ`
  for a finite group `Γ`, no further hypotheses).
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

/-! ### Classification as an equality of pairs -/

section Classifies

variable (X : FppfStack.{u})

/-- Transport of an isomorphism `f₁^* x ≅ f₁^* y` along an equality `f₁ = f₂` of test maps,
through the canonical identifications `stackPullbackObjIsoOfEq`. -/
noncomputable def stackIsoOfMapEq {S T : Scheme.{u}} {f₁ f₂ : S ⟶ T} (h : f₁ = f₂)
    {x y : StackFiber X T}
    (e : (stackPullback X f₁).obj x ≅ (stackPullback X f₁).obj y) :
    (stackPullback X f₂).obj x ≅ (stackPullback X f₂).obj y :=
  (stackPullbackObjIsoOfEq X h x).symm ≪≫ e ≪≫ stackPullbackObjIsoOfEq X h y

/-- Transport along `rfl` is the identity. -/
@[simp]
theorem stackIsoOfMapEq_rfl {S T : Scheme.{u}} {f : S ⟶ T} {x y : StackFiber X T}
    (e : (stackPullback X f).obj x ≅ (stackPullback X f).obj y) :
    stackIsoOfMapEq X rfl e = e := by
  apply Iso.ext
  simp [stackIsoOfMapEq, stackPullbackObjIsoOfEq]

/-- Transport along an equality of test maps turns a heterogeneous equality of isomorphisms into
an equality. -/
theorem stackIsoOfMapEq_eq_of_heq {S T : Scheme.{u}} {f₁ f₂ : S ⟶ T} (h : f₁ = f₂)
    {x y : StackFiber X T}
    {e₁ : (stackPullback X f₁).obj x ≅ (stackPullback X f₁).obj y}
    {e₂ : (stackPullback X f₂).obj x ≅ (stackPullback X f₂).obj y} (hh : HEq e₁ e₂) :
    stackIsoOfMapEq X h e₁ = e₂ := by
  subst h
  rw [stackIsoOfMapEq_rfl]
  exact eq_of_heq hh

variable {X}

namespace DiagonalClassifies

variable {U T : Scheme.{u}} {map : U ⟶ T} {x y : StackFiber X T}
  {universal : (stackPullback X map).obj x ≅ (stackPullback X map).obj y}
  {S : Scheme.{u}} {f : S ⟶ T} {e : (stackPullback X f).obj x ≅ (stackPullback X f).obj y}
  {g : S ⟶ U}

/-- **Classification from an equality of pairs**: `g` classifies `e` over `f` as soon as the
pair `(g ≫ map, stackPullbackIso X g map universal)` equals `(f, e)` in
`Σ f, (f^* x ≅ f^* y)`. -/
theorem of_sigma_eq
    (h : (⟨g ≫ map, stackPullbackIso X g map universal⟩ :
        Σ f : S ⟶ T, ((stackPullback X f).obj x ≅ (stackPullback X f).obj y)) = ⟨f, e⟩) :
    DiagonalClassifies X map universal f e g := by
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 h
  exact ⟨h1, stackIsoOfMapEq_eq_of_heq X h1 h2⟩

/-- **Classification as an equality of pairs** (converse of `of_sigma_eq`). -/
theorem sigma_eq (hc : DiagonalClassifies X map universal f e g) :
    (⟨g ≫ map, stackPullbackIso X g map universal⟩ :
        Σ f : S ⟶ T, ((stackPullback X f).obj x ≅ (stackPullback X f).obj y)) = ⟨f, e⟩ := by
  obtain ⟨h1, h2⟩ := hc
  subst h1
  refine Sigma.ext rfl (heq_of_eq ?_)
  rw [← h2]
  apply Iso.ext
  simp [stackPullbackObjIsoOfEq, diagonalInducedIso]

/-- Classification is invariant under transport of the presenting map along an equality. -/
theorem of_map_eq {map' : U ⟶ T} (h : map = map')
    (hc : DiagonalClassifies X map universal f e g) :
    DiagonalClassifies X map' (stackIsoOfMapEq X h universal) f e g := by
  subst h
  rw [stackIsoOfMapEq_rfl]
  exact hc

/-- Classification is reflected by transport of the presenting map along an equality. -/
theorem of_map_eq_transport {map' : U ⟶ T} (h : map = map')
    (hc : DiagonalClassifies X map' (stackIsoOfMapEq X h universal) f e g) :
    DiagonalClassifies X map universal f e g := by
  subst h
  rw [stackIsoOfMapEq_rfl] at hc
  exact hc

end DiagonalClassifies

end Classifies

namespace ActionTorsor

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G} {T : Scheme.{u}}

/-! ### The diagonal presentation attached to a representation of the isomorphism sheaf -/

section Presentation

variable (x y : ActionTorsor G U T) (RP : TorsorRepresentation x.toFppfTorsor)
  (RQ : TorsorRepresentation y.toFppfTorsor) {W : Scheme.{u}}
  (e : fppfYoneda.obj W ≅ isomSheaf x y RP RQ)

/-- The universal point of a representation `e` of the isomorphism sheaf: the `W`-point
corresponding to `e.hom` under the Yoneda lemma. -/
noncomputable def isomUniversalPoint : IsomPoint x y RP RQ W :=
  fppfJ.yonedaEquiv e.hom

/-- Restricting the universal point along `g : S ⟶ W` gives the point corresponding to
`fppfYoneda.map g ≫ e.hom`. -/
theorem isomUniversalPoint_restrict {S : Scheme.{u}} (g : S ⟶ W) :
    (isomUniversalPoint x y RP RQ e).restrict g = fppfJ.yonedaEquiv (fppfYoneda.map g ≫ e.hom) :=
  GrothendieckTopology.yonedaEquiv_naturality (J := fppfJ.{u}) e.hom g

/-- The test map of the universal point is the structure map `w` of the representation. -/
theorem isomUniversalPoint_f (w : W ⟶ T)
    (he : e.hom ≫ isomProjection x y RP RQ = fppfYoneda.map w) :
    (isomUniversalPoint x y RP RQ e).f = w := by
  apply fppfYoneda.map_injective
  rw [← he, comp_isomProjection]
  rfl

/-- **The lift of a fibre isomorphism to the representing scheme**: the `S`-point of `W`
corresponding under `e` to the point `(f, e')` of the isomorphism sheaf. -/
noncomputable def isomLift {S : Scheme.{u}} (f : S ⟶ T)
    (e' : (stackPullback (quotientStack G U) f).obj x ≅
      (stackPullback (quotientStack G U) f).obj y) : S ⟶ W :=
  fppfJ.yonedaEquiv
    (fppfJ.yonedaEquiv.symm ((isomPointEquiv x y RP RQ S).symm ⟨f, e'⟩) ≫ e.inv)

/-- The sheaf map of the lift. -/
theorem fppfYoneda_map_isomLift {S : Scheme.{u}} (f : S ⟶ T)
    (e' : (stackPullback (quotientStack G U) f).obj x ≅
      (stackPullback (quotientStack G U) f).obj y) :
    fppfYoneda.map (isomLift x y RP RQ e f e') =
      fppfJ.yonedaEquiv.symm ((isomPointEquiv x y RP RQ S).symm ⟨f, e'⟩) ≫ e.inv := by
  apply fppfJ.yonedaEquiv.injective
  rw [GrothendieckTopology.yonedaEquiv_yoneda_map]
  rfl

/-- The universal point restricted along the lift of `(f, e')` is the point of `(f, e')`. -/
theorem isomUniversalPoint_restrict_isomLift {S : Scheme.{u}} (f : S ⟶ T)
    (e' : (stackPullback (quotientStack G U) f).obj x ≅
      (stackPullback (quotientStack G U) f).obj y) :
    (isomUniversalPoint x y RP RQ e).restrict (isomLift x y RP RQ e f e') =
      (isomPointEquiv x y RP RQ S).symm ⟨f, e'⟩ := by
  rw [isomUniversalPoint_restrict, fppfYoneda_map_isomLift, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  exact Equiv.apply_symm_apply _ _

/-- The lift lies over `f`. -/
theorem isomLift_map (w : W ⟶ T) (he : e.hom ≫ isomProjection x y RP RQ = fppfYoneda.map w)
    {S : Scheme.{u}} (f : S ⟶ T)
    (e' : (stackPullback (quotientStack G U) f).obj x ≅
      (stackPullback (quotientStack G U) f).obj y) :
    isomLift x y RP RQ e f e' ≫ w = f := by
  apply fppfYoneda.map_injective
  rw [Functor.map_comp, ← he, fppfYoneda_map_isomLift, Category.assoc, Iso.inv_hom_id_assoc,
    comp_isomProjection]
  have hp := (fppfJ.yonedaEquiv (F := isomSheaf x y RP RQ)).apply_symm_apply
    ((isomPointEquiv x y RP RQ S).symm ⟨f, e'⟩)
  rw [hp]
  rfl

/-- The pair attached to the restriction of the universal point along `g : S ⟶ W` is
`(g ≫ w₀, stackPullbackIso g w₀ univ)`, where `w₀` is the test map of the universal point and
`univ` its fibre isomorphism. -/
theorem isomPointEquiv_isomUniversalPoint_restrict {S : Scheme.{u}} (g : S ⟶ W) :
    isomPointEquiv x y RP RQ S ((isomUniversalPoint x y RP RQ e).restrict g) =
      ⟨g ≫ (isomUniversalPoint x y RP RQ e).f,
        stackPullbackIso (quotientStack G U) g (isomUniversalPoint x y RP RQ e).f
          (isomPointEquiv x y RP RQ W (isomUniversalPoint x y RP RQ e)).2⟩ :=
  Sigma.ext rfl (heq_of_eq (isomPointEquiv_restrict x y RP RQ g _))

/-- Two maps to the representing scheme along which the universal point has the same
restriction are equal. -/
theorem eq_of_isomUniversalPoint_restrict_eq {S : Scheme.{u}} {g g' : S ⟶ W}
    (h : (isomUniversalPoint x y RP RQ e).restrict g =
      (isomUniversalPoint x y RP RQ e).restrict g') : g = g' := by
  rw [isomUniversalPoint_restrict, isomUniversalPoint_restrict] at h
  have h' := fppfJ.yonedaEquiv.injective h
  rw [cancel_mono] at h'
  exact fppfYoneda.map_injective h'

variable (w : W ⟶ T) (he : e.hom ≫ isomProjection x y RP RQ = fppfYoneda.map w)

/-- **The universal isomorphism** `w^* x ≅ w^* y` of a representation of the isomorphism sheaf:
the fibre isomorphism attached to the universal point, transported to the structure map `w`. -/
noncomputable def isomUniversalIso :
    (stackPullback (quotientStack G U) w).obj x ≅ (stackPullback (quotientStack G U) w).obj y :=
  stackIsoOfMapEq (quotientStack G U) (isomUniversalPoint_f x y RP RQ e w he)
    (isomPointEquiv x y RP RQ W (isomUniversalPoint x y RP RQ e)).2

/-- The lift of `(f, e')` classifies `e'`. -/
theorem isomLift_classifies {S : Scheme.{u}} (f : S ⟶ T)
    (e' : (stackPullback (quotientStack G U) f).obj x ≅
      (stackPullback (quotientStack G U) f).obj y) :
    DiagonalClassifies (quotientStack G U) w (isomUniversalIso x y RP RQ e w he) f e'
      (isomLift x y RP RQ e f e') := by
  refine DiagonalClassifies.of_map_eq (isomUniversalPoint_f x y RP RQ e w he) ?_
  refine DiagonalClassifies.of_sigma_eq ?_
  rw [← isomPointEquiv_isomUniversalPoint_restrict, isomUniversalPoint_restrict_isomLift]
  exact Equiv.apply_symm_apply _ _

/-- Any map classifying `e'` over `f` is the lift of `(f, e')`. -/
theorem eq_isomLift_of_classifies {S : Scheme.{u}} (f : S ⟶ T)
    (e' : (stackPullback (quotientStack G U) f).obj x ≅
      (stackPullback (quotientStack G U) f).obj y) (g : S ⟶ W)
    (hc : DiagonalClassifies (quotientStack G U) w (isomUniversalIso x y RP RQ e w he) f e' g) :
    g = isomLift x y RP RQ e f e' := by
  have h := (DiagonalClassifies.of_map_eq_transport (isomUniversalPoint_f x y RP RQ e w he)
    hc).sigma_eq
  rw [← isomPointEquiv_isomUniversalPoint_restrict] at h
  apply eq_of_isomUniversalPoint_restrict_eq x y RP RQ e
  rw [isomUniversalPoint_restrict_isomLift]
  exact (isomPointEquiv x y RP RQ S).eq_symm_apply.2 h

/-- **The diagonal presentation of `[U/G]` at `(x, y)` attached to a representation of the
isomorphism sheaf**: a scheme `W` over `T` with `fppfYoneda.obj W ≅ isomSheaf x y RP RQ` over
`T` is a `DiagonalPresentation (quotientStack G U) T x y` with space `W` and structure map
`w`. -/
noncomputable def isomDiagonalPresentationOfRepresentation :
    DiagonalPresentation (quotientStack G U) T x y where
  space := W
  map := w
  universalIso := isomUniversalIso x y RP RQ e w he
  lift f e' := isomLift x y RP RQ e f e'
  lift_map f e' := isomLift_map x y RP RQ e w he f e'
  lift_compatible f e' := isomLift_classifies x y RP RQ e w he f e'
  lift_unique f e' g hc := eq_isomLift_of_classifies x y RP RQ e w he f e' g hc

/-- The space of the presentation is `W`. -/
@[simp]
theorem isomDiagonalPresentationOfRepresentation_space :
    (isomDiagonalPresentationOfRepresentation x y RP RQ e w he).space = W :=
  rfl

/-- The structure map of the presentation is `w`. -/
@[simp]
theorem isomDiagonalPresentationOfRepresentation_map :
    (isomDiagonalPresentationOfRepresentation x y RP RQ e w he).map = w :=
  rfl

/-- The universal isomorphism of the presentation is `isomUniversalIso`. -/
@[simp]
theorem isomDiagonalPresentationOfRepresentation_universalIso :
    (isomDiagonalPresentationOfRepresentation x y RP RQ e w he).universalIso =
      isomUniversalIso x y RP RQ e w he :=
  rfl

/-- The lifts of the presentation are `isomLift`. -/
@[simp]
theorem isomDiagonalPresentationOfRepresentation_lift {S : Scheme.{u}} (f : S ⟶ T)
    (e' : (stackPullback (quotientStack G U) f).obj x ≅
      (stackPullback (quotientStack G U) f).obj y) :
    (isomDiagonalPresentationOfRepresentation x y RP RQ e w he).lift f e' =
      isomLift x y RP RQ e f e' :=
  rfl

end Presentation

/-- **The diagonal of `[U/G]` is representable** as soon as, for every pair of objects over
every scheme, the underlying torsors are represented by schemes and the isomorphism sheaf is
represented by a scheme over the base. -/
theorem hasRepresentableDiagonal_quotientStack_of_isomRepresentation
    (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G)
    (h : ∀ (T : Scheme.{u}) (x y : ActionTorsor G U T),
      ∃ (RP : TorsorRepresentation x.toFppfTorsor) (RQ : TorsorRepresentation y.toFppfTorsor)
        (W : Scheme.{u}) (w : W ⟶ T) (e : fppfYoneda.obj W ≅ isomSheaf x y RP RQ),
        e.hom ≫ isomProjection x y RP RQ = fppfYoneda.map w) :
    HasRepresentableDiagonal (quotientStack G U) := by
  intro T x y
  obtain ⟨RP, RQ, W, w, e, he⟩ := h T x y
  exact ⟨isomDiagonalPresentationOfRepresentation x y RP RQ e w he⟩

/-! ### The classifying stack `BG` -/

section Classifying

variable (x y : ActionTorsor G (AlgebraicSpaceAction.pointAction G) T)
  (RP : TorsorRepresentation x.toFppfTorsor) (RQ : TorsorRepresentation y.toFppfTorsor)
  {W : Scheme.{u}} (e : fppfYoneda.obj W ≅ isomSheaf x y RP RQ) (w : W ⟶ T)
  (he : e.hom ≫ isomProjection x y RP RQ = fppfYoneda.map w)

/-- `isomDiagonalPresentationOfRepresentation` for the classifying stack `BG`
(`classifyingStack G` is by definition `quotientStack G (pointAction G)`). -/
noncomputable def isomDiagonalPresentationClassifying :
    DiagonalPresentation (classifyingStack G) T x y :=
  isomDiagonalPresentationOfRepresentation x y RP RQ e w he

/-- The space of the presentation of `BG` is `W`. -/
@[simp]
theorem isomDiagonalPresentationClassifying_space :
    (isomDiagonalPresentationClassifying x y RP RQ e w he).space = W :=
  rfl

/-- The structure map of the presentation of `BG` is `w`. -/
@[simp]
theorem isomDiagonalPresentationClassifying_map :
    (isomDiagonalPresentationClassifying x y RP RQ e w he).map = w :=
  rfl

end Classifying

end ActionTorsor

/-! ### Étale surjective charts are smooth surjective -/

/-- Étale surjective scheme morphisms are smooth surjective. -/
theorem etaleSurjective_le_smoothSurjective :
    ((@_root_.AlgebraicGeometry.Etale ⊓ @_root_.AlgebraicGeometry.Surjective) :
      MorphismProperty Scheme.{u}) ≤
      ((@_root_.AlgebraicGeometry.Smooth ⊓ @_root_.AlgebraicGeometry.Surjective) :
        MorphismProperty Scheme.{u}) :=
  fun _ _ _ hf ↦ ⟨let _ := hf.1; inferInstance, hf.2⟩

/-- An étale surjective chart is a smooth surjective chart. -/
theorem StackChart.isSmoothSurjective_of_isEtaleSurjective {X : FppfStack.{u}}
    (A : StackChart X) (h : A.IsEtaleSurjective) : A.IsSmoothSurjective :=
  ⟨h.1, fun T x p ↦ etaleSurjective_le_smoothSurjective _ (h.2 T x p)⟩

/-! ### `BG` as a Deligne–Mumford stack

The isomorphism sheaf of two objects of `BG` is represented by a scheme étale and finite over
the base (`ActionTorsor.exists_isomRepresentation`, `Stacks/TorsorIsomRepresentable.lean`),
so the diagonal of `BG` is representable and `BG` is an algebraic, indeed Deligne–Mumford,
stack. -/

namespace ActionTorsor

variable {R : Type u} [CommRing R] {grp : GrpObj (fppfYoneda.obj (Spec (CommRingCat.of R)))}

/-- **The diagonal of `BG` is representable** for `G = affineGroup R grp` with `R` finite étale
over `ℤ` and `Spec R → Spec ℤ` surjective: every isomorphism sheaf of two torsors is represented
by a scheme (`exists_isomRepresentation`). -/
theorem hasRepresentableDiagonal_classifyingStack [Algebra.Etale ℤ R] [Module.Finite ℤ R]
    (hR : _root_.AlgebraicGeometry.Surjective
      (@Spec.map (CommRingCat.of TorsorZu.{u}) (CommRingCat.of R)
        (CommRingCat.ofHom (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R))))) :
    HasRepresentableDiagonal (classifyingStack (affineGroup R grp)) := by
  intro T x y
  obtain ⟨RP, -⟩ :=
    FppfTorsor.exists_torsorRepresentation_affineGroup_of_int hR
      (ActionTorsor.toFppfTorsor (G := affineGroup R grp)
        (U := AlgebraicSpaceAction.pointAction _) (T := T) x)
  obtain ⟨RQ, -⟩ :=
    FppfTorsor.exists_torsorRepresentation_affineGroup_of_int hR
      (ActionTorsor.toFppfTorsor (G := affineGroup R grp)
        (U := AlgebraicSpaceAction.pointAction _) (T := T) y)
  obtain ⟨W, w, e, he, -, -⟩ := exists_isomRepresentation x y RP RQ
  exact ⟨isomDiagonalPresentationClassifying x y RP RQ e w he⟩

/-- **`BG` as an algebraic stack**, for `G = affineGroup R grp` with `R` finite étale over `ℤ`
and `Spec R → Spec ℤ` surjective: the diagonal is representable
(`hasRepresentableDiagonal_classifyingStack`) and the atlas `pt → BG` is étale surjective, hence
smooth surjective. -/
noncomputable def classifyingAlgebraicStack [Algebra.Etale ℤ R] [Module.Finite ℤ R]
    (hR : _root_.AlgebraicGeometry.Surjective
      (@Spec.map (CommRingCat.of TorsorZu.{u}) (CommRingCat.of R)
        (CommRingCat.ofHom (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R))))) :
    AlgebraicStack.{u} where
  toStack := classifyingStack (affineGroup R grp)
  diagonal_representable := hasRepresentableDiagonal_classifyingStack hR
  smoothAtlas := ⟨classifyingAtlasChart (affineGroup R grp),
    (classifyingAtlasChart (affineGroup R grp)).isSmoothSurjective_of_isEtaleSurjective
      (classifyingAtlasChart_affineGroup_isEtaleSurjective_of_int hR)⟩

/-- The underlying stack of `classifyingAlgebraicStack` is `BG`. -/
@[simp]
theorem classifyingAlgebraicStack_toStack [Algebra.Etale ℤ R] [Module.Finite ℤ R]
    (hR : _root_.AlgebraicGeometry.Surjective
      (@Spec.map (CommRingCat.of TorsorZu.{u}) (CommRingCat.of R)
        (CommRingCat.ofHom (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R))))) :
    (classifyingAlgebraicStack (grp := grp) hR).toStack = classifyingStack (affineGroup R grp) :=
  rfl

/-- **`BG` as a Deligne–Mumford stack**, for `G = affineGroup R grp` with `R` finite étale over
`ℤ` and `Spec R → Spec ℤ` surjective: the algebraic stack `classifyingAlgebraicStack` with the
étale surjective atlas `classifyingAtlasChart G`. -/
noncomputable def classifyingDeligneMumfordStack [Algebra.Etale ℤ R] [Module.Finite ℤ R]
    (hR : _root_.AlgebraicGeometry.Surjective
      (@Spec.map (CommRingCat.of TorsorZu.{u}) (CommRingCat.of R)
        (CommRingCat.ofHom (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R))))) :
    DeligneMumfordStack.{u} where
  toAlgebraicStack := classifyingAlgebraicStack hR
  etaleAtlas := ⟨classifyingAtlasChart (affineGroup R grp),
    classifyingAtlasChart_affineGroup_isEtaleSurjective_of_int hR⟩

/-- The underlying stack of `classifyingDeligneMumfordStack` is `BG`. -/
@[simp]
theorem classifyingDeligneMumfordStack_toStack [Algebra.Etale ℤ R] [Module.Finite ℤ R]
    (hR : _root_.AlgebraicGeometry.Surjective
      (@Spec.map (CommRingCat.of TorsorZu.{u}) (CommRingCat.of R)
        (CommRingCat.ofHom (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R))))) :
    (classifyingDeligneMumfordStack (grp := grp) hR).toStack =
      classifyingStack (affineGroup R grp) :=
  rfl

end ActionTorsor

/-! ### `BΓ` for a finite group `Γ` -/

section Constant

variable (Γ : Type u) [Group Γ] [Finite Γ] [DecidableEq Γ]

/-- **The diagonal of `BΓ` is representable** for a finite group `Γ`. -/
theorem hasRepresentableDiagonal_classifyingStack_constant :
    HasRepresentableDiagonal (ActionTorsor.classifyingStack (constantGroup Γ)) :=
  ActionTorsor.hasRepresentableDiagonal_classifyingStack (surjective_constant Γ)

/-- **`BΓ` as an algebraic stack**, for a finite group `Γ`. -/
noncomputable def constantClassifyingAlgebraicStack : AlgebraicStack.{u} :=
  ActionTorsor.classifyingAlgebraicStack (grp := constantGrpObj Γ) (surjective_constant Γ)

/-- The underlying stack of `constantClassifyingAlgebraicStack Γ` is `BΓ`. -/
@[simp]
theorem constantClassifyingAlgebraicStack_toStack :
    (constantClassifyingAlgebraicStack Γ).toStack =
      ActionTorsor.classifyingStack (constantGroup Γ) :=
  rfl

/-- **`BΓ` as a Deligne–Mumford stack**, for a finite group `Γ`: the classifying stack of the
constant group `constantGroup Γ`, with representable diagonal and the étale surjective atlas
`pt → BΓ`. -/
noncomputable def constantClassifyingDeligneMumfordStack : DeligneMumfordStack.{u} :=
  ActionTorsor.classifyingDeligneMumfordStack (grp := constantGrpObj Γ) (surjective_constant Γ)

/-- The underlying stack of `constantClassifyingDeligneMumfordStack Γ` is `BΓ`. -/
@[simp]
theorem constantClassifyingDeligneMumfordStack_toStack :
    (constantClassifyingDeligneMumfordStack Γ).toStack =
      ActionTorsor.classifyingStack (constantGroup Γ) :=
  rfl

end Constant

end GromovWitten.AlgebraicGeometry
