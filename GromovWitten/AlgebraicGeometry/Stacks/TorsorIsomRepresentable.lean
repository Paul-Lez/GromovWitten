/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Stacks.TorsorIsomSheaf
import GromovWitten.AlgebraicGeometry.Stacks.TorsorAffineRefinement

/-!
# Representability of the isomorphism sheaf of two torsors

Let `G = affineGroup R grp` be an affine group with `R` étale and finite over `ℤ`, and let
`x y : ActionTorsor G (pointAction G) T` be two objects of the classifying stack `BG` over a
scheme `T`, with represented underlying torsors (`RP`, `RQ`).  This file proves that the
isomorphism sheaf `isomSheaf x y RP RQ` of `Stacks/TorsorIsomSheaf.lean` is represented by a
scheme étale and finite over `T` (`ActionTorsor.exists_isomRepresentation`).

The proof follows the representability of torsors (`Stacks/TorsorRepresentable.lean`):

1. (For any group algebraic space `G`.)  If `x` has a global section `σ`, evaluating an
   isomorphism `f^* x ≅ f^* y` at the base change of `σ` identifies `Isom(x, y)` with the sheaf
   `y.P` of the torsor `y` over the base (`ActionTorsor.isomSheafIsoOfSection`).  This uses that
   a morphism out of a torsor with a section is determined by the image of the section
   (`ConeQuotient.hom_ext_of_section`) and that any section gives a trivialisation
   (`ActionTorsor.sectionEquivTrivialisation`); the condition on the maps to the one-point
   space is automatic.
2. Over an affine base `Spec A`, both torsors are trivialised by a common faithfully flat,
   finitely presented affine cover `Spec B` (`ActionTorsor.exists_commonAffineTrivialisation`);
   by base change (`isomBaseChangeIso`) and step 1, `Isom(x, y) ×_{Spec A} Spec B` is the base
   change of `y`, which is `Spec (B ⊗[ℤ] R)` (`TorsorAffineTrivialisation.descentInput`).  This
   is an `AffineDescentInput` (`ActionTorsor.isomDescentInput`) whose coordinate ring is étale
   and finite over `B`, so effective descent of affine schemes represents `Isom(x, y)` by a
   scheme étale and finite over `Spec A` (`ActionTorsor.exists_isomRepresentation_affine`).
3. Over an arbitrary `T`, the representing schemes over the affine opens glue
   (`LocallyRepresentable`), exactly as in `TorsorRepresentation.exists_of_affine`.

Surjectivity of the representing scheme over `T` is not claimed: `Isom(x, y)` may be empty.
No hypothesis on the representations `RP`, `RQ` and no surjectivity hypothesis on
`Spec R → Spec ℤ` is needed.

## Main results

* `ActionTorsor.isoOfSection σ hσ f τ hτ : pullbackObj f x ≅ pullbackObj f y`: the isomorphism
  attached to a section `τ` of `y` over `f`, when `x` has a section `σ`;
  `ActionTorsor.iso_ext_of_section`: such an isomorphism is determined by its value on `σ`.
* `ActionTorsor.evalPoint σ hσ p`: the section of `y` obtained by evaluating the isomorphism of
  a point `p` of `Isom(x, y)` at the base change of the section `σ` of `x`;
  `ActionTorsor.evalPoint_injective`, `ActionTorsor.exists_evalPoint_eq`: this is a bijection
  onto the sections of `y`; `ActionTorsor.evalPoint_restrict`: it is natural in the test scheme.
* `ActionTorsor.evalSheafHom σ hσ : isomSheaf x y RP RQ ⟶ y.P` and
  `ActionTorsor.isomSheafIsoOfSection σ hσ : isomSheaf x y RP RQ ≅ y.P`, lying over the base
  (`ActionTorsor.evalSheafHom_comp_projection`).
* `ActionTorsor.exists_commonAffineTrivialisation`: two torsors over `Spec A` are trivialised
  over a common faithfully flat, finitely presented affine cover.
* `ActionTorsor.isomDescentInput D sP hsP : AffineDescentInput A D.B (isomSheaf x y RP RQ)
  (isomProjection x y RP RQ)` with coordinate ring `D.descentInput.M = D.B ⊗[TorsorZu] R`, and
  `ActionTorsor.etale_isomDescentInput_of_int`, `ActionTorsor.finite_isomDescentInput_of_int`.
* `ActionTorsor.exists_isomRepresentation_affine`, `ActionTorsor.exists_isomRepresentation`:
  `Isom(x, y)` is represented by a scheme étale and finite over the base.
-/

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

namespace ActionTorsor

/-! ### The isomorphism sheaf of a torsor with a section -/

section OfSection

variable {G : AlgebraicSpaceGroup.{u}} {S : Scheme.{u}}
  {x y : ActionTorsor G (AlgebraicSpaceAction.pointAction G) S}
  {RP : TorsorRepresentation x.toFppfTorsor} {RQ : TorsorRepresentation y.toFppfTorsor}
  (σ : fppfYoneda.obj S ⟶ x.P) (hσ : σ ≫ x.projection = 𝟙 _)

/-- The sheaf of the one-point action is terminal, typed at `(pointAction G).space.toSheaf`. -/
private noncomputable def pointActionIsTerminal (G : AlgebraicSpaceGroup.{u}) :
    IsTerminal (AlgebraicSpaceAction.pointAction G).space.toSheaf :=
  AlgebraicSpaceAction.pointIsTerminal

/-- A trivialisation obtained from a section carries the unit section to that section
(`ActionTorsor.sectionEquivTrivialisation` is inverted by evaluation at the unit section). -/
private theorem trivialSection_comp_sectionEquivTrivialisation_hom
    {U : AlgebraicSpaceAction G} {T : Scheme.{u}} (P : ActionTorsor G U T)
    (t : fppfYoneda.obj T ⟶ U.space.toSheaf)
    (τ : {τ : fppfYoneda.obj T ⟶ P.P // τ ≫ P.projection = 𝟙 _ ∧ τ ≫ P.target = t}) :
    ConeQuotient.trivialSection t ≫ (sectionEquivTrivialisation P t τ).hom.iso.hom = τ.1 :=
  congrArg Subtype.val ((sectionEquivTrivialisation P t).left_inv τ)

/-- If `a ≫ e.hom = b` for an isomorphism `e` of equivariant torsors, then `b ≫ e.inv = a`. -/
private theorem comp_inv_iso_hom_of_comp_hom {U : AlgebraicSpaceAction G} {T : Scheme.{u}}
    {P Q : ActionTorsor G U T} (e : P ≅ Q) (a : fppfYoneda.obj T ⟶ P.P)
    (b : fppfYoneda.obj T ⟶ Q.P) (h : a ≫ e.hom.iso.hom = b) : b ≫ e.inv.iso.hom = a := by
  rw [← h, Category.assoc, inv_iso_hom, Iso.hom_inv_id, Category.comp_id]

include hσ in
/-- The section of `y` over `f` obtained by evaluating an isomorphism `f^* x ≅ f^* y` at the
base change of the section `σ` of `x` lies over `f`. -/
theorem evalIso_projection {S' : Scheme.{u}} (f : S' ⟶ S)
    (e : pullbackObj f x ≅ pullbackObj f y) :
    (ConeQuotient.pullbackSection x σ hσ f ≫ e.hom.iso.hom ≫
        pullback.fst y.projection (fppfYoneda.map f)) ≫ y.projection = fppfYoneda.map f := by
  have hover : e.hom.iso.hom ≫ pullback.snd y.projection (fppfYoneda.map f) =
      pullback.snd x.projection (fppfYoneda.map f) := e.hom.over
  simp only [Category.assoc]
  rw [pullback.condition, ← Category.assoc _ (pullback.snd _ _), hover]
  change ConeQuotient.pullbackSection x σ hσ f ≫ (pullbackObj f x).projection ≫ _ = _
  rw [← Category.assoc, ConeQuotient.pullbackSection_projection, Category.id_comp]

/-- The point of the one-point space determined by the base change of `σ` (there is only one,
but the trivialisations below are typed with it). -/
private noncomputable def sectionTarget {S' : Scheme.{u}} (f : S' ⟶ S) :
    fppfYoneda.obj S' ⟶ (AlgebraicSpaceAction.pointAction G).space.toSheaf :=
  ConeQuotient.pullbackSection x σ hσ f ≫ (pullbackObj f x).target

/-- The trivialisation of `f^* x` by the base change of `σ`. -/
private noncomputable def trivialisationX {S' : Scheme.{u}} (f : S' ⟶ S) :
    ConeQuotient.trivialWithPoint (sectionTarget σ hσ f) ≅ pullbackObj f x :=
  sectionEquivTrivialisation (pullbackObj f x) (sectionTarget σ hσ f)
    ⟨ConeQuotient.pullbackSection x σ hσ f, ConeQuotient.pullbackSection_projection x σ hσ f,
      rfl⟩

/-- `trivialisationX` carries the unit section to the base change of `σ`. -/
private theorem trivialSection_comp_trivialisationX_hom {S' : Scheme.{u}} (f : S' ⟶ S) :
    ConeQuotient.trivialSection (sectionTarget σ hσ f) ≫ (trivialisationX σ hσ f).hom.iso.hom =
      ConeQuotient.pullbackSection x σ hσ f :=
  trivialSection_comp_sectionEquivTrivialisation_hom _ _ _

/-- The section of `f^* y` attached to a section `τ` of `y` over `f`. -/
private noncomputable def liftSection {S' : Scheme.{u}} (f : S' ⟶ S)
    (τ : fppfYoneda.obj S' ⟶ y.P) (hτ : τ ≫ y.projection = fppfYoneda.map f) :
    fppfYoneda.obj S' ⟶ (pullbackObj f y).P :=
  pullback.lift τ (𝟙 _) (by rw [hτ, Category.id_comp])

/-- The trivialisation of `f^* y` by a section `τ` of `y` over `f`. -/
private noncomputable def trivialisationY {S' : Scheme.{u}} (f : S' ⟶ S)
    (τ : fppfYoneda.obj S' ⟶ y.P) (hτ : τ ≫ y.projection = fppfYoneda.map f) :
    ConeQuotient.trivialWithPoint (sectionTarget σ hσ f) ≅ pullbackObj f y :=
  sectionEquivTrivialisation (pullbackObj f y) (sectionTarget σ hσ f)
    ⟨liftSection f τ hτ, pullback.lift_snd _ _ _, (pointActionIsTerminal G).hom_ext _ _⟩

/-- `trivialisationY` carries the unit section to the section of `f^* y` attached to `τ`. -/
private theorem trivialSection_comp_trivialisationY_hom {S' : Scheme.{u}} (f : S' ⟶ S)
    (τ : fppfYoneda.obj S' ⟶ y.P) (hτ : τ ≫ y.projection = fppfYoneda.map f) :
    ConeQuotient.trivialSection (sectionTarget σ hσ f) ≫
      (trivialisationY σ hσ f τ hτ).hom.iso.hom = liftSection f τ hτ :=
  trivialSection_comp_sectionEquivTrivialisation_hom _ _ _

/-- **The isomorphism `f^* x ≅ f^* y` attached to a section `τ` of `y` over `f`**, when `x` has
a section `σ`: the composite of the trivialisations of `f^* x` by `σ` and of `f^* y` by `τ`. -/
noncomputable def isoOfSection {S' : Scheme.{u}} (f : S' ⟶ S) (τ : fppfYoneda.obj S' ⟶ y.P)
    (hτ : τ ≫ y.projection = fppfYoneda.map f) : pullbackObj f x ≅ pullbackObj f y :=
  (trivialisationX σ hσ f).symm ≪≫ trivialisationY σ hσ f τ hτ

/-- The isomorphism attached to `τ` carries the base change of `σ` to the section of `f^* y`
determined by `τ`. -/
theorem pullbackSection_comp_isoOfSection_hom {S' : Scheme.{u}} (f : S' ⟶ S)
    (τ : fppfYoneda.obj S' ⟶ y.P) (hτ : τ ≫ y.projection = fppfYoneda.map f) :
    ConeQuotient.pullbackSection x σ hσ f ≫ (isoOfSection σ hσ f τ hτ).hom.iso.hom =
      pullback.lift τ (𝟙 _) (by rw [hτ, Category.id_comp]) := by
  rw [isoOfSection, Iso.trans_hom, comp_iso_hom, ← Category.assoc, Iso.symm_hom,
    comp_inv_iso_hom_of_comp_hom _ _ _ (trivialSection_comp_trivialisationX_hom σ hσ f),
    trivialSection_comp_trivialisationY_hom]
  rfl

/-- Evaluating the isomorphism attached to `τ` at the base change of `σ` gives back `τ`. -/
theorem pullbackSection_comp_isoOfSection_hom_fst {S' : Scheme.{u}} (f : S' ⟶ S)
    (τ : fppfYoneda.obj S' ⟶ y.P) (hτ : τ ≫ y.projection = fppfYoneda.map f) :
    ConeQuotient.pullbackSection x σ hσ f ≫ (isoOfSection σ hσ f τ hτ).hom.iso.hom ≫
      pullback.fst y.projection (fppfYoneda.map f) = τ := by
  rw [← Category.assoc, pullbackSection_comp_isoOfSection_hom, pullback.lift_fst]

include hσ in
/-- **An isomorphism `f^* x ≅ f^* y` is determined by its value on the base change of a
section `σ` of `x`.** -/
theorem iso_ext_of_section {S' : Scheme.{u}} (f : S' ⟶ S)
    {e e' : pullbackObj f x ≅ pullbackObj f y}
    (h : ConeQuotient.pullbackSection x σ hσ f ≫ e.hom.iso.hom ≫
        pullback.fst y.projection (fppfYoneda.map f) =
      ConeQuotient.pullbackSection x σ hσ f ≫ e'.hom.iso.hom ≫
        pullback.fst y.projection (fppfYoneda.map f)) : e = e' := by
  refine Iso.ext (ConeQuotient.hom_ext_of_section (ConeQuotient.pullbackSection x σ hσ f)
    (ConeQuotient.pullbackSection_projection x σ hσ f) _ _ ?_)
  apply pullback.hom_ext
  · simpa only [Category.assoc] using h
  · have h₁ : e.hom.iso.hom ≫ pullback.snd y.projection (fppfYoneda.map f) =
        pullback.snd x.projection (fppfYoneda.map f) := e.hom.over
    have h₂ : e'.hom.iso.hom ≫ pullback.snd y.projection (fppfYoneda.map f) =
        pullback.snd x.projection (fppfYoneda.map f) := e'.hom.over
    rw [Category.assoc, Category.assoc, h₁, h₂]

/-- The isomorphism attached to the evaluation of an isomorphism `e` is `e`. -/
theorem isoOfSection_eval {S' : Scheme.{u}} (f : S' ⟶ S)
    (e : pullbackObj f x ≅ pullbackObj f y) :
    isoOfSection σ hσ f _ (evalIso_projection σ hσ f e) = e :=
  iso_ext_of_section σ hσ f (pullbackSection_comp_isoOfSection_hom_fst σ hσ f _ _)

/-- The section of `y` obtained by evaluating the isomorphism of a point of `Isom(x, y)` at the
base change of the section `σ` of `x`. -/
noncomputable def evalPoint {S' : Scheme.{u}} (p : IsomPoint x y RP RQ S') :
    fppfYoneda.obj S' ⟶ y.P :=
  ConeQuotient.pullbackSection x σ hσ p.f ≫ p.iso.hom.iso.hom ≫
    pullback.fst y.projection (fppfYoneda.map p.f)

/-- The evaluated section lies over the test map of the point. -/
@[reassoc]
theorem evalPoint_projection {S' : Scheme.{u}} (p : IsomPoint x y RP RQ S') :
    evalPoint σ hσ p ≫ y.projection = fppfYoneda.map p.f :=
  evalIso_projection σ hσ p.f p.iso

/-- The evaluation of the point attached to the isomorphism attached to `τ` is `τ`. -/
theorem evalPoint_ofIso_isoOfSection {S' : Scheme.{u}} (f : S' ⟶ S)
    (τ : fppfYoneda.obj S' ⟶ y.P) (hτ : τ ≫ y.projection = fppfYoneda.map f) :
    evalPoint σ hσ (IsomPoint.ofIso (RP := RP) (RQ := RQ) f (isoOfSection σ hσ f τ hτ)) = τ := by
  unfold evalPoint
  change ConeQuotient.pullbackSection x σ hσ f ≫
    (IsomPoint.ofIso (RP := RP) (RQ := RQ) f (isoOfSection σ hσ f τ hτ)).iso.hom.iso.hom ≫
      pullback.fst y.projection (fppfYoneda.map f) = τ
  rw [IsomPoint.ofIso_iso]
  exact pullbackSection_comp_isoOfSection_hom_fst σ hσ f τ hτ

/-- **Evaluation at the section is injective on points.** -/
theorem evalPoint_injective {S' : Scheme.{u}} {p q : IsomPoint x y RP RQ S'}
    (h : evalPoint σ hσ p = evalPoint σ hσ q) : p = q := by
  have hf : p.f = q.f := by
    apply fppfYoneda.map_injective
    rw [← evalPoint_projection σ hσ p, ← evalPoint_projection σ hσ q, h]
  have hp := IsomPoint.map_hom_eq p
  have hq := IsomPoint.map_hom_eq q
  unfold evalPoint at h
  obtain ⟨f, hom, ep⟩ := p
  obtain ⟨f', hom', eq⟩ := q
  dsimp only at hf h hp hq
  subst hf
  have hiso : (IsomPoint.mk (x := x) (y := y) (RP := RP) (RQ := RQ) f hom ep).iso =
      (IsomPoint.mk f hom' eq).iso :=
    iso_ext_of_section σ hσ f h
  refine IsomPoint.ext_heq rfl (heq_of_eq ?_)
  apply fppfYoneda.map_injective
  rw [hp, hq, hiso]

/-- **Evaluation at the section is surjective onto the sections of `y`.** -/
theorem exists_evalPoint_eq {S' : Scheme.{u}} (τ : fppfYoneda.obj S' ⟶ y.P) :
    ∃ p : IsomPoint x y RP RQ S', evalPoint σ hσ p = τ := by
  obtain ⟨f, hf⟩ : ∃ f : S' ⟶ S, τ ≫ y.projection = fppfYoneda.map f :=
    ⟨fppfYoneda.preimage (τ ≫ y.projection), (fppfYoneda.map_preimage _).symm⟩
  exact ⟨IsomPoint.ofIso f (isoOfSection σ hσ f τ hf), evalPoint_ofIso_isoOfSection σ hσ f τ hf⟩

/-- The base change of the section `σ` along `g ≫ f` is, through the composition comparison,
the base change along `g` of its base change along `f`. -/
@[reassoc]
private theorem pullbackSection_comp_pullbackCompIso_hom_fst {S' S'' : Scheme.{u}}
    (f : S' ⟶ S) (g : S'' ⟶ S') :
    ConeQuotient.pullbackSection x σ hσ (g ≫ f) ≫
        (FppfTorsor.pullbackCompIso x.toFppfTorsor g f).hom ≫
        pullback.fst (pullback.snd x.projection (fppfYoneda.map f)) (fppfYoneda.map g) =
      fppfYoneda.map g ≫ ConeQuotient.pullbackSection x σ hσ f := by
  apply pullback.hom_ext
  · simp only [Category.assoc, FppfTorsor.pullbackCompIso_hom_fst_fst,
      ConeQuotient.pullbackSection_fst, fppfYoneda.map_comp]
  · simp only [Category.assoc, FppfTorsor.pullbackCompIso_hom_fst_snd,
      ConeQuotient.pullbackSection_snd_assoc, ConeQuotient.pullbackSection_snd, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of evaluation**: the evaluated section of a restricted point is the base
change of the evaluated section. -/
theorem evalPoint_restrict {S' S'' : Scheme.{u}} (g : S'' ⟶ S') (p : IsomPoint x y RP RQ S') :
    evalPoint σ hσ (p.restrict g) = fppfYoneda.map g ≫ evalPoint σ hσ p := by
  have hmap := FppfTorsor.pullbackMap_fst_assoc (P := x.toFppfTorsor.pullbackTorsor p.f)
    (Q := y.toFppfTorsor.pullbackTorsor p.f) g p.iso.hom.iso.hom p.iso.hom.over
    (pullback.fst y.projection (fppfYoneda.map p.f))
  change ConeQuotient.pullbackSection x σ hσ (g ≫ p.f) ≫ (p.restrict g).iso.hom.iso.hom ≫
    pullback.fst y.projection (fppfYoneda.map (g ≫ p.f)) = _
  rw [IsomPoint.restrict_iso, ofStackIso_hom_iso_hom, stackPullbackIso_toStackIso_hom_iso_hom]
  unfold evalPoint
  simp only [Category.assoc]
  rw [FppfTorsor.pullbackCompIso_inv_fst, hmap,
    pullbackSection_comp_pullbackCompIso_hom_fst_assoc]

variable (x y RP RQ)

/-- **Evaluation at a section, as a morphism of sheaves** `Isom(x, y) ⟶ y.P`. -/
noncomputable def evalSheafHom : isomSheaf x y RP RQ ⟶ y.P :=
  ObjectProperty.homMk
    { app := fun S' => ↾fun p : IsomPoint x y RP RQ S'.unop => fppfJ.yonedaEquiv (evalPoint σ hσ p)
      naturality := fun S' S'' g => by
        ext p
        exact (congrArg fppfJ.yonedaEquiv (evalPoint_restrict σ hσ g.unop p)).trans
          (GrothendieckTopology.yonedaEquiv_naturality' fppfJ (evalPoint σ hσ p) g).symm }

/-- `evalSheafHom` acts on points by `evalPoint`. -/
@[simp]
theorem evalSheafHom_app {S' : Scheme.{u}} (p : IsomPoint x y RP RQ S') :
    (evalSheafHom x y RP RQ σ hσ).hom.app (Opposite.op S') p =
      fppfJ.yonedaEquiv (evalPoint σ hσ p) :=
  rfl

/-- A morphism from a representable sheaf composed with `evalSheafHom` is the evaluation of
the corresponding point. -/
theorem comp_evalSheafHom {S' : Scheme.{u}} (α : fppfYoneda.obj S' ⟶ isomSheaf x y RP RQ) :
    α ≫ evalSheafHom x y RP RQ σ hσ = evalPoint σ hσ (fppfJ.yonedaEquiv α) := by
  apply fppfJ.yonedaEquiv.injective
  rw [GrothendieckTopology.yonedaEquiv_comp]
  rfl

/-- `evalSheafHom` lies over the base. -/
@[reassoc (attr := simp)]
theorem evalSheafHom_comp_projection :
    evalSheafHom x y RP RQ σ hσ ≫ y.projection = isomProjection x y RP RQ := by
  apply ObjectProperty.hom_ext
  ext ⟨S'⟩ (p : IsomPoint x y RP RQ S')
  change y.projection.hom.app (Opposite.op S') (fppfJ.yonedaEquiv (evalPoint σ hσ p)) = p.f
  rw [← GrothendieckTopology.yonedaEquiv_comp, evalPoint_projection,
    GrothendieckTopology.yonedaEquiv_yoneda_map]

/-- **Evaluation at a section is an isomorphism** `Isom(x, y) ≅ y.P`. -/
instance isIso_evalSheafHom : IsIso (evalSheafHom x y RP RQ σ hσ) := by
  refine fppfSheaf_isIso_of_bijective _ (fun S' => ⟨?_, ?_⟩)
  · intro α β h
    simp only [comp_evalSheafHom] at h
    exact fppfJ.yonedaEquiv.injective (evalPoint_injective σ hσ h)
  · intro γ
    obtain ⟨p, hp⟩ := exists_evalPoint_eq (RP := RP) (RQ := RQ) σ hσ γ
    obtain ⟨α, hα⟩ := (fppfJ.yonedaEquiv (F := isomSheaf x y RP RQ)).surjective p
    refine ⟨α, ?_⟩
    change α ≫ evalSheafHom x y RP RQ σ hσ = γ
    rw [comp_evalSheafHom, hα, hp]

/-- **The isomorphism sheaf of a torsor with a section** `σ` and a torsor `y` is the sheaf of
`y`, over the base (`evalSheafHom_comp_projection`). -/
noncomputable def isomSheafIsoOfSection : isomSheaf x y RP RQ ≅ y.P :=
  asIso (evalSheafHom x y RP RQ σ hσ)

/-- The isomorphism `isomSheafIsoOfSection` is `evalSheafHom`. -/
@[simp]
theorem isomSheafIsoOfSection_hom :
    (isomSheafIsoOfSection x y RP RQ σ hσ).hom = evalSheafHom x y RP RQ σ hσ :=
  rfl

end OfSection

/-! ### Common affine trivialisation of two torsors -/

section CommonTrivialisation

variable {G : AlgebraicSpaceGroup.{u}} {A : Type u} [CommRing A]

/-- **Two torsors over an affine base are trivialised over a common faithfully flat, finitely
presented affine cover**: trivialise the first over `Spec B₁`, then the base change of the second
over `Spec B₂ ⟶ Spec B₁`, and use transitivity of faithful flatness and finite presentation. -/
theorem exists_commonAffineTrivialisation (P Q : FppfTorsor G (Spec (CommRingCat.of A))) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      Module.FaithfullyFlat A B ∧ Algebra.FinitePresentation A B ∧
      (∃ sP : fppfYoneda.obj (Spec (CommRingCat.of B)) ⟶ P.P,
        sP ≫ P.projection = fppfYoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A B)))) ∧
      ∃ sQ : fppfYoneda.obj (Spec (CommRingCat.of B)) ⟶ Q.P,
        sQ ≫ Q.projection = fppfYoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  obtain ⟨B₁, _, _, hff₁, hfp₁, s₁, hs₁⟩ := P.exists_affineFaithfullyFlat_section
  obtain ⟨B₂, _, _, hff₂, hfp₂, s₂, hs₂⟩ :=
    (Q.pullbackTorsor
      (Spec.map (CommRingCat.ofHom (algebraMap A B₁)))).exists_affineFaithfullyFlat_section
  let _ : Algebra A B₂ := ((algebraMap B₁ B₂).comp (algebraMap A B₁)).toAlgebra
  have _ : IsScalarTower A B₁ B₂ := IsScalarTower.of_algebraMap_eq' rfl
  have hcomp : Spec.map (CommRingCat.ofHom (algebraMap B₁ B₂)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A B₁)) =
      Spec.map (CommRingCat.ofHom (algebraMap A B₂)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine ⟨B₂, inferInstance, inferInstance, Module.FaithfullyFlat.trans A B₁ B₂,
    Algebra.FinitePresentation.trans A B₁ B₂,
    ⟨fppfYoneda.map (Spec.map (CommRingCat.ofHom (algebraMap B₁ B₂))) ≫ s₁, ?_⟩,
    ⟨s₂ ≫ pullback.fst _ _, ?_⟩⟩
  · rw [Category.assoc, hs₁, ← Functor.map_comp, hcomp]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hs₂, ← Functor.map_comp, hcomp]

end CommonTrivialisation

/-! ### The affine descent input for `Isom(x, y)` -/

section Affine

variable {R : Type u} [CommRing R] {grp : GrpObj (fppfYoneda.obj (Spec (CommRingCat.of R)))}
  {A : Type u} [CommRing A]
  {x y : ActionTorsor (affineGroup R grp) (AlgebraicSpaceAction.pointAction (affineGroup R grp))
    (Spec (CommRingCat.of A))}
  (RP : TorsorRepresentation x.toFppfTorsor) (RQ : TorsorRepresentation y.toFppfTorsor)
  (D : TorsorAffineTrivialisation y.toFppfTorsor)
  (sP : fppfYoneda.obj (Spec (CommRingCat.of D.B)) ⟶ x.P)
  (hsP : sP ≫ x.projection = fppfYoneda.map D.cover)

/-- **The affine descent input for `Isom(x, y)`** (blueprint D2b): given an affine
trivialisation `D` of `y` over `Spec D.B ⟶ Spec A` and a section `sP` of `x` over the same
cover, the base change of `Isom(x, y)` to `Spec D.B` is `Isom(D.cover^* x, D.cover^* y)`
(`isomBaseChangeIso`), which is the base change of `y` because `D.cover^* x` has the section
`sP` (`isomSheafIsoOfSection`), which is `Spec (D.B ⊗[TorsorZu] R)` (`D.descentInput`).  The
coordinate ring is that of `D.descentInput`, namely `D.B ⊗[TorsorZu] R`. -/
noncomputable def isomDescentInput :
    AffineDescentInput A D.B (isomSheaf x y RP RQ) (isomProjection x y RP RQ) where
  M := D.descentInput.M
  commRing := D.descentInput.commRing
  algebra := D.descentInput.algebra
  algebraBase := D.descentInput.algebraBase
  isScalarTower := D.descentInput.isScalarTower
  θ := (isomBaseChangeIso x y RP RQ D.cover).symm ≪≫
    isomSheafIsoOfSection (pullbackObj D.cover x) (pullbackObj D.cover y)
      (RP.pullbackRep D.cover) (RQ.pullbackRep D.cover)
      (pullback.lift sP (𝟙 _) (by rw [hsP, Category.id_comp])) (pullback.lift_snd _ _ _) ≪≫
    D.descentInput.θ
  θ_over := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [D.descentInput.θ_over]
    change _ ≫ _ ≫ (pullbackObj D.cover y).projection = _
    rw [isomSheafIsoOfSection_hom, evalSheafHom_comp_projection, Iso.inv_comp_eq,
      isomBaseChangeIso_hom_snd]

/-- The coordinate ring of `isomDescentInput` is that of `D.descentInput`. -/
theorem isomDescentInput_M : (isomDescentInput RP RQ D sP hsP).M = D.descentInput.M :=
  rfl

/-- If `R` is étale over `ℤ`, the coordinate ring of `isomDescentInput` is étale over the
cover `D.B`. -/
theorem etale_isomDescentInput_of_int [Algebra.Etale ℤ R] :
    Algebra.Etale D.B (isomDescentInput RP RQ D sP hsP).M :=
  D.etale_descentInput_of_int

/-- If `R` is a finite `ℤ`-module, the coordinate ring of `isomDescentInput` is a finite
`D.B`-module. -/
theorem finite_isomDescentInput_of_int [Module.Finite ℤ R] :
    Module.Finite D.B (isomDescentInput RP RQ D sP hsP).M :=
  D.finite_descentInput_of_int

/-- **Representability of `Isom(x, y)` over an affine base.**  For `G = affineGroup R grp` with
`R` étale and finite over `ℤ`, the isomorphism sheaf of two objects of `BG` over `Spec A` with
represented underlying torsors is represented by a scheme étale and finite over `Spec A`. -/
theorem exists_isomRepresentation_affine [Algebra.Etale ℤ R] [Module.Finite ℤ R]
    (x y : ActionTorsor (affineGroup R grp)
      (AlgebraicSpaceAction.pointAction (affineGroup R grp)) (Spec (CommRingCat.of A)))
    (RP : TorsorRepresentation x.toFppfTorsor) (RQ : TorsorRepresentation y.toFppfTorsor) :
    ∃ (W : Scheme.{u}) (w : W ⟶ Spec (CommRingCat.of A))
      (e : fppfYoneda.obj W ≅ isomSheaf x y RP RQ),
      e.hom ≫ isomProjection x y RP RQ = fppfYoneda.map w ∧
        _root_.AlgebraicGeometry.Etale w ∧ IsFinite w := by
  obtain ⟨B, _, _, hff, hfp, ⟨sP, hsP⟩, ⟨sQ, hsQ⟩⟩ :=
    exists_commonAffineTrivialisation x.toFppfTorsor y.toFppfTorsor
  let D : TorsorAffineTrivialisation y.toFppfTorsor := { B := B, s := sQ, s_over := hsQ }
  let E := isomDescentInput RP RQ D sP hsP
  have := etale_isomDescentInput_of_int RP RQ D sP hsP
  have := finite_isomDescentInput_of_int RP RQ D sP hsP
  have hiso := E.isIso_toSpec
  refine ⟨Spec (CommRingCat.of E.descended),
    Spec.map (CommRingCat.ofHom (algebraMap A E.descended)), (asIso E.toSpec).symm, ?_, ?_, ?_⟩
  · rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq, E.toSpec_comp]
  · have := E.etale_descended
    rw [HasRingHomProperty.Spec_iff (P := @_root_.AlgebraicGeometry.Etale)]
    exact RingHom.etale_algebraMap.2 this
  · have := E.finite_descended
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 this

end Affine

/-! ### Zariski gluing: representability over an arbitrary base -/

section Global

variable {R : Type u} [CommRing R] {grp : GrpObj (fppfYoneda.obj (Spec (CommRingCat.of R)))}

/-- **Representability of the isomorphism sheaf of two objects of `BG`** (blueprint D2b).  For
`G = affineGroup R grp` with `R` étale and finite over `ℤ`, and two objects `x y` of the
classifying stack `BG` over a scheme `T` with represented underlying torsors (`RP`, `RQ`), the
isomorphism sheaf `isomSheaf x y RP RQ` is represented by a scheme `W` étale and finite over
`T`, compatibly with the structure maps.  (Surjectivity of `W ⟶ T` is not claimed: `Isom(x, y)`
may be empty.)  Over affine opens this is `exists_isomRepresentation_affine`; the representing
schemes are glued by `LocallyRepresentable`. -/
theorem exists_isomRepresentation [Algebra.Etale ℤ R] [Module.Finite ℤ R] {T : Scheme.{u}}
    (x y : ActionTorsor (affineGroup R grp)
      (AlgebraicSpaceAction.pointAction (affineGroup R grp)) T)
    (RP : TorsorRepresentation x.toFppfTorsor) (RQ : TorsorRepresentation y.toFppfTorsor) :
    ∃ (W : Scheme.{u}) (w : W ⟶ T) (e : fppfYoneda.obj W ≅ isomSheaf x y RP RQ),
      e.hom ≫ isomProjection x y RP RQ = fppfYoneda.map w ∧
        _root_.AlgebraicGeometry.Etale w ∧ IsFinite w := by
  choose W w e he using fun i : T.affineOpens =>
    exists_isomRepresentation_affine (A := Γ(T, (i : T.Opens)))
      (pullbackObj (i.2.isoSpec.inv ≫ (i : T.Opens).ι) x)
      (pullbackObj (i.2.isoSpec.inv ≫ (i : T.Opens).ι) y)
      (RP.pullbackRep (i.2.isoSpec.inv ≫ (i : T.Opens).ι))
      (RQ.pullbackRep (i.2.isoSpec.inv ≫ (i : T.Opens).ι))
  let L : LocallyRepresentable (isomSheaf x y RP RQ) (isomProjection x y RP RQ) :=
    { ι := T.affineOpens
      U := fun i => i
      iSup_U := iSup_affineOpens_eq_top T
      X := W
      g := fun i => w i ≫ i.2.isoSpec.inv
      θ := fun i => TorsorRepresentation.affineOpenPullbackIso (isomProjection x y RP RQ) i.2 ≪≫
        (isomBaseChangeIso x y RP RQ (i.2.isoSpec.inv ≫ (i : T.Opens).ι)).symm ≪≫ (e i).symm
      θ_over := fun i => by
        have h1 : (e i).inv ≫ fppfYoneda.map (w i) =
            isomProjection (pullbackObj (i.2.isoSpec.inv ≫ (i : T.Opens).ι) x)
              (pullbackObj (i.2.isoSpec.inv ≫ (i : T.Opens).ι) y)
              (RP.pullbackRep (i.2.isoSpec.inv ≫ (i : T.Opens).ι))
              (RQ.pullbackRep (i.2.isoSpec.inv ≫ (i : T.Opens).ι)) := by
          rw [← (he i).1, Iso.inv_hom_id_assoc]
        have h2 : (isomBaseChangeIso x y RP RQ (i.2.isoSpec.inv ≫ (i : T.Opens).ι)).inv ≫
            isomProjection (pullbackObj (i.2.isoSpec.inv ≫ (i : T.Opens).ι) x)
              (pullbackObj (i.2.isoSpec.inv ≫ (i : T.Opens).ι) y)
              (RP.pullbackRep (i.2.isoSpec.inv ≫ (i : T.Opens).ι))
              (RQ.pullbackRep (i.2.isoSpec.inv ≫ (i : T.Opens).ι)) = pullback.snd _ _ := by
          rw [Iso.inv_comp_eq, isomBaseChangeIso_hom_snd]
        simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Functor.map_comp]
        rw [← Category.assoc (e i).inv, h1, ← Category.assoc _ (isomProjection _ _ _ _), h2]
        erw [TorsorRepresentation.affineOpenPullbackIso_hom_snd_assoc]
        rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
          Category.id_comp] }
  refine ⟨L.scheme, L.toBase, L.iso, L.iso_hom_comp, ?_, ?_⟩
  · refine L.etale_toBase fun i => ?_
    have := (he i).2.1
    change _root_.AlgebraicGeometry.Etale (w i ≫ i.2.isoSpec.inv)
    infer_instance
  · refine L.isFinite_toBase fun i => ?_
    have := (he i).2.2
    change IsFinite (w i ≫ i.2.isoSpec.inv)
    infer_instance

end Global

end ActionTorsor

end GromovWitten.AlgebraicGeometry
