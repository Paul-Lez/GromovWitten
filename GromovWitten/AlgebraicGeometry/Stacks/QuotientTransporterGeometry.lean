/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.QuotientTransporter
import GromovWitten.AlgebraicGeometry.Morphisms.Unramified
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Relative geometry of action transporters

For an action over `S`, its reverse graph sends `(g,u)` to `(g • u,u)` in `U ×[S] U`.
Its composite with the second projection is a base change of `G → S`. Cancellation then
proves unramifiedness, properness, or finiteness of the graph under the corresponding hypotheses.
The transporter is an actual pullback of that graph, so it inherits these properties.

Only the equation saying the action is over `S` is used here; group axioms are not required for
these morphism-geometry statements. Descent to a general quotient-stack diagonal is separate.
-/

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.QuotientTransporterGeometry

universe u

variable {S G U T : Scheme.{u}}
  (g : G ⟶ S) (p : U ⟶ S)
  (a : pullback g p ⟶ U)
  (ha : a ≫ p = pullback.snd g p ≫ p)

/-- The reverse action graph over the actual base scheme. -/
noncomputable def actionGraph : pullback g p ⟶ pullback p p :=
  pullback.lift a (pullback.snd g p) ha

@[reassoc (attr := simp)]
theorem actionGraph_fst : actionGraph g p a ha ≫ pullback.fst p p = a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem actionGraph_snd : actionGraph g p a ha ≫ pullback.snd p p = pullback.snd g p :=
  pullback.lift_snd _ _ _

/-- Cancellation proves the graph unramified whenever the group-space projection is unramified. -/
theorem actionGraph_unramified [Unramified g] : Unramified (actionGraph g p a ha) := by
  have : Unramified (actionGraph g p a ha ≫ pullback.snd p p) := by
    rw [actionGraph_snd]
    infer_instance
  exact Unramified.of_comp _ (pullback.snd p p)

/-- A proper group-space projection and a separated acted-on space give a proper graph. -/
theorem actionGraph_proper [IsProper g] [IsSeparated p] :
    IsProper (actionGraph g p a ha) := by
  have : IsProper (actionGraph g p a ha ≫ pullback.snd p p) := by
    rw [actionGraph_snd]
    infer_instance
  exact IsProper.of_comp _ (pullback.snd p p)

/-- A finite group-space projection and a separated acted-on space give a finite graph. -/
theorem actionGraph_finite [IsFinite g] [IsSeparated p] :
    IsFinite (actionGraph g p a ha) := by
  have : IsFinite (actionGraph g p a ha ≫ pullback.snd p p) := by
    rw [actionGraph_snd]
    infer_instance
  exact IsFinite.of_comp _ (pullback.snd p p)

variable (x y : T ⟶ U) (hxy : x ≫ p = y ≫ p)

/-- The transporter of elements carrying `y` to `x`, as an actual scheme pullback. -/
noncomputable def transporter : Scheme.{u} :=
  pullback (actionGraph g p a ha) (pullback.lift x y hxy)

noncomputable def projection : transporter g p a ha x y hxy ⟶ T :=
  pullback.snd _ _

/-- The map retaining the group and acted-on-space coordinates. -/
noncomputable def graphLift : transporter g p a ha x y hxy ⟶ pullback g p :=
  pullback.fst _ _

theorem isPullback :
    IsPullback (graphLift g p a ha x y hxy) (projection g p a ha x y hxy)
      (actionGraph g p a ha) (pullback.lift x y hxy) :=
  IsPullback.of_hasPullback _ _

@[reassoc (attr := simp)]
theorem graphLift_action :
    graphLift g p a ha x y hxy ≫ a = projection g p a ha x y hxy ≫ x := by
  have h := congrArg (fun f => f ≫ pullback.fst p p)
    (isPullback g p a ha x y hxy).w
  simpa only [Category.assoc, actionGraph_fst, pullback.lift_fst] using h

@[reassoc (attr := simp)]
theorem graphLift_snd :
    graphLift g p a ha x y hxy ≫ pullback.snd g p =
      projection g p a ha x y hxy ≫ y := by
  have h := congrArg (fun f => f ≫ pullback.snd p p)
    (isPullback g p a ha x y hxy).w
  simpa only [Category.assoc, actionGraph_snd, pullback.lift_snd] using h

/-- The same unramified criterion holds for every relative transporter. -/
theorem projection_unramified [Unramified g] :
    Unramified (projection g p a ha x y hxy) := by
  have := actionGraph_unramified g p a ha
  exact MorphismProperty.of_isPullback (P := @Unramified)
    (isPullback g p a ha x y hxy) inferInstance

/-- Properness is inherited by the transporter projection through its defining pullback. -/
theorem projection_proper [IsProper g] [IsSeparated p] :
    IsProper (projection g p a ha x y hxy) := by
  have := actionGraph_proper g p a ha
  exact MorphismProperty.of_isPullback (P := @IsProper)
    (isPullback g p a ha x y hxy) inferInstance

/-- Finiteness is inherited by the transporter projection through its defining pullback. -/
theorem projection_finite [IsFinite g] [IsSeparated p] :
    IsFinite (projection g p a ha x y hxy) := by
  have := actionGraph_finite g p a ha
  exact MorphismProperty.of_isPullback (P := @IsFinite)
    (isPullback g p a ha x y hxy) inferInstance

/-- In particular an étale group-space projection gives unramified transporters. -/
theorem projection_unramified_of_etale [Etale g] :
    Unramified (projection g p a ha x y hxy) := by
  have : Unramified g := {}
  exact projection_unramified g p a ha x y hxy

/-- The finite étale case gives both finite and unramified transporters. -/
theorem projection_finite_unramified [IsFinite g] [Etale g] [IsSeparated p] :
    IsFinite (projection g p a ha x y hxy) ∧
      Unramified (projection g p a ha x y hxy) :=
  ⟨projection_finite g p a ha x y hxy,
    projection_unramified_of_etale g p a ha x y hxy⟩

/-! ### Base change and diagonal stabilizers -/

/-- The equality over `S` after changing the test scheme. -/
theorem precomp_over {T' : Scheme.{u}} (b : T' ⟶ T) (x y : T ⟶ U)
    (hxy : x ≫ p = y ≫ p) :
    (b ≫ x) ≫ p = (b ≫ y) ≫ p := by
  rw [Category.assoc, Category.assoc, hxy]

/-- Base change of the relative transporter along a morphism of test schemes. -/
noncomputable def baseChangeMap {T' : Scheme.{u}} (b : T' ⟶ T)
    (x y : T ⟶ U) (hxy : x ≫ p = y ≫ p) :
    transporter g p a ha (b ≫ x) (b ≫ y) (precomp_over (p := p) b x y hxy) ⟶
      transporter g p a ha x y hxy :=
  pullback.lift
    (graphLift g p a ha (b ≫ x) (b ≫ y) (precomp_over (p := p) b x y hxy))
    (projection g p a ha (b ≫ x) (b ≫ y)
      (precomp_over (p := p) b x y hxy) ≫ b)
    (by
      apply pullback.hom_ext
      · simp only [Category.assoc, actionGraph_fst, graphLift_action,
          pullback.lift_fst]
      · simp only [Category.assoc, actionGraph_snd, graphLift_snd,
          pullback.lift_snd])

@[reassoc (attr := simp)]
theorem baseChangeMap_projection {T' : Scheme.{u}} (b : T' ⟶ T)
    (x y : T ⟶ U) (hxy : x ≫ p = y ≫ p) :
    baseChangeMap g p a ha b x y hxy ≫ projection g p a ha x y hxy =
      projection g p a ha (b ≫ x) (b ≫ y)
        (precomp_over (p := p) b x y hxy) ≫ b := by
  apply pullback.lift_snd

@[reassoc (attr := simp)]
theorem baseChangeMap_graphLift {T' : Scheme.{u}} (b : T' ⟶ T)
    (x y : T ⟶ U) (hxy : x ≫ p = y ≫ p) :
    baseChangeMap g p a ha b x y hxy ≫ graphLift g p a ha x y hxy =
      graphLift g p a ha (b ≫ x) (b ≫ y)
        (precomp_over (p := p) b x y hxy) := by
  apply pullback.lift_fst

theorem baseChangeMap_isPullback {T' : Scheme.{u}} (b : T' ⟶ T)
    (x y : T ⟶ U) (hxy : x ≫ p = y ≫ p) :
    IsPullback
      (baseChangeMap g p a ha b x y hxy)
      (projection g p a ha (b ≫ x) (b ≫ y)
        (precomp_over (p := p) b x y hxy))
      (projection g p a ha x y hxy) b := by
  apply IsPullback.of_right (h₁₂ := graphLift g p a ha x y hxy)
    (v₁₃ := actionGraph g p a ha)
    (h₂₂ := pullback.lift x y hxy) _
    (baseChangeMap_projection g p a ha b x y hxy)
    (isPullback g p a ha x y hxy)
  rw [baseChangeMap_graphLift]
  have hpair : b ≫ pullback.lift x y hxy =
      pullback.lift (b ≫ x) (b ≫ y) (precomp_over (p := p) b x y hxy) := by
    apply pullback.hom_ext
    · change b ≫ (pullback.lift x y hxy ≫ pullback.fst p p) =
        pullback.lift (b ≫ x) (b ≫ y) (precomp_over (p := p) b x y hxy) ≫
          pullback.fst p p
      rw [pullback.lift_fst, pullback.lift_fst]
    · change b ≫ (pullback.lift x y hxy ≫ pullback.snd p p) =
        pullback.lift (b ≫ x) (b ≫ y) (precomp_over (p := p) b x y hxy) ≫
          pullback.snd p p
      rw [pullback.lift_snd, pullback.lift_snd]
  rw [hpair]
  exact isPullback g p a ha (b ≫ x) (b ≫ y)
    (precomp_over (p := p) b x y hxy)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem baseChangeMap_id (x y : T ⟶ U) (hxy : x ≫ p = y ≫ p) :
    baseChangeMap g p a ha (𝟙 T) x y hxy = 𝟙 _ := by
  dsimp [baseChangeMap, graphLift, projection, transporter]
  apply pullback.hom_ext <;> simp <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem baseChangeMap_comp {T' T'' : Scheme.{u}} (b : T' ⟶ T) (c : T'' ⟶ T')
    (x y : T ⟶ U) (hxy : x ≫ p = y ≫ p) :
    baseChangeMap g p a ha (c ≫ b) x y hxy =
      baseChangeMap g p a ha c (b ≫ x) (b ≫ y)
        (precomp_over (p := p) b x y hxy) ≫
        baseChangeMap g p a ha b x y hxy := by
  dsimp [baseChangeMap, graphLift, projection, transporter]
  apply pullback.hom_ext <;> simp <;> rfl

/-! The diagonal transporter is the stabilizer groupoid fibre.  We retain the
categorical automorphism structure rather than imposing a group-law convention on
the chosen section labels. -/

namespace Stabilizer

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G} {T : Scheme.{u}}

/-- Sections of the diagonal transporter are exactly automorphisms of the trivial
`G`-torsor with point `x`. -/
noncomputable def sectionAutEquiv (x : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    QuotientTransporter.Section (G := G) (U := U) x x ≃
      CategoryTheory.Aut (ActionTorsor.trivialWithPoint x) where
  toFun s := asIso (QuotientTransporter.arrowOfSection (G := G) (U := U) x x s)
  invFun e := QuotientTransporter.sectionOfArrow (G := G) (U := U) x x e.hom
  left_inv s := QuotientTransporter.sectionOfArrow_arrowOfSection
    (G := G) (U := U) x x s
  right_inv e := by
    apply Iso.ext
    simp only [asIso_hom]
    exact QuotientTransporter.arrowOfSection_sectionOfArrow
      (G := G) (U := U) x x e.hom

@[simp]
theorem sectionAutEquiv_hom (x : fppfYoneda.obj T ⟶ U.space.toSheaf)
    (s : QuotientTransporter.Section (G := G) (U := U) x x) :
      (sectionAutEquiv (G := G) (U := U) x s).hom =
      QuotientTransporter.arrowOfSection (G := G) (U := U) x x s := by
  change (asIso (QuotientTransporter.arrowOfSection (G := G) (U := U) x x s)).hom = _
  exact asIso_hom _

end Stabilizer

end GromovWitten.AlgebraicGeometry.QuotientTransporterGeometry
