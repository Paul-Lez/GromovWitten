/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.Properties

/-!
# Transport of stack-morphism presentations across invertible 2-cells

An invertible 2-cell between stack morphisms transports every scheme-valued presentation of
one morphism to a presentation of the other.  This file constructs that transport, including
the induced comparison equation and both uniqueness laws.  Consequently the raw definition of
a representable property is itself invariant under invertible 2-cells.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackMorphismPresentation

variable {X Y : FppfStack.{u}} {f g : StackHom X Y}

noncomputable def transportUniversal
    (e : StackIso2 f g) {T : Scheme.{u}} {y : StackFiber Y T}
    (p : StackMorphismPresentation g T y) :
    (f.appFunctor p.space).obj p.object ≅
      (stackPullback Y p.map).obj y :=
  ((e.appIso p.space).app p.object).trans p.comparison

noncomputable def transportInputComparison
    (e : StackIso2 f g) {T S : Scheme.{u}} {y : StackFiber Y T}
    (toBase : S ⟶ T) (x : StackFiber X S)
    (c : (f.appFunctor S).obj x ≅ (stackPullback Y toBase).obj y) :
    (g.appFunctor S).obj x ≅ (stackPullback Y toBase).obj y :=
  ((e.appIso S).symm.app x).trans c

set_option backward.isDefEq.respectTransparency false in
theorem stackIso2_naturality_hom_app
    (e : StackIso2 f g) {S U : Scheme.{u}} (l : S ⟶ U)
    (x : StackFiber X U) :
    (e.appIso S).hom.app ((stackPullback X l).obj x) ≫
        (Cat.Hom.toNatIso (g.naturality ⟨l.op⟩)).hom.app x =
      (Cat.Hom.toNatIso (f.naturality ⟨l.op⟩)).hom.app x ≫
        (stackPullback Y l).map ((e.appIso U).hom.app x) := by
  have h := congrArg
    (fun η ↦ η.toNatTrans.app x) (e.hom.naturality ⟨l.op⟩)
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem stackMorphismInducedComparison_transport_hom
    (e : StackIso2 f g) {T : Scheme.{u}} {y : StackFiber Y T}
    (p : StackMorphismPresentation g T y)
    {S : Scheme.{u}} (l : S ⟶ p.space) (x : StackFiber X S)
    (objectIso : x ≅ (stackPullback X l).obj p.object) :
    (stackMorphismInducedComparison f p.map p.object y
      (transportUniversal e p) l x objectIso).hom =
      (e.appIso S).hom.app x ≫
        (stackMorphismInducedComparison g p.map p.object y
          p.comparison l x objectIso).hom := by
  dsimp only [stackMorphismInducedComparison, transportUniversal]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  simp only [Iso.app_hom]
  rw [← reassoc_of% stackIso2_naturality_hom_app e l p.object]
  rw [reassoc_of% (e.appIso S).hom.naturality objectIso.hom]

set_option backward.isDefEq.respectTransparency false in
theorem stackMorphismClassifies_transport_iff
    (e : StackIso2 f g) {T : Scheme.{u}} {y : StackFiber Y T}
    (p : StackMorphismPresentation g T y)
    {S : Scheme.{u}} (toBase : S ⟶ T) (x : StackFiber X S)
    (c : (f.appFunctor S).obj x ≅ (stackPullback Y toBase).obj y)
    (l : S ⟶ p.space)
    (objectIso : x ≅ (stackPullback X l).obj p.object) :
    StackMorphismClassifies f p.map p.object y (transportUniversal e p)
        toBase x c l objectIso ↔
      StackMorphismClassifies g p.map p.object y p.comparison
        toBase x (transportInputComparison e toBase x c) l objectIso := by
  constructor
  · rintro ⟨hmap, hcomparison⟩
    refine ⟨hmap, ?_⟩
    apply Iso.ext
    rw [← cancel_epi ((e.appIso S).hom.app x)]
    dsimp only [transportInputComparison]
    simp only [Iso.trans_hom]
    have hsymm : ((e.appIso S).symm.app x).hom =
        (e.appIso S).inv.app x := rfl
    rw [hsymm]
    rw [Iso.hom_inv_id_app_assoc]
    rw [← reassoc_of% stackMorphismInducedComparison_transport_hom
      e p l x objectIso]
    exact congrArg Iso.hom hcomparison
  · rintro ⟨hmap, hcomparison⟩
    refine ⟨hmap, ?_⟩
    apply Iso.ext
    simp only [Iso.trans_hom]
    rw [stackMorphismInducedComparison_transport_hom e p l x objectIso]
    dsimp only [transportInputComparison] at hcomparison
    have hcomparisonHom := congrArg Iso.hom hcomparison
    simp only [Iso.trans_hom] at hcomparisonHom
    have hsymm : ((e.appIso S).symm.app x).hom =
        (e.appIso S).inv.app x := rfl
    rw [Category.assoc, hcomparisonHom, hsymm]
    simp only [Iso.hom_inv_id_app_assoc]

/-- Transport a complete morphism presentation across an invertible stack
2-cell.  The representing scheme is unchanged, while every classification and
uniqueness field is transported through the component natural isomorphism. -/
noncomputable def transport
    (e : StackIso2 f g) {T : Scheme.{u}} {y : StackFiber Y T}
    (p : StackMorphismPresentation g T y) :
    StackMorphismPresentation f T y where
  space := p.space
  map := p.map
  object := p.object
  comparison := transportUniversal e p
  lift := fun toBase x c ↦
    p.lift toBase x (transportInputComparison e toBase x c)
  lift_map := fun toBase x c ↦
    p.lift_map toBase x (transportInputComparison e toBase x c)
  liftObjectIso := fun toBase x c ↦
    p.liftObjectIso toBase x (transportInputComparison e toBase x c)
  lift_compatible := fun toBase x c ↦
    (stackMorphismClassifies_transport_iff e p toBase x c
      (p.lift toBase x (transportInputComparison e toBase x c))
      (p.liftObjectIso toBase x
        (transportInputComparison e toBase x c))).mpr
      (p.lift_compatible toBase x
        (transportInputComparison e toBase x c))
  liftObjectIso_unique := fun toBase x c objectIso compatible ↦
    p.liftObjectIso_unique toBase x
      (transportInputComparison e toBase x c) objectIso
      ((stackMorphismClassifies_transport_iff e p toBase x c
        (p.lift toBase x (transportInputComparison e toBase x c))
        objectIso).mp compatible)
  lift_unique := fun toBase x c l objectIso compatible ↦
    p.lift_unique toBase x (transportInputComparison e toBase x c)
      l objectIso
      ((stackMorphismClassifies_transport_iff e p toBase x c l
        objectIso).mp compatible)

end StackMorphismPresentation

namespace StackHom

variable {X Y : FppfStack.{u}} {f g : StackHom X Y}

/-- Raw presentation-level representability is invariant under invertible
2-cells once presentations are transported explicitly. -/
theorem hasRepresentablePropertyRaw_congr
    (P : MorphismProperty Scheme.{u}) (e : StackIso2 f g) :
    f.HasRepresentablePropertyRaw P ↔ g.HasRepresentablePropertyRaw P := by
  constructor
  · intro hf T y
    obtain ⟨⟨p, hp⟩⟩ := hf T y
    exact ⟨⟨StackMorphismPresentation.transport e.symm p, hp⟩⟩
  · intro hg T y
    obtain ⟨⟨p, hp⟩⟩ := hg T y
    exact ⟨⟨StackMorphismPresentation.transport e p, hp⟩⟩

/-- The explicit 2-isomorphism-invariant closure agrees with raw
representability after the transport construction. -/
theorem hasRepresentableProperty_iff_raw
    (P : MorphismProperty Scheme.{u}) :
    f.HasRepresentableProperty P ↔ f.HasRepresentablePropertyRaw P := by
  constructor
  · rintro ⟨g, ⟨e⟩, hg⟩
    exact (hasRepresentablePropertyRaw_congr P e).mpr hg
  · intro hf
    exact ⟨f, ⟨StackIso2.refl f⟩, hf⟩

end StackHom

end GromovWitten.AlgebraicGeometry
