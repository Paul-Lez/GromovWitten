/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Stacks.EtaleAtlasDiagonal
import GromovWitten.AlgebraicGeometry.Stacks.SchemeAtlasRefinementReverse

/-!
# Transport and comparison of diagonal presentations

A `DiagonalPresentation X T x y` is a scheme over `T` representing the sheaf of isomorphisms
between two objects `x y` of the stack fibre over `T`.  This file proves the formal
(2-categorical) facts needed to compare such presentations, and applies them to the
isomorphism schemes of two charts over a common refinement.

The two coherences of the stack pseudofunctor used throughout are the unit law
(`stackPullbackIso_id`, pulling back along an identity) and the associativity law
(`stackPullbackIso_comp`, pulling back in two steps), both stated for `stackPullbackIso`, the
form in which `diagonalInducedIso` is defined.

## Main results

* `stackPullbackIso_id`, `stackPullbackIso_comp`: unit and associativity coherence of
  `stackPullbackIso`, up to `stackPullbackObjIsoOfEq`.
* `DiagonalClassifies.precomp`: if `g` classifies `e` over `f`, then `ℓ ≫ g` classifies
  `stackPullbackIso X ℓ f e` over `ℓ ≫ f`.
* `DiagonalClassifies.self`, `DiagonalClassifies.id`, `DiagonalClassifies.comp`:
  self-classification, classification of the universal isomorphism by the identity, and
  composition of classifying maps.
* `DiagonalPresentation.lift_comp` (naturality of `lift`), `DiagonalPresentation.lift_self`,
  `DiagonalPresentation.lift_map_universalIso`.
* `DiagonalPresentation.transport`: transport of a presentation along isomorphisms
  `x ≅ x'`, `y ≅ y'`, with the same `space` and `map` (`transport_space`, `transport_map`,
  both `rfl`).
* `DiagonalPresentation.comparisonIso`: any two presentations of the same pair have isomorphic
  presenting schemes, compatibly with the structure maps (`comparisonIso_hom_map`,
  `comparisonIso_inv_map`).
* `StackChart.isomSchemeIso`: for representable charts `A`, `B` and
  `p : B.PullbackPresentation A.scheme A.tautObj`, the isomorphism scheme of the pair
  `(prod.fst ≫ p.fst, prod.snd ≫ p.fst)` of `A`-objects over `p.space ⨯ p.space` is isomorphic
  over `p.space ⨯ p.space` to the isomorphism scheme of the pair
  `(prod.fst ≫ p.snd, prod.snd ≫ p.snd)` of `B`-objects (`isomSchemeIso_hom_map`,
  `isomSchemeIso_inv_map`).
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

variable {X : FppfStack.{u}}

/-! ## Unit and associativity coherences for pullback isomorphisms -/

/-- The equality-transport isomorphism `stackPullbackObjIsoOfEq` is an `eqToHom`. -/
theorem stackPullbackObjIsoOfEq_hom_eq_eqToHom {R T : Scheme.{u}} {f g : R ⟶ T}
    (h : f = g) (x : StackFiber X T) :
    (stackPullbackObjIsoOfEq X h x).hom = eqToHom (by rw [h]) := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Unit coherence: the compositor along `𝟙 ≫ map`, corrected by the transport along
`𝟙 ≫ map = map`, is the unit isomorphism of the stack pseudofunctor. -/
theorem stackPullbackCompIso_id_hom {U T : Scheme.{u}} (map : U ⟶ T)
    (z : StackFiber X T) :
    (stackPullbackCompIso X (𝟙 U) map z).hom ≫
        (stackPullbackObjIsoOfEq X (Category.id_comp map) z).hom =
      (X.toPseudofunctor.mapId (LocallyDiscrete.mk (Opposite.op U))).hom.toNatTrans.app
        ((stackPullback X map).obj z) := by
  have h0 : (stackPullbackCompIso X (𝟙 U) map z).hom =
      (X.toPseudofunctor.mapComp (⟨map.op⟩ : LocallyDiscrete.mk (Opposite.op T) ⟶
          LocallyDiscrete.mk (Opposite.op U))
        (𝟙 (LocallyDiscrete.mk (Opposite.op U)))).inv.toNatTrans.app z := rfl
  have h4 : (X.toPseudofunctor.map₂ (Bicategory.rightUnitor
      (⟨map.op⟩ : LocallyDiscrete.mk (Opposite.op T) ⟶
      LocallyDiscrete.mk (Opposite.op U))).inv).toNatTrans.app z = 𝟙 _ := by
    simp only [Bicategory.Strict.rightUnitor_eqToIso, eqToIso.inv, PrelaxFunctor.map₂_eqToHom,
      Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app]
    apply eqToHom_refl
  rw [h0, Pseudofunctor.mapComp_id_right_inv_app, h4]
  simp only [stackPullbackObjIsoOfEq_hom_eq_eqToHom, eqToHom_refl]
  erw [Category.comp_id, Category.comp_id]

/-- Unit coherence for `stackPullbackIso`: pulling an isomorphism back along an identity and
transporting along `𝟙 ≫ map = map` gives back the isomorphism. -/
theorem stackPullbackIso_id {U T : Scheme.{u}} (map : U ⟶ T) {x y : StackFiber X T}
    (e : (stackPullback X map).obj x ≅ (stackPullback X map).obj y) :
    (stackPullbackObjIsoOfEq X (Category.id_comp map) x).symm ≪≫
        stackPullbackIso X (𝟙 U) map e ≪≫ stackPullbackObjIsoOfEq X (Category.id_comp map) y =
      e := by
  apply Iso.ext
  have hx := stackPullbackCompIso_id_hom (X := X) map x
  have hy := stackPullbackCompIso_id_hom (X := X) map y
  have hn : (stackPullback X (𝟙 U)).map e.hom ≫
      (X.toPseudofunctor.mapId (LocallyDiscrete.mk (Opposite.op U))).hom.toNatTrans.app
        ((stackPullback X map).obj y) =
      (X.toPseudofunctor.mapId (LocallyDiscrete.mk (Opposite.op U))).hom.toNatTrans.app
        ((stackPullback X map).obj x) ≫ e.hom :=
    (X.toPseudofunctor.mapId (LocallyDiscrete.mk (Opposite.op U))).hom.toNatTrans.naturality
      e.hom
  simp only [stackPullbackIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [hy, hn, ← hx]
  simp

/-- Associativity coherence for `stackPullbackIso`: pulling back in two steps agrees with
pulling back along the composite, after transport along associativity. -/
theorem stackPullbackIso_comp {R S U T : Scheme.{u}} (ℓ : R ⟶ S) (g : S ⟶ U) (map : U ⟶ T)
    {x y : StackFiber X T}
    (e : (stackPullback X map).obj x ≅ (stackPullback X map).obj y) :
    stackPullbackIso X ℓ (g ≫ map) (stackPullbackIso X g map e) =
      (stackPullbackObjIsoOfEq X (Category.assoc ℓ g map) x).symm ≪≫
        stackPullbackIso X (ℓ ≫ g) map e ≪≫
          stackPullbackObjIsoOfEq X (Category.assoc ℓ g map) y := by
  apply Iso.ext
  have hx := stackPullbackCompIso_assoc X ℓ g map x
  have hy := stackPullbackCompIso_assoc X ℓ g map y
  have hx' : (stackPullbackCompIso X ℓ (g ≫ map) x).inv ≫
      (stackPullback X ℓ).map (stackPullbackCompIso X g map x).inv ≫
        (stackPullbackCompIso X ℓ g ((stackPullback X map).obj x)).hom =
      (stackPullbackObjIsoOfEq X (Category.assoc ℓ g map) x).inv ≫
        (stackPullbackCompIso X (ℓ ≫ g) map x).inv := by
    rw [Iso.inv_comp_eq, ← Functor.mapIso_inv, Iso.inv_comp_eq, ← Category.assoc,
      Functor.mapIso_hom, hx]
    simp
  simp only [stackPullbackIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [hy, StackChart.stackPullbackCompIso_naturality_assoc, reassoc_of% hx']

/-! ## Precomposition and self-classification (D.2.1) -/

namespace DiagonalClassifies

variable {U T : Scheme.{u}} {map : U ⟶ T} {x y : StackFiber X T}
  {universal : (stackPullback X map).obj x ≅ (stackPullback X map).obj y}

/-- **Precomposition.**  If `g` classifies `e` over `f`, then `ℓ ≫ g` classifies the pullback
`stackPullbackIso X ℓ f e` of `e` over `ℓ ≫ f`. -/
theorem precomp {S : Scheme.{u}} {f : S ⟶ T}
    {e : (stackPullback X f).obj x ≅ (stackPullback X f).obj y} {g : S ⟶ U}
    (h : DiagonalClassifies X map universal f e g) {S' : Scheme.{u}} (ℓ : S' ⟶ S) :
    DiagonalClassifies X map universal (ℓ ≫ f) (stackPullbackIso X ℓ f e) (ℓ ≫ g) := by
  obtain ⟨map_eq, he⟩ := h
  subst map_eq
  subst he
  refine ⟨Category.assoc ℓ g map, ?_⟩
  have hrefl : (stackPullbackObjIsoOfEq X (rfl : g ≫ map = g ≫ map) x).symm ≪≫
      (diagonalInducedIso X map universal g ≪≫ stackPullbackObjIsoOfEq X rfl y) =
        stackPullbackIso X g map universal := by
    apply Iso.ext
    simp [stackPullbackObjIsoOfEq, diagonalInducedIso]
  rw [hrefl]
  exact (stackPullbackIso_comp (X := X) ℓ g map universal).symm

/-- **Self-classification.**  Every map `g` into the presenting scheme classifies the pullback
of the universal isomorphism along `g`, over `g ≫ map`. -/
theorem self {S : Scheme.{u}} (g : S ⟶ U) :
    DiagonalClassifies X map universal (g ≫ map) (diagonalInducedIso X map universal g) g := by
  refine ⟨rfl, ?_⟩
  apply Iso.ext
  simp [stackPullbackObjIsoOfEq]

/-- The identity of the presenting scheme classifies the universal isomorphism over `map`
(the unit coherence of the stack pseudofunctor). -/
theorem id : DiagonalClassifies X map universal map universal (𝟙 U) :=
  ⟨Category.id_comp map, stackPullbackIso_id map universal⟩

/-- **Composition of classifying maps.**  If `k` classifies `e` for the presentation
`(map', universal')`, and `g` classifies `universal'` for the presentation `(map, universal)`,
then `k ≫ g` classifies `e` for `(map, universal)`. -/
theorem comp {U' : Scheme.{u}} {map' : U' ⟶ T}
    {universal' : (stackPullback X map').obj x ≅ (stackPullback X map').obj y}
    {S : Scheme.{u}} {f : S ⟶ T}
    {e : (stackPullback X f).obj x ≅ (stackPullback X f).obj y} {k : S ⟶ U'} {g : U' ⟶ U}
    (hk : DiagonalClassifies X map' universal' f e k)
    (hg : DiagonalClassifies X map universal map' universal' g) :
    DiagonalClassifies X map universal f e (k ≫ g) := by
  obtain ⟨hk1, hk2⟩ := hk
  subst hk1
  subst hk2
  obtain ⟨m, hm⟩ := hg.precomp k
  refine ⟨m, ?_⟩
  rw [hm]
  apply Iso.ext
  simp [stackPullbackObjIsoOfEq, diagonalInducedIso]

end DiagonalClassifies

namespace DiagonalPresentation

variable {T : Scheme.{u}} {x y : StackFiber X T} (D : DiagonalPresentation X T x y)

/-- **Naturality of `lift`.**  Precomposing the lift of `e` with `ℓ` is the lift of the
pullback of `e` along `ℓ`. -/
theorem lift_comp {S : Scheme.{u}} (f : S ⟶ T)
    (e : (stackPullback X f).obj x ≅ (stackPullback X f).obj y) {S' : Scheme.{u}}
    (ℓ : S' ⟶ S) :
    ℓ ≫ D.lift f e = D.lift (ℓ ≫ f) (stackPullbackIso X ℓ f e) :=
  D.lift_unique _ _ _ ((D.lift_compatible f e).precomp ℓ)

/-- **Self-classification of maps into the presenting scheme.** -/
theorem lift_self {S : Scheme.{u}} (g : S ⟶ D.space) :
    g = D.lift (g ≫ D.map) (diagonalInducedIso X D.map D.universalIso g) :=
  D.lift_unique _ _ _ (DiagonalClassifies.self g)

/-- The lift of the universal isomorphism itself is the identity. -/
theorem lift_map_universalIso : D.lift D.map D.universalIso = 𝟙 D.space :=
  (D.lift_unique _ _ _ DiagonalClassifies.id).symm

end DiagonalPresentation

/-! ## Transport along isomorphisms of the two objects (D.2.2) -/

/-- The pullback of a conjugated universal isomorphism is the conjugate of the pullback
(naturality of the pseudofunctor compositors). -/
theorem diagonalInducedIso_conj {U T : Scheme.{u}} (map : U ⟶ T) {x y x' y' : StackFiber X T}
    (α : x ≅ x') (β : y ≅ y')
    (universal : (stackPullback X map).obj x ≅ (stackPullback X map).obj y)
    {S : Scheme.{u}} (g : S ⟶ U) :
    diagonalInducedIso X map
        (((stackPullback X map).mapIso α).symm ≪≫ universal ≪≫ (stackPullback X map).mapIso β)
        g =
      ((stackPullback X (g ≫ map)).mapIso α).symm ≪≫ diagonalInducedIso X map universal g ≪≫
        (stackPullback X (g ≫ map)).mapIso β := by
  apply Iso.ext
  have hα : (stackPullbackCompIso X g map x').inv ≫
      (stackPullback X g).map ((stackPullback X map).map α.inv) =
      (stackPullback X (g ≫ map)).map α.inv ≫ (stackPullbackCompIso X g map x).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact StackChart.stackPullbackCompIso_naturality g map α.inv
  simp only [diagonalInducedIso, stackPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  rw [StackChart.stackPullbackCompIso_naturality, reassoc_of% hα]

namespace DiagonalClassifies

/-- Classification for a conjugated universal isomorphism is classification of the
correspondingly conjugated isomorphism. -/
theorem conj_iff {U T : Scheme.{u}} {map : U ⟶ T} {x y x' y' : StackFiber X T}
    (α : x ≅ x') (β : y ≅ y')
    (universal : (stackPullback X map).obj x ≅ (stackPullback X map).obj y)
    {S : Scheme.{u}} {f : S ⟶ T}
    (e : (stackPullback X f).obj x' ≅ (stackPullback X f).obj y') (g : S ⟶ U) :
    DiagonalClassifies X map
        (((stackPullback X map).mapIso α).symm ≪≫ universal ≪≫ (stackPullback X map).mapIso β)
        f e g ↔
      DiagonalClassifies X map universal f
        ((stackPullback X f).mapIso α ≪≫ e ≪≫ ((stackPullback X f).mapIso β).symm) g := by
  constructor
  · rintro ⟨h, he⟩
    subst h
    subst he
    refine ⟨rfl, ?_⟩
    rw [diagonalInducedIso_conj]
    apply Iso.ext
    simp [stackPullbackObjIsoOfEq]
  · rintro ⟨h, he⟩
    subst h
    refine ⟨rfl, ?_⟩
    have he' : e = ((stackPullback X (g ≫ map)).mapIso α).symm ≪≫
        ((stackPullback X (g ≫ map)).mapIso α ≪≫ e ≪≫
          ((stackPullback X (g ≫ map)).mapIso β).symm) ≪≫
        (stackPullback X (g ≫ map)).mapIso β := by
      apply Iso.ext
      simp
    rw [he', ← he, diagonalInducedIso_conj]
    apply Iso.ext
    simp [stackPullbackObjIsoOfEq]

end DiagonalClassifies

namespace DiagonalPresentation

variable {T : Scheme.{u}} {x y : StackFiber X T} (D : DiagonalPresentation X T x y)

/-- **Transport of a diagonal presentation along isomorphisms of the two objects.**  The
presenting scheme and its structure map are unchanged; the universal isomorphism is conjugated
by the pulled-back isomorphisms `α`, `β`. -/
noncomputable def transport {x' y' : StackFiber X T} (α : x ≅ x') (β : y ≅ y') :
    DiagonalPresentation X T x' y' where
  space := D.space
  map := D.map
  universalIso :=
    ((stackPullback X D.map).mapIso α).symm ≪≫ D.universalIso ≪≫
      (stackPullback X D.map).mapIso β
  lift f e := D.lift f ((stackPullback X f).mapIso α ≪≫ e ≪≫ ((stackPullback X f).mapIso β).symm)
  lift_map _ _ := D.lift_map _ _
  lift_compatible _ e :=
    (DiagonalClassifies.conj_iff α β D.universalIso e _).2 (D.lift_compatible _ _)
  lift_unique _ e g h :=
    D.lift_unique _ _ _ ((DiagonalClassifies.conj_iff α β D.universalIso e g).1 h)

/-- The transported presentation has the same presenting scheme. -/
@[simp]
theorem transport_space {x' y' : StackFiber X T} (α : x ≅ x') (β : y ≅ y') :
    (D.transport α β).space = D.space := rfl

/-- The transported presentation has the same structure map. -/
@[simp]
theorem transport_map {x' y' : StackFiber X T} (α : x ≅ x') (β : y ≅ y') :
    (D.transport α β).map = D.map := rfl

/-- The universal isomorphism of the transported presentation is the conjugate one. -/
theorem transport_universalIso {x' y' : StackFiber X T} (α : x ≅ x') (β : y ≅ y') :
    (D.transport α β).universalIso =
      ((stackPullback X D.map).mapIso α).symm ≪≫ D.universalIso ≪≫
        (stackPullback X D.map).mapIso β := rfl

/-- Lifts for the transported presentation are lifts of the conjugated isomorphism. -/
theorem transport_lift {x' y' : StackFiber X T} (α : x ≅ x') (β : y ≅ y')
    {S : Scheme.{u}} (f : S ⟶ T)
    (e : (stackPullback X f).obj x' ≅ (stackPullback X f).obj y') :
    (D.transport α β).lift f e =
      D.lift f ((stackPullback X f).mapIso α ≪≫ e ≪≫ ((stackPullback X f).mapIso β).symm) :=
  rfl


/-! ## Comparison of two presentations of the same pair (D.2.3) -/

/-- **Comparison of two presentations of the same isomorphism sheaf.**  The two lifts of the
universal isomorphisms are mutually inverse. -/
noncomputable def comparisonIso (D' : DiagonalPresentation X T x y) : D.space ≅ D'.space where
  hom := D'.lift D.map D.universalIso
  inv := D.lift D'.map D'.universalIso
  hom_inv_id := by
    rw [← D.lift_map_universalIso]
    exact D.lift_unique _ _ _
      ((D'.lift_compatible D.map D.universalIso).comp (D.lift_compatible _ _))
  inv_hom_id := by
    rw [← D'.lift_map_universalIso]
    exact D'.lift_unique _ _ _
      ((D.lift_compatible D'.map D'.universalIso).comp (D'.lift_compatible _ _))

/-- The forward comparison map is the lift of `D.universalIso` into `D'`. -/
@[simp]
theorem comparisonIso_hom (D' : DiagonalPresentation X T x y) :
    (D.comparisonIso D').hom = D'.lift D.map D.universalIso := rfl

/-- The backward comparison map is the lift of `D'.universalIso` into `D`. -/
@[simp]
theorem comparisonIso_inv (D' : DiagonalPresentation X T x y) :
    (D.comparisonIso D').inv = D.lift D'.map D'.universalIso := rfl

/-- The comparison isomorphism lies over the base. -/
@[reassoc (attr := simp)]
theorem comparisonIso_hom_map (D' : DiagonalPresentation X T x y) :
    (D.comparisonIso D').hom ≫ D'.map = D.map :=
  D'.lift_map _ _

/-- The inverse comparison isomorphism lies over the base. -/
@[reassoc (attr := simp)]
theorem comparisonIso_inv_map (D' : DiagonalPresentation X T x y) :
    (D.comparisonIso D').inv ≫ D.map = D'.map :=
  D.lift_map _ _

end DiagonalPresentation

/-! ## Application: the Isom schemes of two charts over a common refinement (D.2.4) -/

namespace StackChart

variable {A B : StackChart X} (hA : A.IsRepresentable) (hB : B.IsRepresentable)
  (p : B.PullbackPresentation A.scheme A.tautObj)

/-- The isomorphism-scheme presentation of chart `A` over `p.space ⨯ p.space`, transported along
the common-refinement comparisons `commonSchemeAtlasComparison p prod.fst` and
`commonSchemeAtlasComparison p prod.snd` to a presentation of the pair of `B`-objects. -/
noncomputable def isomSchemeTransportPresentation :
    DiagonalPresentation X (p.space ⨯ p.space)
      (B.obj (p.space ⨯ p.space) (prod.fst ≫ p.snd))
      (B.obj (p.space ⨯ p.space) (prod.snd ≫ p.snd)) :=
  (A.isomDiagonalPresentation hA (prod.fst ≫ p.fst) (prod.snd ≫ p.fst)).transport
    (commonSchemeAtlasComparison p prod.fst) (commonSchemeAtlasComparison p prod.snd)

/-- **The Isom schemes of two charts over a common refinement are isomorphic.**  For
`p : B.PullbackPresentation A.scheme A.tautObj`, the isomorphism scheme of the pair
`(prod.fst ≫ p.fst, prod.snd ≫ p.fst)` of `A`-objects over `p.space ⨯ p.space` is isomorphic,
over `p.space ⨯ p.space`, to the isomorphism scheme of the pair `(prod.fst ≫ p.snd,
prod.snd ≫ p.snd)` of `B`-objects. -/
noncomputable def isomSchemeIso :
    A.isomScheme hA (prod.fst ≫ p.fst) (prod.snd ≫ p.fst) ≅
      B.isomScheme hB (prod.fst ≫ p.snd) (prod.snd ≫ p.snd) :=
  (isomSchemeTransportPresentation hA p).comparisonIso
    (B.isomDiagonalPresentation hB (prod.fst ≫ p.snd) (prod.snd ≫ p.snd))

/-- `isomSchemeIso` lies over `p.space ⨯ p.space`. -/
@[reassoc (attr := simp)]
theorem isomSchemeIso_hom_map :
    (isomSchemeIso hA hB p).hom ≫ B.isomScheme_map hB (prod.fst ≫ p.snd) (prod.snd ≫ p.snd) =
      A.isomScheme_map hA (prod.fst ≫ p.fst) (prod.snd ≫ p.fst) :=
  DiagonalPresentation.comparisonIso_hom_map _ _

/-- The inverse of `isomSchemeIso` lies over `p.space ⨯ p.space`. -/
@[reassoc (attr := simp)]
theorem isomSchemeIso_inv_map :
    (isomSchemeIso hA hB p).inv ≫ A.isomScheme_map hA (prod.fst ≫ p.fst) (prod.snd ≫ p.fst) =
      B.isomScheme_map hB (prod.fst ≫ p.snd) (prod.snd ≫ p.snd) :=
  DiagonalPresentation.comparisonIso_inv_map _ _

end StackChart


end GromovWitten.AlgebraicGeometry
