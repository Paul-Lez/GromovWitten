/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Stacks.EtaleAtlasDiagonal
import GromovWitten.AlgebraicGeometry.Stacks.StrongTransOfDiscrete
import GromovWitten.AlgebraicGeometry.Stacks.PresentationTransport
import GromovWitten.AlgebraicGeometry.Stacks.PropertiesDescent
import GromovWitten.AlgebraicGeometry.Stacks.DiagonalPresentationTransport

/-!
# Base change of a chart along a representable stack morphism

Let `f : StackHom X Y` be a representable morphism of fppf stacks and `B` a chart of `Y`.  A
scheme presentation `p` of the base change of `f` along the tautological object of `B` (the
scheme `B.scheme ×_Y X`) carries a universal object `p.object` of `X` over `p.space`; this file
turns it into a chart of `X`, the **base-change chart**, and proves:

* every representable property of `B` (for instance étale surjectivity) is inherited by the
  base-change chart;
* the projection `p.map` of the base-change chart to `B.scheme` has every scheme property
  respecting isomorphisms that `f` has representably (for instance properness);
* the self-overlap of the base-change chart is the base change of the self-overlap of `B` along
  `p.map`, through either projection: both squares
  `selfOverlap(A) → selfOverlap(B)` over `p.map` are cartesian.

All arguments are carried out at the level of *fibre points* (`StackChart.FibrePoint`): an
`S`-point of `C.scheme ×_Z T` over a test map `tb : S ⟶ T` is a map `S ⟶ C.scheme` together with
an isomorphism of objects of the stack over `S`.  A scheme presentation of a chart is exactly a
representing object for its fibre points (`StackChart.classifies_iff_pullbackPoint`), so a natural
bijection of fibre points transfers presentations (`PullbackPresentation.transfer`) and produces
cartesian squares of presenting schemes (`StackChart.isPullback_presentationMap`).  The pasting
law `T ×_X (X ×_Y B.scheme) ≅ T ×_Y B.scheme` is then the natural bijection
`StackHom.baseChangePointEquiv`, proved from the universal property of `p`.

## Main results

* `StackHom.ofObject`, `StackChart.ofObject`: the stack morphism `representedStack T ⟶ X`
  classifying an object `x` of `X` over `T` (2-Yoneda), and the corresponding chart.
* `StackChart.FibrePointEquiv`, `StackChart.PullbackPresentation.transfer`: natural equivalences
  of fibre points and transfer of presentations along them.
* `StackChart.presentationMap`, `StackChart.isPullback_presentationMap`: the map of presenting
  schemes induced by a natural equivalence of fibre points over `π : T ⟶ T'` is a base change.
* `StackHom.chartOfPresentation`, `StackHom.baseChangePointEquiv`: the base-change chart of a
  presentation and the pasting law for its fibre points.
* `StackHom.chartOfPresentation_hasRepresentableProperty`,
  `StackHom.chartOfPresentation_isEtaleSurjective`, `StackHom.presentation_map_property`.
* `StackHom.baseChangeChart`, `StackHom.baseChangeChartToBase`,
  `StackHom.baseChangeChart_isEtaleSurjective`, `StackHom.baseChangeChart_hasRepresentableProperty`,
  `StackHom.baseChangeChartToBase_isProper`: the same for a chosen presentation of a representable
  `f`.
* `StackHom.selfOverlapMap`, `StackHom.selfOverlapMap_fst`, `StackHom.selfOverlapMap_snd`,
  `StackHom.isPullback_selfOverlapMap_fst`, `StackHom.isPullback_selfOverlapMap_snd`: the two
  cartesian squares of self-overlap schemes.

## Future work

* Computation lemmas for the induced Vistoli pushforward on classes, and independence of the
  base-change chart (and of the pushforward) from the chosen presentation
  `StackHom.baseChangePresentation`.
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

/-! ## Two coherences of the stack pseudofunctor -/

section Coherence

variable {X : FppfStack.{u}}

/-- Unit coherence of the pullback compositor: the inverse compositor along `𝟙 ≫ map`, followed
by the unit constraint of the stack pseudofunctor, is the transport along `𝟙 ≫ map = map`
(`stackPullbackCompIso_id_hom` solved for the inverse). -/
theorem stackPullbackCompIso_id_inv {U T : Scheme.{u}} (map : U ⟶ T) (z : StackFiber X T) :
    (stackPullbackCompIso X (𝟙 U) map z).inv ≫
      (X.toPseudofunctor.mapId (LocallyDiscrete.mk (Opposite.op U))).hom.toNatTrans.app
        ((stackPullback X map).obj z) =
      (stackPullbackObjIsoOfEq X (Category.id_comp map) z).hom := by
  rw [← stackPullbackCompIso_id_hom, Iso.inv_hom_id_assoc]

/-- Associativity of the inverse pullback compositors, solved for the composite along
`(G ≫ F) ≫ h`. -/
theorem stackPullbackCompIso_inv_assoc {R S U V : Scheme.{u}}
    (G : R ⟶ S) (F : S ⟶ U) (h : U ⟶ V) (z : StackFiber X V) :
    (stackPullbackCompIso X (G ≫ F) h z).inv ≫
        (stackPullbackCompIso X G F ((stackPullback X h).obj z)).inv =
      (stackPullbackObjIsoOfEq X (Category.assoc G F h) z).hom ≫
        (stackPullbackCompIso X G (F ≫ h) z).inv ≫
          (stackPullback X G).map (stackPullbackCompIso X F h z).inv := by
  have hA : (stackPullback X G).mapIso (stackPullbackCompIso X F h z) ≪≫
      stackPullbackCompIso X G (F ≫ h) z =
      stackPullbackCompIso X G F ((stackPullback X h).obj z) ≪≫
        stackPullbackCompIso X (G ≫ F) h z ≪≫
          stackPullbackObjIsoOfEq X (Category.assoc G F h) z :=
    Iso.ext (stackPullbackCompIso_assoc X G F h z)
  have hB := congrArg Iso.inv hA
  simp only [Iso.trans_inv, Functor.mapIso_inv, Category.assoc] at hB
  rw [hB]
  simp

/-- Naturality of the pullback compositor in an equality of the second map. -/
theorem stackPullback_mapIso_objIsoOfEq_compIso {R S T : Scheme.{u}}
    (a : R ⟶ S) {g g' : S ⟶ T} (h : g = g') (z : StackFiber X T) :
    (stackPullback X a).mapIso (stackPullbackObjIsoOfEq X h z) ≪≫ stackPullbackCompIso X a g' z =
      stackPullbackCompIso X a g z ≪≫ stackPullbackObjIsoOfEq X (congrArg (a ≫ ·) h) z := by
  subst h
  apply Iso.ext
  simp

end Coherence

/-! ## The chart of an object over a scheme (2-Yoneda) -/

section OfObject

variable {X : FppfStack.{u}} {T : Scheme.{u}}

/-- The fibre functor of `StackHom.ofObject x` over a test scheme `S`: a map `g : S ⟶ T` (an
object of the discrete fibre of the represented stack) goes to the pullback of `x` along `g`. -/
private noncomputable def ofObjectApp (x : StackFiber X T) (S : Scheme.{u}) :
    StackFiber (representedStack T) S ⥤ StackFiber X S :=
  Discrete.functor (fun g : ULift (S ⟶ T) => (stackPullback X g.down).obj x)

/-- On (necessarily identity-like) arrows of the discrete fibre, `ofObjectApp` is the transport
along the corresponding equality of scheme maps. -/
private theorem ofObjectApp_map (x : StackFiber X T) (S : Scheme.{u}) {g₁ g₂ : S ⟶ T}
    (φ : (Discrete.mk (ULift.up g₁) : StackFiber (representedStack T) S) ⟶
      Discrete.mk (ULift.up g₂)) :
    (ofObjectApp x S).map φ =
      (stackPullbackObjIsoOfEq X (congrArg ULift.down (Discrete.eq_of_hom φ)) x).hom := by
  have h : g₁ = g₂ := congrArg ULift.down (Discrete.eq_of_hom φ)
  subst h
  have : φ = 𝟙 _ := Subsingleton.elim _ _
  subst this
  exact (ofObjectApp x S).map_id _

/-- **The stack morphism classifying an object (2-Yoneda).**  For an object `x` of the fibre of
`X` over a scheme `T`, the strong transformation `representedStack T ⟶ X` sending a test map
`g : S ⟶ T` to the pullback `(stackPullback X g).obj x`; its naturality isomorphisms are the
inverse pullback compositors, and its two coherence laws are the unit and associativity
coherences of the stack pseudofunctor. -/
noncomputable def StackHom.ofObject (x : StackFiber X T) : StackHom (representedStack T) X :=
  Pseudofunctor.StrongTrans.mkCatOfComponents
    (fun a => (ofObjectApp x a.as.unop).toCatHom)
    (fun {_ _} f => Cat.Hom.isoMk (Discrete.natIso (fun g =>
      (stackPullbackCompIso X f.as.unop g.as.down x).symm)))
    (fun a y => by
      obtain ⟨⟨U⟩⟩ := a
      obtain ⟨⟨g⟩⟩ := y
      have := ofObjectApp_map x U (g₁ := 𝟙 U ≫ g) (g₂ := g)
        (((representedStack T).toPseudofunctor.mapId _).hom.toNatTrans.app ⟨⟨g⟩⟩)
      erw [this]
      exact stackPullbackCompIso_id_inv g x)
    (fun f g y => by
      obtain ⟨⟨h⟩⟩ := y
      obtain ⟨F⟩ := f
      obtain ⟨G⟩ := g
      have := ofObjectApp_map x _ (g₁ := G.unop ≫ F.unop ≫ h) (g₂ := (G.unop ≫ F.unop) ≫ h)
        (((representedStack T).toPseudofunctor.mapComp ⟨F⟩ ⟨G⟩).hom.toNatTrans.app ⟨⟨h⟩⟩)
      erw [this]
      exact stackPullbackCompIso_inv_assoc G.unop F.unop h x)

/-- The chart of an object: the scheme `T` with the classifying morphism of `x`. -/
noncomputable def StackChart.ofObject (x : StackFiber X T) : StackChart X where
  scheme := T
  map := StackHom.ofObject x

/-- The objects of the chart of `x` are the pullbacks of `x` (definitionally). -/
theorem StackChart.ofObject_obj (x : StackFiber X T) {S : Scheme.{u}} (g : S ⟶ T) :
    (StackChart.ofObject x).obj S g = (stackPullback X g).obj x := rfl

/-- The pseudonaturality isomorphisms of the chart of `x` are the inverse compositors. -/
theorem StackChart.ofObject_objPullbackIso (x : StackFiber X T) {S S' : Scheme.{u}}
    (m : S' ⟶ S) (g : S ⟶ T) :
    (StackChart.ofObject x).objPullbackIso m g = (stackPullbackCompIso X m g x).symm := rfl

/-- Equality transport in the chart of `x` is equality transport of pullbacks. -/
theorem StackChart.ofObject_objIsoOfEq (x : StackFiber X T) {S : Scheme.{u}} {g g' : S ⟶ T}
    (h : g = g') :
    (StackChart.ofObject x).objIsoOfEq h = stackPullbackObjIsoOfEq X h x := by
  subst h
  rfl

end OfObject

/-! ## Fibre points of a chart over an object -/

namespace StackChart

section FibrePoint

variable {Z : FppfStack.{u}} (C : StackChart Z) {T : Scheme.{u}} (z : StackFiber Z T)

/-- A **fibre point** of the chart `C` over the object `z` lying over a test map
`tb : S ⟶ T`: a map `tc : S ⟶ C.scheme` together with an isomorphism between the chart object
at `tc` and the pullback of `z` along `tb`.  These are the `S`-points of the 2-fibre product
`C.scheme ×_Z T` lying over `tb`. -/
abbrev FibrePoint {S : Scheme.{u}} (tb : S ⟶ T) : Type (u + 1) :=
  Σ tc : S ⟶ C.scheme, C.obj S tc ≅ (stackPullback Z tb).obj z

/-- Pullback of a fibre point along a test map `m : S' ⟶ S`. -/
noncomputable def pullbackPoint {S S' : Scheme.{u}} (m : S' ⟶ S) {tb : S ⟶ T}
    (P : C.FibrePoint z tb) : C.FibrePoint z (m ≫ tb) :=
  ⟨m ≫ P.1, C.inducedComparison tb P.1 P.2 m⟩

/-- Transport of a fibre point along an equality of the underlying test maps. -/
noncomputable def castPoint {S : Scheme.{u}} {tb tb' : S ⟶ T} (h : tb = tb')
    (P : C.FibrePoint z tb) : C.FibrePoint z tb' :=
  ⟨P.1, P.2 ≪≫ stackPullbackObjIsoOfEq Z h z⟩

variable {C z}

/-- Transport in a chart along a reflexivity proof is the identity. -/
@[simp]
theorem objIsoOfEq_self' {S : Scheme.{u}} {a : S ⟶ C.scheme} (h : a = a) :
    C.objIsoOfEq h = Iso.refl _ := by
  rw [Subsingleton.elim h rfl]
  rfl

/-- Equality of fibre points: equal chart maps, and isomorphisms agreeing after transport. -/
theorem fibrePoint_ext_iff {S : Scheme.{u}} {tb : S ⟶ T} {a a' : S ⟶ C.scheme}
    {i : C.obj S a ≅ (stackPullback Z tb).obj z} {i' : C.obj S a' ≅ (stackPullback Z tb).obj z} :
    (⟨a, i⟩ : C.FibrePoint z tb) = ⟨a', i'⟩ ↔ ∃ e : a = a', (C.objIsoOfEq e).symm ≪≫ i = i' := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, by simp [objIsoOfEq]⟩
  · rintro ⟨rfl, h⟩
    simp only [objIsoOfEq, Iso.refl_symm, Iso.refl_trans] at h
    subst h
    rfl

/-- Transport along `rfl` is the identity. -/
@[simp]
theorem castPoint_rfl {S : Scheme.{u}} {tb : S ⟶ T} (P : C.FibrePoint z tb) :
    C.castPoint z rfl P = P := by
  obtain ⟨a, i⟩ := P
  simp [castPoint, stackPullbackObjIsoOfEq]

/-- Two successive transports compose. -/
@[simp]
theorem castPoint_castPoint {S : Scheme.{u}} {tb tb' tb'' : S ⟶ T} (h : tb = tb')
    (h' : tb' = tb'') (P : C.FibrePoint z tb) :
    C.castPoint z h' (C.castPoint z h P) = C.castPoint z (h.trans h') P := by
  subst h h'
  simp

/-- Classification is equality of the pulled-back universal fibre point with the given one
(after transport along the base equation). -/
theorem classifies_iff_pullbackPoint {U : Scheme.{u}} (fst : U ⟶ T) (snd : U ⟶ C.scheme)
    (univ : C.obj U snd ≅ (stackPullback Z fst).obj z) {S : Scheme.{u}}
    (tb : S ⟶ T) (tc : S ⟶ C.scheme) (c : C.obj S tc ≅ (stackPullback Z tb).obj z)
    (m : S ⟶ U) :
    C.Classifies fst snd univ tb tc c m ↔
      ∃ h : m ≫ fst = tb, C.castPoint z h (C.pullbackPoint z m ⟨snd, univ⟩) = ⟨tc, c⟩ := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fibrePoint_ext_iff.2 ⟨h2, ?_⟩⟩
    rw [← h3]
    rfl
  · rintro ⟨h1, h⟩
    obtain ⟨h2, h3⟩ := fibrePoint_ext_iff.1 h
    exact ⟨h1, h2, h3⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Functoriality of pullback of fibre points.** -/
theorem pullbackPoint_comp {S S' S'' : Scheme.{u}} (m : S' ⟶ S) (m' : S'' ⟶ S')
    {tb : S ⟶ T} (P : C.FibrePoint z tb) :
    C.pullbackPoint z (m' ≫ m) P =
      C.castPoint z (Category.assoc m' m tb).symm
        (C.pullbackPoint z m' (C.pullbackPoint z m P)) := by
  obtain ⟨a, i⟩ := P
  refine fibrePoint_ext_iff.2 ⟨Category.assoc m' m a, ?_⟩
  apply Iso.ext
  have h1 := congrArg Iso.hom (C.mapIso_objPullbackIso_comp m a m')
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc] at h1
  simp only [pullbackPoint, inducedComparison_eq, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (stackPullbackCompIso_assoc Z m' m tb z),
    StackChart.stackPullbackCompIso_naturality_assoc, reassoc_of% h1,
    C.objIsoOfEq_inv_eq_symm_hom]
  simp

end FibrePoint

/-! ## Natural equivalences of fibre points and transfer of presentations -/

section FibrePointEquiv

/-- A **natural equivalence of fibre points** between a chart `C` of `Z` over `z` and a chart `D`
of `W` over `w`, both objects lying over the same scheme `T`: fibrewise mutually inverse maps
over every test map `tb : S ⟶ T`, compatible with pullback along test maps.  Such an
equivalence identifies the functors of points of `C.scheme ×_Z T` and `D.scheme ×_W T` over
`T`, so it transfers scheme presentations between them (`PullbackPresentation.transfer`). -/
structure FibrePointEquiv {Z W : FppfStack.{u}} (C : StackChart Z) {T : Scheme.{u}}
    (z : StackFiber Z T) (D : StackChart W) (w : StackFiber W T) where
  /-- The forward map over a test map. -/
  toFun : ∀ {S : Scheme.{u}} (tb : S ⟶ T), C.FibrePoint z tb → D.FibrePoint w tb
  /-- The inverse map over a test map. -/
  invFun : ∀ {S : Scheme.{u}} (tb : S ⟶ T), D.FibrePoint w tb → C.FibrePoint z tb
  /-- The inverse map is a left inverse. -/
  left_inv : ∀ {S : Scheme.{u}} (tb : S ⟶ T) (P : C.FibrePoint z tb), invFun tb (toFun tb P) = P
  /-- The inverse map is a right inverse. -/
  right_inv : ∀ {S : Scheme.{u}} (tb : S ⟶ T) (Q : D.FibrePoint w tb), toFun tb (invFun tb Q) = Q
  /-- The forward map commutes with pullback along test maps. -/
  natural : ∀ {S S' : Scheme.{u}} (m : S' ⟶ S) (tb : S ⟶ T) (P : C.FibrePoint z tb),
    toFun (m ≫ tb) (C.pullbackPoint z m P) = D.pullbackPoint w m (toFun tb P)

namespace FibrePointEquiv

variable {Z W V : FppfStack.{u}} {C : StackChart Z} {T : Scheme.{u}} {z : StackFiber Z T}
  {D : StackChart W} {w : StackFiber W T} (e : C.FibrePointEquiv z D w)

/-- The forward map commutes with transport along base equalities. -/
theorem toFun_castPoint {S : Scheme.{u}} {tb tb' : S ⟶ T} (h : tb = tb')
    (P : C.FibrePoint z tb) :
    e.toFun tb' (C.castPoint z h P) = D.castPoint w h (e.toFun tb P) := by
  subst h
  simp

/-- The inverse map commutes with transport along base equalities. -/
theorem invFun_castPoint {S : Scheme.{u}} {tb tb' : S ⟶ T} (h : tb = tb')
    (Q : D.FibrePoint w tb) :
    e.invFun tb' (D.castPoint w h Q) = C.castPoint z h (e.invFun tb Q) := by
  subst h
  simp

/-- The inverse map is natural as well. -/
theorem invFun_natural {S S' : Scheme.{u}} (m : S' ⟶ S) (tb : S ⟶ T) (Q : D.FibrePoint w tb) :
    e.invFun (m ≫ tb) (D.pullbackPoint w m Q) = C.pullbackPoint z m (e.invFun tb Q) := by
  conv_lhs => rw [← e.right_inv tb Q, ← e.natural m tb (e.invFun tb Q)]
  exact e.left_inv _ _

/-- The inverse natural equivalence. -/
@[simps]
def symm : D.FibrePointEquiv w C z where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
  natural := e.invFun_natural

/-- Composition of natural equivalences of fibre points. -/
@[simps]
def trans {E : StackChart V} {v : StackFiber V T} (e' : D.FibrePointEquiv w E v) :
    C.FibrePointEquiv z E v where
  toFun tb P := e'.toFun tb (e.toFun tb P)
  invFun tb Q := e.invFun tb (e'.invFun tb Q)
  left_inv tb P := by simp [e.left_inv, e'.left_inv]
  right_inv tb Q := by simp [e.right_inv, e'.right_inv]
  natural m tb P := by rw [e.natural, e'.natural]

end FibrePointEquiv

section IsoPointEquiv

variable {Z : FppfStack.{u}} (C : StackChart Z) {T : Scheme.{u}} {z z' : StackFiber Z T}
  (κ : z ≅ z')

/-- Forward map of `isoPointEquiv`. -/
noncomputable def isoPointToFun {S : Scheme.{u}} (tb : S ⟶ T) (P : C.FibrePoint z tb) :
    C.FibrePoint z' tb :=
  ⟨P.1, P.2 ≪≫ (stackPullback Z tb).mapIso κ⟩

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of `isoPointToFun`. -/
theorem isoPointToFun_natural {S S' : Scheme.{u}} (m : S' ⟶ S) (tb : S ⟶ T)
    (P : C.FibrePoint z tb) :
    C.isoPointToFun κ (m ≫ tb) (C.pullbackPoint z m P) =
      C.pullbackPoint z' m (C.isoPointToFun κ tb P) := by
  obtain ⟨a, i⟩ := P
  refine fibrePoint_ext_iff.2 ⟨rfl, ?_⟩
  apply Iso.ext
  simp only [isoPointToFun, pullbackPoint, inducedComparison_eq, Iso.trans_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc, objIsoOfEq_self', Iso.refl_symm,
    Iso.refl_trans]
  rw [StackChart.stackPullbackCompIso_naturality]

/-- **Transport of fibre points along an isomorphism of objects** `κ : z ≅ z'`. -/
noncomputable def isoPointEquiv : C.FibrePointEquiv z C z' where
  toFun := C.isoPointToFun κ
  invFun := C.isoPointToFun κ.symm
  left_inv tb P := by
    obtain ⟨a, i⟩ := P
    simp only [isoPointToFun]
    congr 1
    apply Iso.ext
    simp
  right_inv tb P := by
    obtain ⟨a, i⟩ := P
    simp only [isoPointToFun]
    congr 1
    apply Iso.ext
    simp
  natural := C.isoPointToFun_natural κ

/-- The forward map of `isoPointEquiv`. -/
@[simp]
theorem isoPointEquiv_toFun {S : Scheme.{u}} (tb : S ⟶ T) (P : C.FibrePoint z tb) :
    (C.isoPointEquiv κ).toFun tb P = ⟨P.1, P.2 ≪≫ (stackPullback Z tb).mapIso κ⟩ := rfl

end IsoPointEquiv

namespace PullbackPresentation

variable {Z W : FppfStack.{u}} {C : StackChart Z} {T : Scheme.{u}} {z : StackFiber Z T}
  {D : StackChart W} {w : StackFiber W T}

/-- The lift used by `transfer` classifies the given fibre point. -/
theorem transfer_classifies (e : C.FibrePointEquiv z D w) (R : D.PullbackPresentation T w)
    {S : Scheme.{u}} (tb : S ⟶ T) (tc : S ⟶ C.scheme)
    (c : C.obj S tc ≅ (stackPullback Z tb).obj z) :
    C.Classifies R.fst (e.invFun R.fst ⟨R.snd, R.comparison⟩).1
      (e.invFun R.fst ⟨R.snd, R.comparison⟩).2 tb tc c
      (R.lift tb (e.toFun tb ⟨tc, c⟩).1 (e.toFun tb ⟨tc, c⟩).2) := by
  obtain ⟨h, hR⟩ := (D.classifies_iff_pullbackPoint _ _ _ _ _ _ _).1
    (R.lift_compatible tb (e.toFun tb ⟨tc, c⟩).1 (e.toFun tb ⟨tc, c⟩).2)
  refine (C.classifies_iff_pullbackPoint _ _ _ _ _ _ _).2 ⟨h, ?_⟩
  change C.castPoint z h (C.pullbackPoint z _ (e.invFun R.fst ⟨R.snd, R.comparison⟩)) = _
  rw [← e.invFun_natural, ← e.invFun_castPoint, hR, e.left_inv]

/-- A map whose pulled-back transferred universal point is the given one is the lift. -/
theorem transfer_lift_unique (e : C.FibrePointEquiv z D w) (R : D.PullbackPresentation T w)
    {S : Scheme.{u}} (tb : S ⟶ T) (tc : S ⟶ C.scheme)
    (c : C.obj S tc ≅ (stackPullback Z tb).obj z) (m : S ⟶ R.space)
    (hm : C.Classifies R.fst (e.invFun R.fst ⟨R.snd, R.comparison⟩).1
      (e.invFun R.fst ⟨R.snd, R.comparison⟩).2 tb tc c m) :
    m = R.lift tb (e.toFun tb ⟨tc, c⟩).1 (e.toFun tb ⟨tc, c⟩).2 := by
  obtain ⟨h, hC⟩ := (C.classifies_iff_pullbackPoint _ _ _ _ _ _ _).1 hm
  refine R.lift_unique _ _ _ m ((D.classifies_iff_pullbackPoint _ _ _ _ _ _ _).2 ⟨h, ?_⟩)
  change _ = e.toFun tb ⟨tc, c⟩
  rw [← hC, e.toFun_castPoint]
  change _ = D.castPoint w h
    (e.toFun _ (C.pullbackPoint z m (e.invFun R.fst ⟨R.snd, R.comparison⟩)))
  rw [e.natural, e.right_inv]

/-- **Transfer of a presentation along a natural equivalence of fibre points.**  A scheme
presentation of `D.scheme ×_W T` (over `w`) is also a presentation of `C.scheme ×_Z T` (over
`z`), with the same scheme and the same projection to `T`. -/
noncomputable def transfer (e : C.FibrePointEquiv z D w) (R : D.PullbackPresentation T w) :
    C.PullbackPresentation T z where
  space := R.space
  fst := R.fst
  snd := (e.invFun R.fst ⟨R.snd, R.comparison⟩).1
  comparison := (e.invFun R.fst ⟨R.snd, R.comparison⟩).2
  lift tb tc c := R.lift tb (e.toFun tb ⟨tc, c⟩).1 (e.toFun tb ⟨tc, c⟩).2
  lift_fst tb tc c := R.lift_fst _ _ _
  lift_snd tb tc c := by
    obtain ⟨_, h, _⟩ := transfer_classifies e R tb tc c
    exact h
  lift_compatible tb tc c := transfer_classifies e R tb tc c
  lift_unique tb tc c m h := transfer_lift_unique e R tb tc c m h

end PullbackPresentation

end FibrePointEquiv

/-! ## A cartesian-square criterion for maps between presentations -/

section Cartesian

variable {Z : FppfStack.{u}} {C : StackChart Z} {T : Scheme.{u}} {z : StackFiber Z T}

/-- Moving a transport to the other side of an equation of fibre points. -/
theorem castPoint_eq_iff {S : Scheme.{u}} {tb tb' : S ⟶ T} (h : tb = tb')
    (P : C.FibrePoint z tb) (Q : C.FibrePoint z tb') :
    C.castPoint z h P = Q ↔ P = C.castPoint z h.symm Q := by
  subst h
  simp

/-- Pullback of fibre points commutes with transport along base equalities. -/
theorem pullbackPoint_castPoint {S S' : Scheme.{u}} (m : S' ⟶ S) {tb tb' : S ⟶ T}
    (h : tb = tb') (P : C.FibrePoint z tb) :
    C.pullbackPoint z m (C.castPoint z h P) =
      C.castPoint z (congrArg (m ≫ ·) h) (C.pullbackPoint z m P) := by
  subst h
  simp

/-- Transport along any self-equality is the identity. -/
@[simp]
theorem castPoint_self {S : Scheme.{u}} {tb : S ⟶ T} (h : tb = tb) (P : C.FibrePoint z tb) :
    C.castPoint z h P = P := by
  rw [Subsingleton.elim h rfl, castPoint_rfl]

/-- Pulling back along equal maps gives the same fibre point, up to transport. -/
theorem pullbackPoint_congr {S S' : Scheme.{u}} {m m' : S' ⟶ S} (h : m = m') {tb : S ⟶ T}
    (P : C.FibrePoint z tb) :
    C.castPoint z (congrArg (· ≫ tb) h) (C.pullbackPoint z m P) = C.pullbackPoint z m' P := by
  subst h
  simp

namespace PullbackPresentation

/-- The universal fibre point of a presentation. -/
abbrev univPoint (R : C.PullbackPresentation T z) : C.FibrePoint z R.fst :=
  ⟨R.snd, R.comparison⟩

/-- The lift of a presentation pulls the universal fibre point back to the given one. -/
theorem pullbackPoint_lift (R : C.PullbackPresentation T z) {S : Scheme.{u}} (tb : S ⟶ T)
    (tc : S ⟶ C.scheme) (c : C.obj S tc ≅ (stackPullback Z tb).obj z) :
    C.castPoint z (R.lift_fst tb tc c) (C.pullbackPoint z (R.lift tb tc c) R.univPoint) =
      ⟨tc, c⟩ := by
  obtain ⟨h, hp⟩ := (C.classifies_iff_pullbackPoint _ _ _ _ _ _ _).1 (R.lift_compatible tb tc c)
  exact hp

/-- The lift of a presentation pulls the universal fibre point back to the given one (solved
form). -/
theorem pullbackPoint_lift' (R : C.PullbackPresentation T z) {S : Scheme.{u}} (tb : S ⟶ T)
    (P : C.FibrePoint z tb) :
    C.pullbackPoint z (R.lift tb P.1 P.2) R.univPoint =
      C.castPoint z (R.lift_fst tb P.1 P.2).symm P := by
  have h := R.pullbackPoint_lift tb P.1 P.2
  rw [Sigma.eta] at h
  exact (castPoint_eq_iff _ _ _).1 h

/-- Maps into a presentation are determined by the pulled-back universal fibre points. -/
theorem eq_of_pullbackPoint (R : C.PullbackPresentation T z) {S : Scheme.{u}}
    {u₁ u₂ : S ⟶ R.space} (h : u₁ ≫ R.fst = u₂ ≫ R.fst)
    (hp : C.castPoint z h (C.pullbackPoint z u₁ R.univPoint) =
      C.pullbackPoint z u₂ R.univPoint) : u₁ = u₂ := by
  have k₂ : u₂ = R.lift (u₂ ≫ R.fst) (C.pullbackPoint z u₂ R.univPoint).1
      (C.pullbackPoint z u₂ R.univPoint).2 :=
    R.lift_unique _ _ _ _ ((C.classifies_iff_pullbackPoint _ _ _ _ _ _ _).2 ⟨rfl, by simp⟩)
  have k₁ : u₁ = R.lift (u₂ ≫ R.fst) (C.pullbackPoint z u₂ R.univPoint).1
      (C.pullbackPoint z u₂ R.univPoint).2 :=
    R.lift_unique _ _ _ _ ((C.classifies_iff_pullbackPoint _ _ _ _ _ _ _).2 ⟨h, hp⟩)
  exact k₁.trans k₂.symm

end PullbackPresentation

variable {W : FppfStack.{u}} {D : StackChart W} {T' : Scheme.{u}} (π : T ⟶ T')
  (z' : StackFiber W T')

/-- A fibre point over the pullback object `π^* z'` and `tb` is a fibre point over `z'` and
`tb ≫ π`. -/
noncomputable def overPoint {S : Scheme.{u}} {tb : S ⟶ T}
    (Q : D.FibrePoint ((stackPullback W π).obj z') tb) : D.FibrePoint z' (tb ≫ π) :=
  ⟨Q.1, Q.2 ≪≫ stackPullbackCompIso W tb π z'⟩

/-- Inverse of `overPoint`. -/
noncomputable def underPoint {S : Scheme.{u}} {tb : S ⟶ T} (Q : D.FibrePoint z' (tb ≫ π)) :
    D.FibrePoint ((stackPullback W π).obj z') tb :=
  ⟨Q.1, Q.2 ≪≫ (stackPullbackCompIso W tb π z').symm⟩

variable {π z'}

/-- `underPoint` is a right inverse of `overPoint`. -/
@[simp]
theorem overPoint_underPoint {S : Scheme.{u}} {tb : S ⟶ T} (Q : D.FibrePoint z' (tb ≫ π)) :
    overPoint π z' (underPoint π z' Q) = Q := by
  obtain ⟨a, i⟩ := Q
  simp [overPoint, underPoint]

/-- `underPoint` is a left inverse of `overPoint`. -/
@[simp]
theorem underPoint_overPoint {S : Scheme.{u}} {tb : S ⟶ T}
    (Q : D.FibrePoint ((stackPullback W π).obj z') tb) :
    underPoint π z' (overPoint π z' Q) = Q := by
  obtain ⟨a, i⟩ := Q
  simp [overPoint, underPoint]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of `overPoint`. -/
theorem overPoint_pullbackPoint {S S' : Scheme.{u}} (m : S' ⟶ S) {tb : S ⟶ T}
    (Q : D.FibrePoint ((stackPullback W π).obj z') tb) :
    overPoint π z' (D.pullbackPoint _ m Q) =
      D.castPoint z' (Category.assoc m tb π).symm (D.pullbackPoint z' m (overPoint π z' Q)) := by
  obtain ⟨a, i⟩ := Q
  refine fibrePoint_ext_iff.2 ⟨rfl, ?_⟩
  apply Iso.ext
  simp only [overPoint, pullbackPoint, inducedComparison_eq, Iso.trans_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc, objIsoOfEq_self', Iso.refl_symm,
    Iso.refl_trans]
  rw [reassoc_of% (stackPullbackCompIso_assoc W m tb π z')]
  simp

/-- `overPoint` commutes with transport along base equalities. -/
theorem overPoint_castPoint {S : Scheme.{u}} {tb tb' : S ⟶ T} (h : tb = tb')
    (Q : D.FibrePoint ((stackPullback W π).obj z') tb) :
    overPoint π z' (D.castPoint _ h Q) =
      D.castPoint z' (congrArg (· ≫ π) h) (overPoint π z' Q) := by
  subst h
  simp

/-- `underPoint` commutes with transport along base equalities. -/
theorem underPoint_castPoint {S : Scheme.{u}} {tb tb' : S ⟶ T} (h : tb = tb')
    (Q : D.FibrePoint z' (tb ≫ π)) :
    underPoint π z' (D.castPoint z' (congrArg (· ≫ π) h) Q) =
      D.castPoint _ h (underPoint π z' Q) := by
  subst h
  simp

variable (π z') in
/-- `overPoint` applied to a pulled-back fibre point, solved for the pullback. -/
theorem pullbackPoint_overPoint {S S' : Scheme.{u}} (m : S' ⟶ S) {tb : S ⟶ T}
    (Q : D.FibrePoint ((stackPullback W π).obj z') tb) :
    D.pullbackPoint z' m (overPoint π z' Q) =
      D.castPoint z' (Category.assoc m tb π) (overPoint π z' (D.pullbackPoint _ m Q)) := by
  rw [overPoint_pullbackPoint]
  simp

variable (e : C.FibrePointEquiv z D ((stackPullback W π).obj z'))
  (R : C.PullbackPresentation T z) (R' : D.PullbackPresentation T' z')

/-- **The map of presentations induced by a natural equivalence of fibre points over `π`**:
the classifying map into `R'` of the image of the universal fibre point of `R`. -/
noncomputable def presentationMap : R.space ⟶ R'.space :=
  R'.lift (R.fst ≫ π) (overPoint π z' (e.toFun R.fst R.univPoint)).1
    (overPoint π z' (e.toFun R.fst R.univPoint)).2

/-- The induced map of presentations lies over `π` on the first projections. -/
theorem presentationMap_fst : presentationMap e R R' ≫ R'.fst = R.fst ≫ π :=
  R'.lift_fst _ _ _

/-- The second projection of the induced map of presentations. -/
theorem presentationMap_snd :
    presentationMap e R R' ≫ R'.snd = (e.toFun R.fst R.univPoint).1 :=
  R'.lift_snd _ _ _

/-- The pulled-back universal fibre point of `R'` along `l ≫ presentationMap` is the image of the
pulled-back universal fibre point of `R` along `l`. -/
theorem pullbackPoint_presentationMap {S : Scheme.{u}} (l : S ⟶ R.space) :
    D.castPoint z' (by rw [Category.assoc, presentationMap_fst, Category.assoc])
        (D.pullbackPoint z' (l ≫ presentationMap e R R') R'.univPoint) =
      overPoint π z' (e.toFun (l ≫ R.fst) (C.pullbackPoint z l R.univPoint)) := by
  have hM := R'.pullbackPoint_lift (R.fst ≫ π) (overPoint π z' (e.toFun R.fst R.univPoint)).1
    (overPoint π z' (e.toFun R.fst R.univPoint)).2
  have hM' : D.pullbackPoint z' (presentationMap e R R') R'.univPoint =
      D.castPoint z' (presentationMap_fst e R R').symm
        (overPoint π z' (e.toFun R.fst R.univPoint)) := by
    rw [Sigma.eta] at hM
    rw [← hM, castPoint_castPoint]
    exact (castPoint_self _ _).symm
  rw [pullbackPoint_comp, hM', pullbackPoint_castPoint, pullbackPoint_overPoint, ← e.natural]
  simp only [castPoint_castPoint, castPoint_self]

/-- The fibre point over `s.snd` classified by `isPullback_presentationMap`'s lift. -/
noncomputable def presentationMapLiftPoint {S : Scheme.{u}} (u : S ⟶ R'.space) (v : S ⟶ T)
    (h : u ≫ R'.fst = v ≫ π) : C.FibrePoint z v :=
  e.invFun v (underPoint π z' (D.castPoint z' h (D.pullbackPoint z' u R'.univPoint)))

/-- The image of the lifted fibre point is the transported pulled-back universal point. -/
theorem toFun_presentationMapLiftPoint {S : Scheme.{u}} (u : S ⟶ R'.space) (v : S ⟶ T)
    (h : u ≫ R'.fst = v ≫ π) :
    e.toFun v (presentationMapLiftPoint e R' u v h) =
      underPoint π z' (D.castPoint z' h (D.pullbackPoint z' u R'.univPoint)) :=
  e.right_inv _ _

/-- **The induced map of presentations is a base change.**  If `e` identifies fibre points of `C`
over `z` with fibre points of `D` over `π^* z'`, then the square formed by `presentationMap e R R'`,
the projections `R.fst`, `R'.fst` and `π` is cartesian. -/
theorem isPullback_presentationMap : IsPullback (presentationMap e R R') R.fst R'.fst π := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (presentationMap_fst e R R')
    (fun s ↦ R.lift s.snd (presentationMapLiftPoint e R' s.fst s.snd s.condition).1
      (presentationMapLiftPoint e R' s.fst s.snd s.condition).2) ?_ ?_ ?_)
  · intro s
    have hw : (R.lift s.snd (presentationMapLiftPoint e R' s.fst s.snd s.condition).1
        (presentationMapLiftPoint e R' s.fst s.snd s.condition).2 ≫ presentationMap e R R') ≫
          R'.fst = s.fst ≫ R'.fst := by
      rw [Category.assoc, presentationMap_fst, ← Category.assoc, R.lift_fst, s.condition]
    refine R'.eq_of_pullbackPoint hw ?_
    have k1 := pullbackPoint_presentationMap e R R'
      (R.lift s.snd (presentationMapLiftPoint e R' s.fst s.snd s.condition).1
        (presentationMapLiftPoint e R' s.fst s.snd s.condition).2)
    rw [R.pullbackPoint_lift', e.toFun_castPoint, toFun_presentationMapLiftPoint,
      overPoint_castPoint, overPoint_underPoint, castPoint_castPoint, castPoint_eq_iff,
      castPoint_castPoint] at k1
    rw [castPoint_eq_iff, k1]
  · intro s
    exact R.lift_fst _ _ _
  · intro s m hfst hsnd
    refine R.lift_unique _ _ _ m ((C.classifies_iff_pullbackPoint _ _ _ _ _ _ _).2 ⟨hsnd, ?_⟩)
    rw [Sigma.eta]
    have key : e.toFun s.snd (C.castPoint z hsnd (C.pullbackPoint z m R.univPoint)) =
        e.toFun s.snd (presentationMapLiftPoint e R' s.fst s.snd s.condition) := by
      have k1 := pullbackPoint_presentationMap e R R' m
      have k2 := pullbackPoint_congr (z := z') (C := D) hfst R'.univPoint
      rw [castPoint_eq_iff] at k2
      rw [k2, castPoint_castPoint] at k1
      have k3 : e.toFun (m ≫ R.fst) (C.pullbackPoint z m R.univPoint) =
          underPoint π z' (D.castPoint z' (by rw [← hfst, Category.assoc, presentationMap_fst,
            Category.assoc]) (D.pullbackPoint z' s.fst R'.univPoint)) := by
        rw [k1, underPoint_overPoint]
      rw [toFun_presentationMapLiftPoint, e.toFun_castPoint, k3, ← underPoint_castPoint,
        castPoint_castPoint]
    simpa [e.left_inv] using congrArg (e.invFun s.snd) key

end Cartesian

end StackChart

/-! ## The base-change chart of a presentation -/

namespace StackHom

section BaseChange

variable {X Y : FppfStack.{u}} (f : StackHom X Y) (B : StackChart Y)

/-- The pseudonaturality isomorphism of a stack morphism `f` at an object `x` and a map `g`:
`f (g^* x) ≅ g^* (f x)`. -/
private noncomputable abbrev pullbackComparison {S T : Scheme.{u}} (g : S ⟶ T)
    (x : StackFiber X T) :
    (f.appFunctor S).obj ((stackPullback X g).obj x) ≅
      (stackPullback Y g).obj ((f.appFunctor T).obj x) :=
  (Cat.Hom.toNatIso (f.naturality ⟨g.op⟩)).app x

variable {f B} (p : StackMorphismPresentation f B.scheme B.tautObj)

/-- **The base change of a chart along a stack morphism, attached to a presentation.**  For a
presentation `p` of `B.scheme ×_Y X` (the base change of `f` along the tautological object of
the chart `B`), the chart of `X` with scheme `p.space` classifying the universal object
`p.object`. -/
noncomputable def chartOfPresentation : StackChart X := StackChart.ofObject p.object

/-- The scheme of the base-change chart is the presenting scheme. -/
@[simp]
theorem chartOfPresentation_scheme : (chartOfPresentation p).scheme = p.space := rfl

/-- The comparison `f (a^* p.object) ≅ (a ≫ p.map)^* B.tautObj` attached to a map
`a : S ⟶ p.space` and an isomorphism of an object with `a^* p.object`. -/
private noncomputable abbrev basePresentationComparison {S : Scheme.{u}} (a : S ⟶ p.space)
    (x' : StackFiber X S) (ι : x' ≅ (stackPullback X a).obj p.object) :
    (f.appFunctor S).obj x' ≅ (stackPullback Y (a ≫ p.map)).obj B.tautObj :=
  stackMorphismInducedComparison f p.map p.object B.tautObj p.comparison a x' ι

variable {T : Scheme.{u}} (x : StackFiber X T)

/-- Forward map of `baseChangePointEquiv`. -/
noncomputable def baseChangePointToFun {S : Scheme.{u}} (tb : S ⟶ T)
    (P : (chartOfPresentation p).FibrePoint x tb) : B.FibrePoint ((f.appFunctor T).obj x) tb :=
  ⟨P.1 ≫ p.map, B.identityObjectPullbackComparison (P.1 ≫ p.map) ≪≫
    (basePresentationComparison p P.1 _ P.2.symm).symm ≪≫ f.pullbackComparison tb x⟩

/-- Inverse map of `baseChangePointEquiv`. -/
noncomputable def baseChangePointInvFun {S : Scheme.{u}} (tb : S ⟶ T)
    (Q : B.FibrePoint ((f.appFunctor T).obj x) tb) : (chartOfPresentation p).FibrePoint x tb :=
  ⟨p.lift Q.1 ((stackPullback X tb).obj x)
      (f.pullbackComparison tb x ≪≫ Q.2.symm ≪≫ B.identityObjectPullbackComparison Q.1),
    (p.liftObjectIso Q.1 ((stackPullback X tb).obj x)
      (f.pullbackComparison tb x ≪≫ Q.2.symm ≪≫ B.identityObjectPullbackComparison Q.1)).symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- `baseChangePointInvFun` is a left inverse of `baseChangePointToFun` (uniqueness in the
universal property of `p`). -/
theorem baseChangePoint_left_inv {S : Scheme.{u}} (tb : S ⟶ T)
    (P : (chartOfPresentation p).FibrePoint x tb) :
    baseChangePointInvFun p x tb (baseChangePointToFun p x tb P) = P := by
  obtain ⟨a, ι⟩ := P
  have hκ : f.pullbackComparison tb x ≪≫ (B.identityObjectPullbackComparison (a ≫ p.map) ≪≫
      (basePresentationComparison p a _ ι.symm).symm ≪≫ f.pullbackComparison tb x).symm ≪≫
      B.identityObjectPullbackComparison (a ≫ p.map) = basePresentationComparison p a _ ι.symm := by
    apply Iso.ext
    simp
  have hcl : StackMorphismClassifies f p.map p.object B.tautObj p.comparison (a ≫ p.map)
      ((stackPullback X tb).obj x) (basePresentationComparison p a _ ι.symm) a ι.symm :=
    ⟨rfl, by simp⟩
  have he : a = p.lift (a ≫ p.map) _ (basePresentationComparison p a _ ι.symm) :=
    p.lift_unique _ _ _ a ι.symm hcl
  have hiso := p.liftObjectIso_unique _ _ _ (ι.symm ≪≫ stackPullbackObjIsoOfEq X he p.object)
    (stackMorphismClassifies_changeMap _ _ hcl he rfl)
  simp only [baseChangePointInvFun, baseChangePointToFun]
  rw [hκ, ← hiso]
  refine (StackChart.fibrePoint_ext_iff (C := chartOfPresentation p) (z := x)).2 ⟨he.symm, ?_⟩
  clear hiso hκ
  generalize p.lift (a ≫ p.map) _ (basePresentationComparison p a _ ι.symm) = l at he ⊢
  subst he
  apply Iso.ext
  simp only [StackChart.objIsoOfEq_self', stackPullbackObjIsoOfEq_self, Iso.refl_symm,
    Iso.refl_trans]
  exact Category.id_comp ι.hom

set_option backward.isDefEq.respectTransparency false in
/-- `baseChangePointInvFun` is a right inverse of `baseChangePointToFun` (compatibility in
the universal property of `p`). -/
theorem baseChangePoint_right_inv {S : Scheme.{u}} (tb : S ⟶ T)
    (Q : B.FibrePoint ((f.appFunctor T).obj x) tb) :
    baseChangePointToFun p x tb (baseChangePointInvFun p x tb Q) = Q := by
  obtain ⟨b, ι'⟩ := Q
  simp only [baseChangePointToFun, baseChangePointInvFun, Iso.symm_symm_eq]
  set κ := f.pullbackComparison tb x ≪≫ ι'.symm ≪≫ B.identityObjectPullbackComparison b
    with hκ
  obtain ⟨e, hc⟩ := p.lift_compatible b ((stackPullback X tb).obj x) κ
  have hc' : (basePresentationComparison p (p.lift b _ κ) _
      (p.liftObjectIso b ((stackPullback X tb).obj x) κ)).inv =
      (stackPullbackObjIsoOfEq Y e B.tautObj).hom ≫ κ.inv := by
    have h2 := congrArg Iso.inv hc
    simp only [Iso.trans_inv] at h2
    rw [← h2]
    simp
  have hcongr := congrArg Iso.hom (B.identityObjectPullbackComparison_congr e)
  simp only [Iso.trans_hom, Iso.symm_hom] at hcongr
  refine (StackChart.fibrePoint_ext_iff (C := B) (z := (f.appFunctor T).obj x)).2 ⟨e, ?_⟩
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [hc']
  simp only [Category.assoc]
  rw [reassoc_of% hcongr]
  simp [κ]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of `baseChangePointToFun` under pullback of fibre points. -/
theorem baseChangePoint_natural {S S' : Scheme.{u}} (m : S' ⟶ S) (tb : S ⟶ T)
    (P : (chartOfPresentation p).FibrePoint x tb) :
    baseChangePointToFun p x (m ≫ tb) ((chartOfPresentation p).pullbackPoint x m P) =
      B.pullbackPoint ((f.appFunctor T).obj x) m (baseChangePointToFun p x tb P) := by
  obtain ⟨a, ι⟩ := P
  have h1 : ((chartOfPresentation p).inducedComparison tb a ι m).symm =
      (stackPullbackCompIso X m tb x).symm ≪≫ ((stackPullback X m).mapIso ι.symm ≪≫
        stackPullbackCompIso X m a p.object) := by
    apply Iso.ext
    simp [StackChart.inducedComparison_eq, chartOfPresentation,
      StackChart.ofObject_objPullbackIso]
  have I2 := stackMorphismInducedComparison_comp f p.map p.object B.tautObj p.comparison a
    ((stackPullback X tb).obj x) ι.symm m ((stackPullback X (m ≫ tb)).obj x)
    (stackPullbackCompIso X m tb x).symm
  have I3 := stackHomNaturalityCompPullback f m tb x
  have I4 := congrArg Iso.hom (B.inducedComparison_identityObjectPullbackComparison (a ≫ p.map) m)
  have I5 := congrArg Iso.hom (B.identityObjectPullbackComparison_congr (Category.assoc m a p.map))
  simp only [StackChart.inducedComparison_eq, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc] at I4
  simp only [Iso.trans_hom, Iso.symm_hom] at I5
  simp only [baseChangePointToFun, StackChart.pullbackPoint]
  rw [h1]
  refine (StackChart.fibrePoint_ext_iff (C := B) (z := (f.appFunctor T).obj x)).2
    ⟨Category.assoc m a p.map, ?_⟩
  apply Iso.ext
  have I2' := congrArg Iso.inv I2
  simp only [Iso.trans_inv] at I2'
  have I6 := (Iso.inv_comp_eq _).1 I2'.symm
  simp only [Iso.trans_hom, Iso.symm_hom, StackChart.inducedComparison_eq, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [I6]
  simp only [stackMorphismInducedComparison, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv,
    Category.assoc, Iso.app_inv, Iso.app_hom]
  have I3' : (f.appFunctor S').map (stackPullbackCompIso X m tb x).hom ≫
      (Cat.Hom.toNatIso (f.naturality ⟨(m ≫ tb).op⟩)).hom.app x =
      (Cat.Hom.toNatIso (f.naturality ⟨m.op⟩)).hom.app ((stackPullback X tb).obj x) ≫
        (stackPullback Y m).map ((Cat.Hom.toNatIso (f.naturality ⟨tb.op⟩)).hom.app x) ≫
          (stackPullbackCompIso Y m tb ((f.appFunctor T).obj x)).hom := I3
  rw [reassoc_of% I5, I3', Iso.inv_hom_id_app_assoc, ← I4]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- **Fibre points of the base-change chart are fibre points of `B` over the image object.**
For `x` over `T`, a fibre point of `chartOfPresentation p` over `x` (a map to `p.space` with an
identification of the pulled-back universal object with `x`) is the same as a fibre point of
`B` over `f x`, naturally in the test scheme: this is the pasting law
`T ×_X (X ×_Y B.scheme) ≅ T ×_Y B.scheme`. -/
noncomputable def baseChangePointEquiv :
    (chartOfPresentation p).FibrePointEquiv x B ((f.appFunctor T).obj x) where
  toFun := baseChangePointToFun p x
  invFun := baseChangePointInvFun p x
  left_inv := baseChangePoint_left_inv p x
  right_inv := baseChangePoint_right_inv p x
  natural := baseChangePoint_natural p x

/-! ### The self-overlap of the base-change chart -/

/-- The comparison `f (tautological object of the base-change chart) ≅ p.map^* B.tautObj`. -/
private noncomputable def tautComparison :
    (f.appFunctor p.space).obj (chartOfPresentation p).tautObj ≅
      (stackPullback Y p.map).obj B.tautObj :=
  basePresentationComparison p (𝟙 p.space) (chartOfPresentation p).tautObj
      (Iso.refl ((stackPullback X (𝟙 p.space)).obj p.object)) ≪≫
    stackPullbackObjIsoOfEq Y (Category.id_comp p.map) B.tautObj

/-- Fibre points of the base-change chart over its tautological object are fibre points of `B`
over the pullback of its tautological object along `p.map`. -/
noncomputable def selfPointEquiv :
    (chartOfPresentation p).FibrePointEquiv (chartOfPresentation p).tautObj B
      ((stackPullback Y p.map).obj B.tautObj) :=
  (baseChangePointEquiv p (chartOfPresentation p).tautObj).trans
    (B.isoPointEquiv (tautComparison p))

/-- The canonical comparison `f (a^* p.object) ≅ (a ≫ p.map)^* B.tautObj`. -/
private noncomputable abbrev canonicalComparison {S : Scheme.{u}} (a : S ⟶ p.space) :
    (f.appFunctor S).obj ((chartOfPresentation p).obj S a) ≅
      (stackPullback Y (a ≫ p.map)).obj B.tautObj :=
  basePresentationComparison p a ((chartOfPresentation p).obj S a)
    (Iso.refl ((stackPullback X a).obj p.object))

set_option backward.isDefEq.respectTransparency false in
/-- The induced comparison of a morphism presentation factors through the source-object
isomorphism. -/
theorem stackMorphismInducedComparison_eq_mapIso {U T' : Scheme.{u}} (map : U ⟶ T')
    (object : StackFiber X U)
    (y : StackFiber Y T')
    (universal : (f.appFunctor U).obj object ≅ (stackPullback Y map).obj y) {S : Scheme.{u}}
    (g : S ⟶ U) (x' : StackFiber X S) (e : x' ≅ (stackPullback X g).obj object) :
    stackMorphismInducedComparison f map object y universal g x' e =
      (f.appFunctor S).mapIso e ≪≫
        stackMorphismInducedComparison f map object y universal g _ (Iso.refl _) := by
  apply Iso.ext
  simp only [stackMorphismInducedComparison, Iso.trans_hom, Functor.mapIso_hom, Iso.refl_hom,
    Category.assoc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The induced comparison along the identity source isomorphism. -/
theorem stackMorphismInducedComparison_refl_eq {U T' : Scheme.{u}} (map : U ⟶ T')
    (object : StackFiber X U)
    (y : StackFiber Y T')
    (universal : (f.appFunctor U).obj object ≅ (stackPullback Y map).obj y) {S : Scheme.{u}}
    (g : S ⟶ U) :
    stackMorphismInducedComparison f map object y universal g _ (Iso.refl _) =
      (Cat.Hom.toNatIso (f.naturality ⟨g.op⟩)).app object ≪≫
        (stackPullback Y g).mapIso universal ≪≫
        stackPullbackCompIso Y g map y := by
  apply Iso.ext
  simp only [stackMorphismInducedComparison, Iso.trans_hom, Functor.mapIso_hom, Iso.refl_hom,
    Category.assoc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- `basePresentationComparison` factors through the canonical comparison. -/
private theorem basePresentationComparison_eq {S : Scheme.{u}} (a : S ⟶ p.space)
    (x' : StackFiber X S)
    (ι : x' ≅ (stackPullback X a).obj p.object) :
    basePresentationComparison p a x' ι = (f.appFunctor S).mapIso ι ≪≫ canonicalComparison p a := by
  apply Iso.ext
  simp only [stackMorphismInducedComparison, Iso.trans_hom, Functor.mapIso_hom, Iso.refl_hom,
    Category.assoc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The pullback of `tautComparison` along `a`, corrected by the compositors, is the
canonical comparison at `a`, up to the identification of the chart object with the
pulled-back tautological object. -/
private theorem pullbackComparison_tautComparison {S : Scheme.{u}} (a : S ⟶ p.space) :
    f.pullbackComparison a (chartOfPresentation p).tautObj ≪≫
        (stackPullback Y a).mapIso (tautComparison p) ≪≫
          stackPullbackCompIso Y a p.map B.tautObj =
      (f.appFunctor S).mapIso
          ((chartOfPresentation p).identityObjectPullbackComparison a).symm ≪≫
        canonicalComparison p a := by
  have I := stackMorphismInducedComparison_comp f p.map p.object B.tautObj p.comparison
    (𝟙 p.space) (chartOfPresentation p).tautObj
    (Iso.refl ((stackPullback X (𝟙 p.space)).obj p.object)) a
    ((chartOfPresentation p).obj S a) ((chartOfPresentation p).identityObjectPullbackComparison a)
  have J := stackMorphismInducedComparison_changeMap f p.map p.object B.tautObj p.comparison
    (Category.comp_id a) ((chartOfPresentation p).obj S a)
    (((chartOfPresentation p).identityObjectPullbackComparison a).trans
      (stackPullbackCompIso X a (𝟙 p.space) p.object))
    (Iso.refl ((stackPullback X a).obj p.object)) (by
      apply Iso.ext
      simp only [chartOfPresentation, StackChart.identityObjectPullbackComparison,
        StackChart.objIsoOfEq_self', StackChart.ofObject_objPullbackIso, Iso.refl_trans,
        stackPullbackObjIsoOfEq_self, Iso.trans_refl, Iso.trans_hom, Iso.symm_hom, Iso.refl_hom]
      exact Iso.inv_hom_id _)
  have K := stackPullback_mapIso_objIsoOfEq_compIso a (Category.id_comp p.map) B.tautObj
  have hrefl : (stackPullback X a).mapIso (Iso.refl ((stackPullback X (𝟙 p.space)).obj p.object)) ≪≫
      stackPullbackCompIso X a (𝟙 p.space) p.object =
      stackPullbackCompIso X a (𝟙 p.space) p.object := by
    apply Iso.ext
    erw [Iso.trans_hom, Functor.mapIso_hom, Iso.refl_hom, CategoryTheory.Functor.map_id]
    exact Category.id_comp _
  rw [stackMorphismInducedComparison_eq_mapIso, stackMorphismInducedComparison_refl_eq, hrefl] at I
  rw [canonicalComparison, basePresentationComparison, ← J, tautComparison, Functor.mapIso_trans,
    Iso.trans_assoc, K]
  have I2 := congrArg (fun e ↦ ((f.appFunctor S).mapIso
    ((chartOfPresentation p).identityObjectPullbackComparison a)).symm ≪≫ e) I
  simp only [Iso.symm_self_id_assoc] at I2
  rw [← Iso.trans_assoc, ← Iso.trans_assoc, Iso.trans_assoc _ _ (stackPullbackCompIso _ _ _ _),
    I2]
  apply Iso.ext
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Closed form of the self-overlap fibre-point equivalence. -/
private theorem selfPoint_snd {S : Scheme.{u}} (a₁ a₂ : S ⟶ p.space)
    (ι : (chartOfPresentation p).obj S a₂ ≅
      (stackPullback X a₁).obj (chartOfPresentation p).tautObj) :
    (StackChart.overPoint p.map B.tautObj ((selfPointEquiv p).toFun a₁ ⟨a₂, ι⟩)).2 =
      B.identityObjectPullbackComparison (a₂ ≫ p.map) ≪≫ (canonicalComparison p a₂).symm ≪≫
        (f.appFunctor S).mapIso
          (ι ≪≫ ((chartOfPresentation p).identityObjectPullbackComparison a₁).symm) ≪≫
        canonicalComparison p a₁ := by
  have h := pullbackComparison_tautComparison p a₁
  change ((B.identityObjectPullbackComparison (a₂ ≫ p.map) ≪≫
    (basePresentationComparison p a₂ _ ι.symm).symm ≪≫
      f.pullbackComparison a₁ (chartOfPresentation p).tautObj) ≪≫
        (stackPullback Y a₁).mapIso (tautComparison p)) ≪≫
          stackPullbackCompIso Y a₁ p.map B.tautObj = _
  rw [basePresentationComparison_eq, Iso.trans_assoc, Iso.trans_assoc, Iso.trans_assoc, h]
  apply Iso.ext
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The self-overlap fibre-point equivalence commutes with exchanging the two legs. -/
theorem selfPoint_swap {S : Scheme.{u}} (a₁ a₂ : S ⟶ p.space)
    (ι : (chartOfPresentation p).obj S a₂ ≅
      (stackPullback X a₁).obj (chartOfPresentation p).tautObj) :
    B.selfSwapTestComparison (StackChart.overPoint p.map B.tautObj ((selfPointEquiv p).toFun a₂
        ⟨a₁, (chartOfPresentation p).selfSwapTestComparison ι⟩)).2 =
      (StackChart.overPoint p.map B.tautObj ((selfPointEquiv p).toFun a₁ ⟨a₂, ι⟩)).2 := by
  rw [selfPoint_snd, selfPoint_snd]
  apply Iso.ext
  simp only [chartOfPresentation_scheme, StackChart.selfSwapTestComparison, Iso.trans_assoc,
    Iso.self_symm_id, Iso.trans_refl, Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_symm,
    Iso.symm_symm_eq, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    Iso.cancel_iso_hom_left, Iso.cancel_iso_inv_left]
  erw [Iso.inv_hom_id, Category.comp_id]

section SelfOverlap

variable (hA : (chartOfPresentation p).IsRepresentable) (hB : B.IsRepresentable)

/-- **The map of self-overlaps induced by the base-change chart**: the self-overlap scheme of
`chartOfPresentation p` maps to the self-overlap scheme of `B`, over `p.map` on both legs. -/
noncomputable def selfOverlapMap :
    ((chartOfPresentation p).selfOverlapScheme hA).space ⟶ (B.selfOverlapScheme hB).space :=
  StackChart.presentationMap (selfPointEquiv p) _ _

/-- The map of self-overlaps lies over `p.map` on the first projections. -/
theorem selfOverlapMap_fst :
    selfOverlapMap p hA hB ≫ (B.selfOverlapScheme hB).fst =
      ((chartOfPresentation p).selfOverlapScheme hA).fst ≫ p.map :=
  StackChart.presentationMap_fst _ _ _

/-- The map of self-overlaps lies over `p.map` on the second projections. -/
theorem selfOverlapMap_snd :
    selfOverlapMap p hA hB ≫ (B.selfOverlapScheme hB).snd =
      ((chartOfPresentation p).selfOverlapScheme hA).snd ≫ p.map :=
  StackChart.presentationMap_snd _ _ _

/-- **The source square of self-overlaps is cartesian**: the self-overlap of the base-change
chart is the base change of the self-overlap of `B` along `p.map`, via the first projections. -/
theorem isPullback_selfOverlapMap_fst :
    IsPullback (selfOverlapMap p hA hB) ((chartOfPresentation p).selfOverlapScheme hA).fst
      (B.selfOverlapScheme hB).fst p.map :=
  StackChart.isPullback_presentationMap _ _ _

/-- Exchanging the legs of both self-overlaps does not change the induced map. -/
theorem presentationMap_selfSwap :
    StackChart.presentationMap (selfPointEquiv p)
        ((chartOfPresentation p).selfOverlapScheme hA).selfSwap
        (B.selfOverlapScheme hB).selfSwap = selfOverlapMap p hA hB := by
  change (B.selfOverlapScheme hB).lift _ _ _ = (B.selfOverlapScheme hB).lift _ _ _
  congr 1
  exact selfPoint_swap p _ _ _

/-- **The target square of self-overlaps is cartesian.** -/
theorem isPullback_selfOverlapMap_snd :
    IsPullback (selfOverlapMap p hA hB) ((chartOfPresentation p).selfOverlapScheme hA).snd
      (B.selfOverlapScheme hB).snd p.map := by
  rw [← presentationMap_selfSwap]
  exact StackChart.isPullback_presentationMap _ _ _

end SelfOverlap

/-- **Representable properties of a chart are inherited by its base change.**  If every base
change of the chart `B` of `Y` has a projection with property `P`, the same holds for the
base-change chart `chartOfPresentation p` of `X`: presentations of the two are transferred into
each other along `baseChangePointEquiv`, with the same projection to the test scheme. -/
theorem chartOfPresentation_hasRepresentableProperty (P : MorphismProperty Scheme.{u})
    (hB : B.HasRepresentableProperty P) :
    (chartOfPresentation p).HasRepresentableProperty P := by
  refine ⟨fun T x ↦ ⟨StackChart.PullbackPresentation.transfer (baseChangePointEquiv p x)
    (hB.1 T ((f.appFunctor T).obj x)).some⟩, fun T x R ↦ ?_⟩
  exact hB.2 T ((f.appFunctor T).obj x)
    (StackChart.PullbackPresentation.transfer (baseChangePointEquiv p x).symm R)

/-- The base change of an étale surjective chart is étale surjective. -/
theorem chartOfPresentation_isEtaleSurjective (hB : B.IsEtaleSurjective) :
    (chartOfPresentation p).IsEtaleSurjective :=
  chartOfPresentation_hasRepresentableProperty p _ hB

/-- The projection of a presentation of a morphism with representable property `P` (respecting
isomorphisms) has property `P`. -/
theorem presentation_map_property (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hf : f.HasRepresentableProperty P) : P p.map :=
  property_of_hasRepresentablePropertyRaw P ((hasRepresentableProperty_iff_raw P).1 hf) p

end BaseChange

section ChosenBaseChange

variable {X Y : FppfStack.{u}} (f : StackHom X Y) (hf : f.IsRepresentable) (B : StackChart Y)

/-- A chosen presentation of the base change of a representable stack morphism `f` along the
tautological object of a chart `B` of the target. -/
noncomputable def baseChangePresentation : StackMorphismPresentation f B.scheme B.tautObj :=
  ((hasRepresentableProperty_iff_raw ⊤).1 hf B.scheme B.tautObj).some.1

/-- **The base change `B.scheme ×_Y X` of a chart `B` of `Y` along a representable morphism
`f : X ⟶ Y`**, as a chart of `X` (its scheme is the scheme of the chosen presentation
`baseChangePresentation f hf B`). -/
noncomputable def baseChangeChart : StackChart X :=
  chartOfPresentation (baseChangePresentation f hf B)

/-- The projection of the base-change chart to the chart it is pulled back from. -/
noncomputable def baseChangeChartToBase : (f.baseChangeChart hf B).scheme ⟶ B.scheme :=
  (baseChangePresentation f hf B).map

/-- Base change preserves étale surjective charts. -/
theorem baseChangeChart_isEtaleSurjective (hB : B.IsEtaleSurjective) :
    (f.baseChangeChart hf B).IsEtaleSurjective :=
  chartOfPresentation_isEtaleSurjective _ hB

/-- Base change preserves every representable property of a chart. -/
theorem baseChangeChart_hasRepresentableProperty (P : MorphismProperty Scheme.{u})
    (hB : B.HasRepresentableProperty P) : (f.baseChangeChart hf B).HasRepresentableProperty P :=
  chartOfPresentation_hasRepresentableProperty _ P hB

/-- The projection of the base-change chart has every scheme property that `f` has
representably (for properties respecting isomorphisms). -/
theorem baseChangeChartToBase_property (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hP : f.HasRepresentableProperty P) : P (f.baseChangeChartToBase hf B) :=
  presentation_map_property _ P hP

/-- For a representable proper morphism, the projection of the base-change chart is proper. -/
theorem baseChangeChartToBase_isProper
    (hP : f.HasRepresentableProperty @_root_.AlgebraicGeometry.IsProper) :
    _root_.AlgebraicGeometry.IsProper (f.baseChangeChartToBase hf B) :=
  f.baseChangeChartToBase_property hf B @_root_.AlgebraicGeometry.IsProper hP

end ChosenBaseChange

end StackHom

end GromovWitten.AlgebraicGeometry
