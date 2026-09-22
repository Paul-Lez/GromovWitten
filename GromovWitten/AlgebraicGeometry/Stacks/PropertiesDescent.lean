/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.GenuineBaseChange
import GromovWitten.AlgebraicGeometry.Stacks.EquivalenceProperties
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# Descent for representable properties of stack morphisms

The key geometric input is `StackMorphismPresentation.isPullback_baseChangeHom`: given a scheme
presentation `p` of the base change of `f : X ⟶ Y` by `y : Y(T)` and a presentation `q` of the
base change by any object of `Y(S)` isomorphic to the pullback of `y` along `base : S ⟶ T`, the
square

```
q.space --> p.space
   |           |
   v           v
   S  --base-> T
```

is an actual pullback square of schemes.  Only the two universal properties are used; no
comparison is accepted as data.  The proof rests on three coherence theorems proved here:
`stackMorphismInducedComparison_comp` (composition of classifying scheme maps),
`stackMorphismInducedComparison_compTarget` (change of the universal object along an
isomorphism and of the structure map along a composite), and the resulting equivalences
`stackMorphismClassifies_comp_iff` and `stackMorphismClassifies_compTarget_iff`.

Consequences proved here.

* `StackMorphismPresentation.property_iff_of_presentation`: every scheme-morphism property
  respecting isomorphisms is independent of the chosen presentation, so
  `StackHom.property_of_hasRepresentablePropertyRaw` transfers it to *every* presentation.
* `StackMorphismPresentation.property_of_descendsAlong` and
  `StackHom.hasRepresentablePropertyRaw_of_cover`: descent along any class of covers for which
  Mathlib provides `MorphismProperty.DescendsAlong`.  `hasRepresentablePropertyRaw_iff_cover`
  turns this into an equivalence for base-change stable properties.
* `StackMorphismPresentation.property_of_isZariskiLocalAtTarget` and
  `StackHom.hasRepresentablePropertyRaw_of_openCover`: Zariski locality on the test schemes.
* `StackMorphismPresentation.property_of_isStableUnderBaseChange`: the converse direction.

Coverage of the named representable properties.  fppf (equivalently, by
`smoothCover_le_fppfCover` and `etaleCover_le_fppfCover`, smooth and etale) descent is
available for smooth, etale, unramified, locally of finite type, locally of finite
presentation, quasi-compact, finite type, finite presentation, surjective, open immersion,
isomorphism, universally closed/open/injective.  Quasi-compactness has no fpqc-descent theorem
in Mathlib; `quasiCompact_descendsAlong_fpqcCover` supplies it here, which is what unlocks
finite type and finite presentation.

The extension modules `Stacks.FlatDescent` and `Stacks.ProperDescent` add fpqc and fppf
descent for flat, separated, and proper morphisms. Flatness uses faithfully flat descent of
modules; separatedness uses universal closedness of the diagonal, and properness combines
separatedness with universal closedness and local finite type. The statements in this file
remain available without importing those extensions.
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

section Coherence

variable {X Y : FppfStack.{u}}

/-- Transport along a reflexivity proof is the identity isomorphism. -/
@[simp]
theorem stackPullbackObjIsoOfEq_self (W : FppfStack.{u}) {R T : Scheme.{u}} {a : R ⟶ T}
    (h : a = a) (z : StackFiber W T) : stackPullbackObjIsoOfEq W h z = Iso.refl _ := by
  rw [Subsingleton.elim h rfl]
  rfl

/-- Pulling an object back along the identity returns the object, by the unit constraint of the
stack pseudofunctor. -/
noncomputable def stackPullbackIdIso (W : FppfStack.{u}) (T : Scheme.{u})
    (z : StackFiber W T) : z ≅ (stackPullback W (𝟙 T)).obj z :=
  ((Cat.Hom.toNatIso
    (W.toPseudofunctor.mapId (LocallyDiscrete.mk (Opposite.op T)))).app z).symm

/-- Right cancellation of an isomorphism in a composite of isomorphisms. -/
theorem iso_trans_right_cancel {C : Type*} [Category C] {a b c : C}
    {i j : a ≅ b} (k : b ≅ c) (h : i.trans k = j.trans k) : i = j := by
  apply Iso.ext
  have hh := congrArg Iso.hom h
  simp only [Iso.trans_hom] at hh
  exact (cancel_mono k.hom).1 hh

/-- Changing the classifying target map of a presentation by an equality changes the induced
comparison only by the canonical equality transport. -/
theorem stackMorphismInducedComparison_changeUniversal (f : StackHom X Y)
    {U T : Scheme.{u}} {map map' : U ⟶ T} (hmap : map = map') (object : StackFiber X U)
    (y : StackFiber Y T)
    (universal : (StackHom.appFunctor f U).obj object ≅ (stackPullback Y map).obj y)
    {S : Scheme.{u}} (g : S ⟶ U) (x : StackFiber X S)
    (e : x ≅ (stackPullback X g).obj object) :
    stackMorphismInducedComparison f map' object y
        (universal.trans (stackPullbackObjIsoOfEq Y hmap y)) g x e =
      (stackMorphismInducedComparison f map object y universal g x e).trans
        (stackPullbackObjIsoOfEq Y (congrArg (fun k => g ≫ k) hmap) y) := by
  subst hmap
  simp [stackPullbackObjIsoOfEq]

set_option backward.isDefEq.respectTransparency false in
/-- The comparison induced by a composite of scheme maps is the comparison induced in two
steps, up to the transport forced by associativity of scheme-map composition. -/
theorem stackMorphismInducedComparison_comp (f : StackHom X Y)
    {U T : Scheme.{u}} (map : U ⟶ T) (object : StackFiber X U) (y : StackFiber Y T)
    (universal : (StackHom.appFunctor f U).obj object ≅ (stackPullback Y map).obj y)
    {U' : Scheme.{u}} (g₂ : U' ⟶ U) (x' : StackFiber X U')
    (e₂ : x' ≅ (stackPullback X g₂).obj object)
    {S : Scheme.{u}} (g₁ : S ⟶ U') (x : StackFiber X S)
    (e₁ : x ≅ (stackPullback X g₁).obj x') :
    stackMorphismInducedComparison f (g₂ ≫ map) x' y
        (stackMorphismInducedComparison f map object y universal g₂ x' e₂) g₁ x e₁ =
      (stackMorphismInducedComparison f map object y universal (g₁ ≫ g₂) x
          (e₁.trans (((stackPullback X g₁).mapIso e₂).trans
            (stackPullbackCompIso X g₁ g₂ object)))).trans
        (stackPullbackObjIsoOfEq Y (Category.assoc g₁ g₂ map) y) := by
  apply Iso.ext
  simp only [stackMorphismInducedComparison, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  simp only [Iso.app_hom, Cat.Hom.toNatIso_hom]
  have hq := (f.naturality ⟨g₁.op⟩).hom.toNatTrans.naturality e₂.hom
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at hq
  rw [← reassoc_of% hq]
  rw [reassoc_of% stackHomNaturalityCompPullback f g₁ g₂ object]
  have hp := (Cat.Hom.toNatIso
    (Y.toPseudofunctor.mapComp ⟨g₂.op⟩ ⟨g₁.op⟩)).inv.naturality universal.hom
  change
    (stackPullback Y g₁).map ((stackPullback Y g₂).map universal.hom) ≫
        (stackPullbackCompIso Y g₁ g₂ ((stackPullback Y map).obj y)).hom =
      (stackPullbackCompIso Y g₁ g₂ ((StackHom.appFunctor f U).obj object)).hom ≫
        (stackPullback Y (g₁ ≫ g₂)).map universal.hom at hp
  rw [← reassoc_of% hp]
  rw [stackPullbackCompIso_assoc Y g₁ g₂ map y]

set_option backward.isDefEq.respectTransparency false in
/-- Post-composing the universal comparison of a presentation with an isomorphism to a
pulled-back object, and correspondingly composing the structure map, changes the induced
comparison only by the canonical pullback compositors. -/
theorem stackMorphismInducedComparison_compTarget (f : StackHom X Y)
    {V S T : Scheme.{u}} (m : V ⟶ S) (object : StackFiber X V)
    {y' : StackFiber Y S} {y : StackFiber Y T}
    (universal : (StackHom.appFunctor f V).obj object ≅ (stackPullback Y m).obj y')
    (base : S ⟶ T) (kappa : y' ≅ (stackPullback Y base).obj y)
    {W : Scheme.{u}} (g : W ⟶ V) (x : StackFiber X W)
    (e : x ≅ (stackPullback X g).obj object) :
    stackMorphismInducedComparison f (m ≫ base) object y
        (universal.trans (((stackPullback Y m).mapIso kappa).trans
          (stackPullbackCompIso Y m base y))) g x e =
      (stackMorphismInducedComparison f m object y' universal g x e).trans
        ((((stackPullback Y (g ≫ m)).mapIso kappa).trans
          (stackPullbackCompIso Y (g ≫ m) base y)).trans
          (stackPullbackObjIsoOfEq Y (Category.assoc g m base) y)) := by
  apply Iso.ext
  simp only [stackMorphismInducedComparison, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  have hp := (Cat.Hom.toNatIso
    (Y.toPseudofunctor.mapComp ⟨m.op⟩ ⟨g.op⟩)).inv.naturality kappa.hom
  change
    (stackPullback Y g).map ((stackPullback Y m).map kappa.hom) ≫
        (stackPullbackCompIso Y g m ((stackPullback Y base).obj y)).hom =
      (stackPullbackCompIso Y g m y').hom ≫
        (stackPullback Y (g ≫ m)).map kappa.hom at hp
  rw [← reassoc_of% hp]
  rw [stackPullbackCompIso_assoc Y g m base y]

/-- With the underlying scheme-map equation fixed, classification is exactly the equation
between the induced comparison and the supplied one. -/
theorem stackMorphismClassifies_iff (f : StackHom X Y)
    {U T : Scheme.{u}} (map : U ⟶ T) (object : StackFiber X U) (y : StackFiber Y T)
    (universal : (StackHom.appFunctor f U).obj object ≅ (stackPullback Y map).obj y)
    {S : Scheme.{u}} {toBase : S ⟶ T} (x : StackFiber X S)
    (comparison : (StackHom.appFunctor f S).obj x ≅ (stackPullback Y toBase).obj y)
    {g : S ⟶ U} (objectIso : x ≅ (stackPullback X g).obj object)
    (map_eq : g ≫ map = toBase) :
    StackMorphismClassifies f map object y universal toBase x comparison g objectIso ↔
      (stackMorphismInducedComparison f map object y universal g x objectIso).trans
        (stackPullbackObjIsoOfEq Y map_eq y) = comparison := by
  constructor
  · rintro ⟨me, h⟩
    rwa [Subsingleton.elim map_eq me]
  · intro h
    exact ⟨map_eq, h⟩

set_option backward.isDefEq.respectTransparency false in
/-- Classification through a presentation composes with classification through a further
scheme map: the two-step classification is equivalent to the single classification along the
composite scheme map. -/
theorem stackMorphismClassifies_comp_iff (f : StackHom X Y)
    {U T : Scheme.{u}} (map : U ⟶ T) (object : StackFiber X U) (y : StackFiber Y T)
    (universal : (StackHom.appFunctor f U).obj object ≅ (stackPullback Y map).obj y)
    {U' : Scheme.{u}} {g₂ : U' ⟶ U} {toBase₂ : U' ⟶ T} {x₂ : StackFiber X U'}
    {c₂ : (StackHom.appFunctor f U').obj x₂ ≅ (stackPullback Y toBase₂).obj y}
    {e₂ : x₂ ≅ (stackPullback X g₂).obj object}
    (h₂ : StackMorphismClassifies f map object y universal toBase₂ x₂ c₂ g₂ e₂)
    {S : Scheme.{u}} {g₁ : S ⟶ U'} {toBase₁ : S ⟶ T} {x₁ : StackFiber X S}
    {c₁ : (StackHom.appFunctor f S).obj x₁ ≅ (stackPullback Y toBase₁).obj y}
    {e₁ : x₁ ≅ (stackPullback X g₁).obj x₂}
    (map_eq : g₁ ≫ toBase₂ = toBase₁) :
    StackMorphismClassifies f toBase₂ x₂ y c₂ toBase₁ x₁ c₁ g₁ e₁ ↔
      StackMorphismClassifies f map object y universal toBase₁ x₁ c₁ (g₁ ≫ g₂)
        (e₁.trans (((stackPullback X g₁).mapIso e₂).trans
          (stackPullbackCompIso X g₁ g₂ object))) := by
  obtain ⟨m₂, hc₂⟩ := h₂
  subst m₂
  simp only [stackPullbackObjIsoOfEq, Iso.trans_refl] at hc₂
  subst hc₂
  have map_eq' : (g₁ ≫ g₂) ≫ map = toBase₁ := (Category.assoc g₁ g₂ map).trans map_eq
  rw [stackMorphismClassifies_iff f _ _ y _ x₁ c₁ e₁ map_eq]
  rw [stackMorphismClassifies_iff f map object y universal x₁ c₁ _ map_eq']
  rw [stackMorphismInducedComparison_comp f map object y universal g₂ x₂ e₂ g₁ x₁ e₁]
  rw [Iso.trans_assoc, stackPullbackObjIsoOfEq_trans]

set_option backward.isDefEq.respectTransparency false in
/-- Composing the structure map of a presentation with a further scheme map, and its universal
object with an isomorphism to the corresponding pullback, does not change which scheme maps
classify a given object and comparison. -/
theorem stackMorphismClassifies_compTarget_iff (f : StackHom X Y)
    {V S T : Scheme.{u}} (m : V ⟶ S) (object : StackFiber X V)
    {y' : StackFiber Y S} {y : StackFiber Y T}
    (universal : (StackHom.appFunctor f V).obj object ≅ (stackPullback Y m).obj y')
    (base : S ⟶ T) (kappa : y' ≅ (stackPullback Y base).obj y)
    {W : Scheme.{u}} {toBase : W ⟶ S} (x : StackFiber X W)
    (c : (StackHom.appFunctor f W).obj x ≅ (stackPullback Y toBase).obj y')
    {g : W ⟶ V} (e : x ≅ (stackPullback X g).obj object)
    (map_eq : g ≫ m = toBase) :
    StackMorphismClassifies f m object y' universal toBase x c g e ↔
      StackMorphismClassifies f (m ≫ base) object y
        (universal.trans (((stackPullback Y m).mapIso kappa).trans
          (stackPullbackCompIso Y m base y)))
        (toBase ≫ base) x
        (c.trans (((stackPullback Y toBase).mapIso kappa).trans
          (stackPullbackCompIso Y toBase base y))) g e := by
  subst map_eq
  have map_eq' : g ≫ (m ≫ base) = (g ≫ m) ≫ base := (Category.assoc g m base).symm
  rw [stackMorphismClassifies_iff f m object y' universal x c e rfl]
  rw [stackMorphismClassifies_iff f (m ≫ base) object y _ x _ e map_eq']
  rw [stackMorphismInducedComparison_compTarget f m object universal base kappa g x e]
  simp only [stackPullbackObjIsoOfEq_self, Iso.trans_refl]
  constructor
  · rintro rfl
    rfl
  · intro h
    exact iso_trans_right_cancel _ h

end Coherence

namespace StackMorphismPresentation

variable {X Y : FppfStack.{u}} {f : StackHom X Y}
  {T : Scheme.{u}} {y : StackFiber Y T} {S : Scheme.{u}} {y' : StackFiber Y S}

/-- A presentation over `S` is also a presentation of the composite structure map, once the
universal object is compared with the pullback of the object over `T`. -/
noncomputable def compTargetComparison (q : StackMorphismPresentation f S y')
    (base : S ⟶ T) (kappa : y' ≅ (stackPullback Y base).obj y) :
    (StackHom.appFunctor f q.space).obj q.object ≅
      (stackPullback Y (q.map ≫ base)).obj y :=
  q.comparison.trans
    (((stackPullback Y q.map).mapIso kappa).trans (stackPullbackCompIso Y q.map base y))

variable (p : StackMorphismPresentation f T y)

/-- The canonical scheme map from a presentation over `S` to a presentation over `T`. -/
noncomputable def baseChangeHom (q : StackMorphismPresentation f S y') (base : S ⟶ T)
    (kappa : y' ≅ (stackPullback Y base).obj y) : q.space ⟶ p.space :=
  p.lift (q.map ≫ base) q.object (q.compTargetComparison base kappa)

@[reassoc]
theorem baseChangeHom_map (q : StackMorphismPresentation f S y') (base : S ⟶ T)
    (kappa : y' ≅ (stackPullback Y base).obj y) :
    p.baseChangeHom q base kappa ≫ p.map = q.map ≫ base :=
  p.lift_map _ _ _

/-- The universal object of the presentation over `S` is the pullback of the universal object
of the presentation over `T` along the canonical comparison map. -/
noncomputable def baseChangeHomObjectIso (q : StackMorphismPresentation f S y') (base : S ⟶ T)
    (kappa : y' ≅ (stackPullback Y base).obj y) :
    q.object ≅ (stackPullback X (p.baseChangeHom q base kappa)).obj p.object :=
  p.liftObjectIso (q.map ≫ base) q.object (q.compTargetComparison base kappa)

theorem baseChangeHom_classifies (q : StackMorphismPresentation f S y') (base : S ⟶ T)
    (kappa : y' ≅ (stackPullback Y base).obj y) :
    StackMorphismClassifies f p.map p.object y p.comparison (q.map ≫ base) q.object
      (q.compTargetComparison base kappa) (p.baseChangeHom q base kappa)
      (p.baseChangeHomObjectIso q base kappa) :=
  p.lift_compatible _ _ _

/-- The object of `X` over a test scheme determined by a map into the representing scheme. -/
noncomputable def testObject {W : Scheme.{u}} (w : W ⟶ p.space) : StackFiber X W :=
  (stackPullback X w).obj p.object

/-- The comparison carried by `testObject`, transported to an arbitrary factorisation of the
composite structure map. -/
noncomputable def testComparisonOver {W : Scheme.{u}} {w₁ : W ⟶ S} {base : S ⟶ T}
    {w₂ : W ⟶ p.space} (hw : w₁ ≫ base = w₂ ≫ p.map) :
    (StackHom.appFunctor f W).obj (p.testObject w₂) ≅
      (stackPullback Y (w₁ ≫ base)).obj y :=
  (stackMorphismInducedComparison f p.map p.object y p.comparison w₂ (p.testObject w₂)
    (Iso.refl _)).trans (stackPullbackObjIsoOfEq Y hw.symm y)

theorem testComparisonOver_classifies {W : Scheme.{u}} {w₁ : W ⟶ S} {base : S ⟶ T}
    {w₂ : W ⟶ p.space} (hw : w₁ ≫ base = w₂ ≫ p.map) :
    StackMorphismClassifies f p.map p.object y p.comparison (w₁ ≫ base) (p.testObject w₂)
      (p.testComparisonOver hw) w₂ (Iso.refl _) :=
  ⟨hw.symm, rfl⟩

theorem eq_lift_testComparisonOver {W : Scheme.{u}} {w₁ : W ⟶ S} {base : S ⟶ T}
    {w₂ : W ⟶ p.space} (hw : w₁ ≫ base = w₂ ≫ p.map) :
    w₂ = p.lift (w₁ ≫ base) (p.testObject w₂) (p.testComparisonOver hw) :=
  p.lift_unique _ _ _ _ _ (p.testComparisonOver_classifies hw)

/-- The comparison carried by `testObject`, expressed over the object on `S`. -/
noncomputable def testComparisonBase {W : Scheme.{u}} {w₁ : W ⟶ S} {base : S ⟶ T}
    {w₂ : W ⟶ p.space} (kappa : y' ≅ (stackPullback Y base).obj y)
    (hw : w₁ ≫ base = w₂ ≫ p.map) :
    (StackHom.appFunctor f W).obj (p.testObject w₂) ≅ (stackPullback Y w₁).obj y' :=
  (p.testComparisonOver hw).trans
    ((((stackPullback Y w₁).mapIso kappa).trans (stackPullbackCompIso Y w₁ base y)).symm)

theorem testComparisonBase_trans {W : Scheme.{u}} {w₁ : W ⟶ S} {base : S ⟶ T}
    {w₂ : W ⟶ p.space} (kappa : y' ≅ (stackPullback Y base).obj y)
    (hw : w₁ ≫ base = w₂ ≫ p.map) :
    (p.testComparisonBase kappa hw).trans
        (((stackPullback Y w₁).mapIso kappa).trans (stackPullbackCompIso Y w₁ base y)) =
      p.testComparisonOver hw := by
  simp [testComparisonBase]

set_option backward.isDefEq.respectTransparency false in
/-- The two classification problems attached to the two presentations agree: a scheme map to
the presentation over `S` classifies the test data exactly when its composite with the
canonical comparison classifies the corresponding data over `T`. -/
theorem testClassifies_iff (q : StackMorphismPresentation f S y') (base : S ⟶ T)
    (kappa : y' ≅ (stackPullback Y base).obj y) {W : Scheme.{u}} {w₁ : W ⟶ S}
    {w₂ : W ⟶ p.space} (hw : w₁ ≫ base = w₂ ≫ p.map) (l : W ⟶ q.space)
    (hl : l ≫ q.map = w₁) (el : p.testObject w₂ ≅ (stackPullback X l).obj q.object) :
    StackMorphismClassifies f q.map q.object y' q.comparison w₁ (p.testObject w₂)
        (p.testComparisonBase kappa hw) l el ↔
      StackMorphismClassifies f p.map p.object y p.comparison (w₁ ≫ base) (p.testObject w₂)
        (p.testComparisonOver hw) (l ≫ p.baseChangeHom q base kappa)
        (el.trans (((stackPullback X l).mapIso
            (p.baseChangeHomObjectIso q base kappa)).trans
          (stackPullbackCompIso X l (p.baseChangeHom q base kappa) p.object))) := by
  rw [stackMorphismClassifies_compTarget_iff f q.map q.object q.comparison base kappa
    (p.testObject w₂) (p.testComparisonBase kappa hw) el hl]
  rw [p.testComparisonBase_trans kappa hw]
  exact stackMorphismClassifies_comp_iff f p.map p.object y p.comparison
    (p.baseChangeHom_classifies q base kappa)
    ((Category.assoc l q.map base).symm.trans (congrArg (fun k => k ≫ base) hl))

set_option backward.isDefEq.respectTransparency false in
/-- **Base change of presentations.**  The representing scheme of a presentation over `S` is an
actual fibre product of the representing scheme over `T` with `S`.  Consequently every
scheme-level base-change or descent statement applies verbatim to representable stack
morphisms. -/
theorem isPullback_baseChangeHom (q : StackMorphismPresentation f S y') (base : S ⟶ T)
    (kappa : y' ≅ (stackPullback Y base).obj y) :
    IsPullback q.map (p.baseChangeHom q base kappa) base p.map := by
  have hcomm : CommSq q.map (p.baseChangeHom q base kappa) base p.map :=
    ⟨(p.baseChangeHom_map q base kappa).symm⟩
  refine IsPullback.of_isLimit' hcomm (PullbackCone.IsLimit.mk hcomm.w
    (fun s => q.lift s.fst (p.testObject s.snd) (p.testComparisonBase kappa s.condition))
    (fun s => q.lift_map _ _ _) (fun s => ?_) (fun s m hm1 hm2 => ?_))
  · have hl := q.lift_compatible s.fst (p.testObject s.snd)
      (p.testComparisonBase kappa s.condition)
    have hbig := (p.testClassifies_iff q base kappa s.condition
      (q.lift s.fst (p.testObject s.snd) (p.testComparisonBase kappa s.condition))
      (q.lift_map _ _ _) (q.liftObjectIso _ _ _)).1 hl
    exact (p.lift_unique _ _ _ _ _ hbig).trans
      (p.eq_lift_testComparisonOver s.condition).symm
  · refine q.lift_unique _ _ _ m
      ((stackPullbackObjIsoOfEq X hm2.symm p.object).trans
        (((stackPullback X m).mapIso (p.baseChangeHomObjectIso q base kappa)).trans
          (stackPullbackCompIso X m (p.baseChangeHom q base kappa) p.object)).symm)
      ((p.testClassifies_iff q base kappa s.condition m hm1 _).2 ?_)
    have hchanged := stackMorphismClassifies_changeMap (Iso.refl _)
      (stackPullbackObjIsoOfEq X hm2.symm p.object)
      (p.testComparisonOver_classifies s.condition) hm2.symm (by simp)
    simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
    exact hchanged

/-- The comparison map between two presentations of the same base change is an isomorphism. -/
theorem isIso_baseChangeHom_id (p q : StackMorphismPresentation f T y) :
    IsIso (p.baseChangeHom q (𝟙 T) (stackPullbackIdIso Y T y)) := by
  have hiso : (MorphismProperty.isomorphisms Scheme.{u})
      (p.baseChangeHom q (𝟙 T) (stackPullbackIdIso Y T y)) :=
    MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme.{u})
      (p.isPullback_baseChangeHom q (𝟙 T) (stackPullbackIdIso Y T y))
      ((MorphismProperty.isomorphisms.iff (𝟙 T)).2 inferInstance)
  exact hiso

/-- The comparison map between two presentations of the same base change is compatible with the
two structure maps. -/
theorem baseChangeHom_id_map (p q : StackMorphismPresentation f T y) :
    p.baseChangeHom q (𝟙 T) (stackPullbackIdIso Y T y) ≫ p.map = q.map := by
  rw [p.baseChangeHom_map q (𝟙 T) (stackPullbackIdIso Y T y), Category.comp_id]

/-- **Independence of the presentation.**  A scheme-morphism property respecting isomorphisms
holds for the structure map of one presentation of a base change exactly when it holds for the
structure map of any other. -/
theorem property_iff_of_presentation (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (p q : StackMorphismPresentation f T y) : P p.map ↔ P q.map := by
  have := p.isIso_baseChangeHom_id q
  rw [← p.baseChangeHom_id_map q, P.cancel_left_of_respectsIso]

/-- **Descent along a cover of the test scheme.**  If the scheme property `P` descends along
`Q`, then it descends from a presentation over a `Q`-cover to a presentation over the base. -/
theorem property_of_descendsAlong (P Q : MorphismProperty Scheme.{u})
    [MorphismProperty.DescendsAlong P Q]
    (p : StackMorphismPresentation f T y) (q : StackMorphismPresentation f S y')
    (base : S ⟶ T) (kappa : y' ≅ (stackPullback Y base).obj y) (hQ : Q base)
    (hq : P q.map) : P p.map :=
  MorphismProperty.of_isPullback_of_descendsAlong
    (p.isPullback_baseChangeHom q base kappa) hQ hq

/-- The converse of `property_of_descendsAlong`: a base-change-stable property passes from a
presentation over the base to a presentation over any test scheme above it. -/
theorem property_of_isStableUnderBaseChange (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (p : StackMorphismPresentation f T y)
    (q : StackMorphismPresentation f S y') (base : S ⟶ T)
    (kappa : y' ≅ (stackPullback Y base).obj y) (hp : P p.map) : P q.map :=
  P.of_isPullback (p.isPullback_baseChangeHom q base kappa).flip hp

/-- **Zariski locality on the test scheme.**  A property local at the target can be checked on
presentations over the members of any open cover. -/
theorem property_of_isZariskiLocalAtTarget (P : MorphismProperty Scheme.{u})
    [_root_.AlgebraicGeometry.IsZariskiLocalAtTarget P]
    (p : StackMorphismPresentation f T y) (U : T.OpenCover)
    (q : ∀ i, StackMorphismPresentation f (U.X i) ((stackPullback Y (U.f i)).obj y))
    (hq : ∀ i, P (q i).map) : P p.map := by
  refine _root_.AlgebraicGeometry.IsZariskiLocalAtTarget.of_openCover (f := p.map) U fun i => ?_
  have hsq := (p.isPullback_baseChangeHom (q i) (U.f i) (Iso.refl _)).flip
  change P (Limits.pullback.snd p.map (U.f i))
  rw [← P.cancel_left_of_respectsIso hsq.isoPullback.hom, hsq.isoPullback_hom_snd]
  exact hq i

end StackMorphismPresentation

namespace StackHom

variable {X Y : FppfStack.{u}} {f : StackHom X Y}

/-- `f` has the scheme property `P` on a `Q`-cover if every test object admits a `Q`-cover of
its test scheme carrying a presentation whose structure map has `P`. -/
def HasRepresentablePropertyOnCover (f : StackHom X Y) (P Q : MorphismProperty Scheme.{u}) :
    Prop :=
  ∀ (T : Scheme.{u}) (y : StackFiber Y T), ∃ (S : Scheme.{u}) (base : S ⟶ T), Q base ∧
    ∃ q : StackMorphismPresentation f S ((stackPullback Y base).obj y), P q.map

/-- `f` has the scheme property `P` on an open cover if every test object admits an open cover
of its test scheme carrying presentations whose structure maps have `P`. -/
def HasRepresentablePropertyOnOpenCover (f : StackHom X Y) (P : MorphismProperty Scheme.{u}) :
    Prop :=
  ∀ (T : Scheme.{u}) (y : StackFiber Y T), ∃ U : T.OpenCover.{u},
    ∃ q : ∀ i, StackMorphismPresentation f (U.X i) ((stackPullback Y (U.f i)).obj y),
      ∀ i, P (q i).map

/-- The structure map of every presentation of a base change of a raw-representable morphism
has the property, not just the particular presentation produced by the witness. -/
theorem property_of_hasRepresentablePropertyRaw (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] (h : f.HasRepresentablePropertyRaw P) {T : Scheme.{u}}
    {y : StackFiber Y T} (p : StackMorphismPresentation f T y) : P p.map := by
  obtain ⟨⟨p', hp'⟩⟩ := h T y
  exact (p.property_iff_of_presentation P p').2 hp'

/-- **Descent for raw representable properties.**  A representable stack morphism has the
scheme property `P` as soon as, for every test object, some `Q`-cover of the test scheme
carries a presentation whose structure map has `P`. -/
theorem hasRepresentablePropertyRaw_of_cover (P Q : MorphismProperty Scheme.{u})
    [MorphismProperty.DescendsAlong P Q] (hrep : f.HasRepresentablePropertyRaw ⊤)
    (hcover : f.HasRepresentablePropertyOnCover P Q) :
    f.HasRepresentablePropertyRaw P := by
  intro T y
  obtain ⟨⟨p, -⟩⟩ := hrep T y
  obtain ⟨S, base, hQ, q, hq⟩ := hcover T y
  exact ⟨⟨p, p.property_of_descendsAlong P Q q base (Iso.refl _) hQ hq⟩⟩

/-- **Descent for representable properties**, in the 2-isomorphism-invariant formulation. -/
theorem hasRepresentableProperty_of_cover (P Q : MorphismProperty Scheme.{u})
    [MorphismProperty.DescendsAlong P Q] (hrep : f.IsRepresentable)
    (hcover : f.HasRepresentablePropertyOnCover P Q) :
    f.HasRepresentableProperty P :=
  (hasRepresentableProperty_iff_raw P).2
    (hasRepresentablePropertyRaw_of_cover P Q
      ((hasRepresentableProperty_iff_raw (⊤ : MorphismProperty Scheme.{u})).1 hrep) hcover)

/-- Descent along a smaller class of covers follows from descent along a larger one. -/
theorem hasRepresentableProperty_of_cover_of_le (P Q Q' : MorphismProperty Scheme.{u})
    [MorphismProperty.DescendsAlong P Q] (hle : Q' ≤ Q) (hrep : f.IsRepresentable)
    (hcover : f.HasRepresentablePropertyOnCover P Q') :
    f.HasRepresentableProperty P := by
  have : MorphismProperty.DescendsAlong P Q' := MorphismProperty.DescendsAlong.of_le hle
  exact hasRepresentableProperty_of_cover P Q' hrep hcover

/-- The cover condition is also necessary when `P` is stable under base change, so descent is
an equivalence. -/
theorem hasRepresentablePropertyRaw_iff_cover (P Q : MorphismProperty Scheme.{u})
    [MorphismProperty.DescendsAlong P Q] [P.IsStableUnderBaseChange]
    (hrep : f.HasRepresentablePropertyRaw ⊤)
    (hQ : ∀ (T : Scheme.{u}), ∃ (S : Scheme.{u}) (base : S ⟶ T), Q base) :
    f.HasRepresentablePropertyRaw P ↔ f.HasRepresentablePropertyOnCover P Q := by
  refine ⟨fun h T y => ?_, fun h => hasRepresentablePropertyRaw_of_cover P Q hrep h⟩
  obtain ⟨S, base, hb⟩ := hQ T
  obtain ⟨⟨q, -⟩⟩ := hrep S ((stackPullback Y base).obj y)
  obtain ⟨⟨p, hp⟩⟩ := h T y
  exact ⟨S, base, hb, q,
    p.property_of_isStableUnderBaseChange P q base (Iso.refl _) hp⟩

/-- **Zariski locality of representable properties on the test scheme.** -/
theorem hasRepresentablePropertyRaw_of_openCover (P : MorphismProperty Scheme.{u})
    [_root_.AlgebraicGeometry.IsZariskiLocalAtTarget P]
    (hrep : f.HasRepresentablePropertyRaw ⊤)
    (hcover : f.HasRepresentablePropertyOnOpenCover P) :
    f.HasRepresentablePropertyRaw P := by
  intro T y
  obtain ⟨⟨p, -⟩⟩ := hrep T y
  obtain ⟨U, q, hq⟩ := hcover T y
  exact ⟨⟨p, p.property_of_isZariskiLocalAtTarget P U q hq⟩⟩

/-- **Zariski locality of representable properties**, in the 2-isomorphism-invariant
formulation. -/
theorem hasRepresentableProperty_of_openCover (P : MorphismProperty Scheme.{u})
    [_root_.AlgebraicGeometry.IsZariskiLocalAtTarget P] (hrep : f.IsRepresentable)
    (hcover : f.HasRepresentablePropertyOnOpenCover P) :
    f.HasRepresentableProperty P :=
  (hasRepresentableProperty_iff_raw P).2
    (hasRepresentablePropertyRaw_of_openCover P
      ((hasRepresentableProperty_iff_raw (⊤ : MorphismProperty Scheme.{u})).1 hrep) hcover)

end StackHom

section Covers

open _root_.AlgebraicGeometry (Surjective Flat QuasiCompact LocallyOfFinitePresentation
  LocallyOfFiniteType Smooth Etale FormallyUnramified IsOpenImmersion UniversallyClosed
  UniversallyOpen UniversallyInjective IsZariskiLocalAtTarget)

/-- fpqc covers: surjective, flat and quasi-compact scheme morphisms. -/
abbrev FpqcCover : MorphismProperty Scheme.{u} := @Surjective ⊓ @Flat ⊓ @QuasiCompact

/-- fppf covers: surjective, flat and locally finitely presented scheme morphisms. -/
abbrev FppfCover : MorphismProperty Scheme.{u} :=
  @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation

/-- Smooth covers: surjective smooth scheme morphisms. -/
abbrev SmoothCover : MorphismProperty Scheme.{u} := @Surjective ⊓ @Smooth

/-- Etale covers: surjective etale scheme morphisms. -/
abbrev EtaleCover : MorphismProperty Scheme.{u} := @Surjective ⊓ @Etale

theorem smoothCover_le_fppfCover : SmoothCover.{u} ≤ FppfCover.{u} := by
  rintro A B g ⟨hs, hsm⟩
  have : Smooth g := hsm
  exact ⟨⟨hs, inferInstance⟩, inferInstance⟩

theorem etaleCover_le_fppfCover : EtaleCover.{u} ≤ FppfCover.{u} := by
  rintro A B g ⟨hs, he⟩
  have : Etale g := he
  exact ⟨⟨hs, inferInstance⟩, inferInstance⟩

theorem etaleCover_le_smoothCover : EtaleCover.{u} ≤ SmoothCover.{u} := by
  rintro A B g ⟨hs, he⟩
  have : Etale g := he
  exact ⟨hs, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Quasi-compactness satisfies fpqc descent.**  This scheme-level statement is not yet in
Mathlib; it is proved here by reducing to an affine base, where quasi-compactness of a morphism
is compactness of its source, and using that the projection from the base change is
surjective. -/
instance quasiCompact_descendsAlong_fpqcCover :
    MorphismProperty.DescendsAlong (@QuasiCompact : MorphismProperty Scheme.{u})
      FpqcCover.{u} := by
  refine _root_.AlgebraicGeometry.IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact
    (@QuasiCompact : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat) ?_ ?_
  · rw [inf_comm]
    gcongr
    exact _root_.AlgebraicGeometry.IsLocalIso.le_of_isZariskiLocalAtSource @Flat
  · intro R S W φ g hφ hfst
    have hsurj : Surjective (_root_.AlgebraicGeometry.Spec.map φ) := hφ.1
    have hflat : Flat (_root_.AlgebraicGeometry.Spec.map φ) := hφ.2
    have hqc : QuasiCompact (Limits.pullback.fst
      (_root_.AlgebraicGeometry.Spec.map φ) g) := hfst
    have hc : CompactSpace ↥(Limits.pullback
        (_root_.AlgebraicGeometry.Spec.map φ) g) :=
      QuasiCompact.compactSpace_of_compactSpace
        (Limits.pullback.fst (_root_.AlgebraicGeometry.Spec.map φ) g)
    have hW : CompactSpace ↥W := by
      constructor
      rw [← Set.image_univ_of_surjective
        (Limits.pullback.snd (_root_.AlgebraicGeometry.Spec.map φ) g).surjective]
      exact isCompact_univ.image
        (Limits.pullback.snd (_root_.AlgebraicGeometry.Spec.map φ) g).continuous
    exact _root_.AlgebraicGeometry.HasAffineProperty.iff_of_isAffine.mpr hW

/-- Unramified morphisms satisfy fpqc descent, because both of their defining properties do. -/
instance : MorphismProperty.DescendsAlong @Unramified FpqcCover.{u} where
  of_isPullback sq hf hfst :=
    { formallyUnramified := MorphismProperty.DescendsAlong.of_isPullback
        (P := @FormallyUnramified) (Q := FpqcCover.{u}) sq hf hfst.formallyUnramified
      locallyOfFiniteType := MorphismProperty.DescendsAlong.of_isPullback
        (P := @LocallyOfFiniteType) (Q := FpqcCover.{u}) sq hf hfst.locallyOfFiniteType }

section Instances

/- Mathlib's fppf-descent instance is derived from fpqc descent plus Zariski locality at the
target, and finding the latter for the ring-hom-defined properties needs the more permissive
definitional-unfolding behaviour.  The specialisations are recorded once here so that later
instance searches succeed with the default settings. -/
set_option backward.isDefEq.respectTransparency false

instance : MorphismProperty.DescendsAlong @Smooth FppfCover.{u} := inferInstance

instance : MorphismProperty.DescendsAlong @Etale FppfCover.{u} := inferInstance

instance : MorphismProperty.DescendsAlong @FormallyUnramified FppfCover.{u} := inferInstance

instance : MorphismProperty.DescendsAlong @LocallyOfFiniteType FppfCover.{u} := inferInstance

instance : MorphismProperty.DescendsAlong @LocallyOfFinitePresentation FppfCover.{u} :=
  inferInstance

instance : MorphismProperty.DescendsAlong @Unramified FppfCover.{u} := inferInstance

instance : MorphismProperty.DescendsAlong @Surjective FppfCover.{u} := inferInstance

instance : MorphismProperty.DescendsAlong @IsOpenImmersion FppfCover.{u} := inferInstance

instance : MorphismProperty.DescendsAlong @UniversallyClosed FppfCover.{u} := inferInstance

instance : MorphismProperty.DescendsAlong @UniversallyOpen FppfCover.{u} := inferInstance

instance : MorphismProperty.DescendsAlong @UniversallyInjective FppfCover.{u} := inferInstance

instance : MorphismProperty.DescendsAlong (MorphismProperty.isomorphisms Scheme.{u})
    FppfCover.{u} := inferInstance

instance : MorphismProperty.DescendsAlong @QuasiCompact FppfCover.{u} := inferInstance

instance : MorphismProperty.DescendsAlong
    ((@QuasiCompact ⊓ @LocallyOfFiniteType) : MorphismProperty Scheme.{u}) FppfCover.{u} :=
  inferInstance

instance : MorphismProperty.DescendsAlong
    ((@QuasiCompact ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u})
    FppfCover.{u} := inferInstance

instance : IsZariskiLocalAtTarget (@Unramified : MorphismProperty Scheme.{u}) := inferInstance

instance : IsZariskiLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u}) := inferInstance

instance : IsZariskiLocalAtTarget (@Flat : MorphismProperty Scheme.{u}) := inferInstance

instance : IsZariskiLocalAtTarget (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
  inferInstance

instance : IsZariskiLocalAtTarget
    (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) := inferInstance

instance : IsZariskiLocalAtTarget
    ((@QuasiCompact ⊓ @LocallyOfFiniteType) : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsLocalAtTarget.inf _ _

instance : IsZariskiLocalAtTarget
    ((@QuasiCompact ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsLocalAtTarget.inf _ _

end Instances

end Covers

namespace StackHom

variable {X Y : FppfStack.{u}} {f : StackHom X Y}

open _root_.AlgebraicGeometry renaming Smooth → SchSmooth, Etale → SchEtale,
  Flat → SchFlat, QuasiCompact → SchQuasiCompact,
  LocallyOfFiniteType → SchLocallyOfFiniteType,
  LocallyOfFinitePresentation → SchLocallyOfFinitePresentation,
  IsOpenImmersion → SchIsOpenImmersion, IsSeparated → SchIsSeparated,
  IsProper → SchIsProper, IsImmersion → SchIsImmersion,
  IsClosedImmersion → SchIsClosedImmersion

open _root_.GromovWitten.AlgebraicGeometry renaming Unramified → SchUnramified

/-! ### fppf and smooth descent for the named representable properties

The properties below are exactly those for which Mathlib supplies scheme-level fppf descent.
Flatness, quasi-compactness, separatedness, properness, and the immersion properties do not
yet descend along faithfully flat covers in Mathlib; for those the Zariski-local statements at
the end of this section are the strongest currently available. -/

/-- Representable smoothness descends along fppf covers of the test schemes. -/
theorem smooth_of_fppfCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchSmooth FppfCover.{u}) : f.Smooth :=
  hasRepresentableProperty_of_cover _ _ hrep h

/-- Representable smoothness descends along smooth surjective covers of the test schemes. -/
theorem smooth_of_smoothCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchSmooth SmoothCover.{u}) : f.Smooth :=
  hasRepresentableProperty_of_cover_of_le _ FppfCover.{u} _ smoothCover_le_fppfCover hrep h

/-- Representable etaleness descends along fppf covers of the test schemes. -/
theorem etale_of_fppfCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchEtale FppfCover.{u}) : f.Etale :=
  hasRepresentableProperty_of_cover _ _ hrep h

/-- Representable etaleness descends along smooth surjective covers of the test schemes. -/
theorem etale_of_smoothCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchEtale SmoothCover.{u}) : f.Etale :=
  hasRepresentableProperty_of_cover_of_le _ FppfCover.{u} _ smoothCover_le_fppfCover hrep h

/-- Representable unramifiedness descends along fppf covers of the test schemes. -/
theorem unramified_of_fppfCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchUnramified FppfCover.{u}) : f.Unramified :=
  hasRepresentableProperty_of_cover _ _ hrep h

/-- Representable unramifiedness descends along smooth surjective covers. -/
theorem unramified_of_smoothCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchUnramified SmoothCover.{u}) : f.Unramified :=
  hasRepresentableProperty_of_cover_of_le _ FppfCover.{u} _ smoothCover_le_fppfCover hrep h

/-- Being representably locally of finite type descends along fppf covers. -/
theorem locallyOfFiniteType_of_fppfCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchLocallyOfFiniteType FppfCover.{u}) :
    f.LocallyOfFiniteType :=
  hasRepresentableProperty_of_cover _ _ hrep h

/-- Being representably locally of finite type descends along smooth surjective covers. -/
theorem locallyOfFiniteType_of_smoothCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchLocallyOfFiniteType SmoothCover.{u}) :
    f.LocallyOfFiniteType :=
  hasRepresentableProperty_of_cover_of_le _ FppfCover.{u} _ smoothCover_le_fppfCover hrep h

/-- Being representably locally of finite presentation descends along fppf covers. -/
theorem locallyOfFinitePresentation_of_fppfCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchLocallyOfFinitePresentation FppfCover.{u}) :
    f.LocallyOfFinitePresentation :=
  hasRepresentableProperty_of_cover _ _ hrep h

/-- Being representably locally of finite presentation descends along smooth covers. -/
theorem locallyOfFinitePresentation_of_smoothCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchLocallyOfFinitePresentation SmoothCover.{u}) :
    f.LocallyOfFinitePresentation :=
  hasRepresentableProperty_of_cover_of_le _ FppfCover.{u} _ smoothCover_le_fppfCover hrep h

/-- Being a representable open immersion descends along fppf covers. -/
theorem openImmersion_of_fppfCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchIsOpenImmersion FppfCover.{u}) : f.OpenImmersion :=
  hasRepresentableProperty_of_cover _ _ hrep h

/-- Representable quasi-compactness descends along fppf covers. -/
theorem quasiCompact_of_fppfCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchQuasiCompact FppfCover.{u}) : f.QuasiCompact :=
  hasRepresentableProperty_of_cover _ _ hrep h

/-- Representable quasi-compactness descends along smooth surjective covers. -/
theorem quasiCompact_of_smoothCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchQuasiCompact SmoothCover.{u}) : f.QuasiCompact :=
  hasRepresentableProperty_of_cover_of_le _ FppfCover.{u} _ smoothCover_le_fppfCover hrep h

/-- Being a representable finite-type morphism descends along fppf covers. -/
theorem finiteType_of_fppfCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover
      (@SchQuasiCompact ⊓ @SchLocallyOfFiniteType) FppfCover.{u}) : f.FiniteType :=
  hasRepresentableProperty_of_cover _ _ hrep h

/-- Being a representable finite-type morphism descends along smooth surjective covers. -/
theorem finiteType_of_smoothCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover
      (@SchQuasiCompact ⊓ @SchLocallyOfFiniteType) SmoothCover.{u}) : f.FiniteType :=
  hasRepresentableProperty_of_cover_of_le _ FppfCover.{u} _ smoothCover_le_fppfCover hrep h

/-- Being a representable finite-presentation morphism descends along fppf covers. -/
theorem finitePresentation_of_fppfCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover
      (@SchQuasiCompact ⊓ @SchLocallyOfFinitePresentation) FppfCover.{u}) :
    f.FinitePresentation :=
  hasRepresentableProperty_of_cover _ _ hrep h

/-- Being a representable finite-presentation morphism descends along smooth covers. -/
theorem finitePresentation_of_smoothCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover
      (@SchQuasiCompact ⊓ @SchLocallyOfFinitePresentation) SmoothCover.{u}) :
    f.FinitePresentation :=
  hasRepresentableProperty_of_cover_of_le _ FppfCover.{u} _ smoothCover_le_fppfCover hrep h

/-! ### Zariski locality on the test schemes

These statements need no faithfully flat descent and therefore also cover the properties for
which Mathlib has no fppf-descent theorem yet. -/

/-- Representable flatness is local on the test schemes. -/
theorem flat_of_openCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnOpenCover @SchFlat) : f.Flat :=
  hasRepresentableProperty_of_openCover _ hrep h

/-- Representable quasi-compactness is local on the test schemes. -/
theorem quasiCompact_of_openCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnOpenCover @SchQuasiCompact) : f.QuasiCompact :=
  hasRepresentableProperty_of_openCover _ hrep h

/-- Representable separatedness is local on the test schemes. -/
theorem separated_of_openCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnOpenCover @SchIsSeparated) : f.Separated :=
  hasRepresentableProperty_of_openCover _ hrep h

/-- Representable properness is local on the test schemes. -/
theorem proper_of_openCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnOpenCover @SchIsProper) : f.Proper :=
  hasRepresentableProperty_of_openCover _ hrep h

/-- Being a representable immersion is local on the test schemes. -/
theorem immersion_of_openCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnOpenCover @SchIsImmersion) : f.Immersion :=
  hasRepresentableProperty_of_openCover _ hrep h

/-- Being a representable closed immersion is local on the test schemes. -/
theorem closedImmersion_of_openCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnOpenCover @SchIsClosedImmersion) : f.ClosedImmersion :=
  hasRepresentableProperty_of_openCover _ hrep h

/-- Being a representable finite-type morphism is local on the test schemes. -/
theorem finiteType_of_openCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnOpenCover (@SchQuasiCompact ⊓ @SchLocallyOfFiniteType)) :
    f.FiniteType :=
  hasRepresentableProperty_of_openCover _ hrep h

/-- Being a representable finite-presentation morphism is local on the test schemes. -/
theorem finitePresentation_of_openCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnOpenCover
      (@SchQuasiCompact ⊓ @SchLocallyOfFinitePresentation)) : f.FinitePresentation :=
  hasRepresentableProperty_of_openCover _ hrep h

end StackHom

namespace StackHom

variable {X Y Z : FppfStack.{u}}

/-! ### Compatibility of descent with the rest of the calculus -/

/-- The cover hypothesis itself is invariant under invertible 2-cells, since presentations
transport with unchanged representing scheme and structure map. -/
theorem hasRepresentablePropertyOnCover_congr {f g : StackHom X Y}
    (P Q : MorphismProperty Scheme.{u}) (e : StackIso2 f g) :
    f.HasRepresentablePropertyOnCover P Q ↔ g.HasRepresentablePropertyOnCover P Q := by
  constructor
  · intro h T y
    obtain ⟨S, base, hQ, q, hq⟩ := h T y
    exact ⟨S, base, hQ, StackMorphismPresentation.transport e.symm q, hq⟩
  · intro h T y
    obtain ⟨S, base, hQ, q, hq⟩ := h T y
    exact ⟨S, base, hQ, StackMorphismPresentation.transport e q, hq⟩

/-- Descent is compatible with composition: two morphisms satisfying the cover hypothesis have
a composite with the descended property. -/
theorem comp_hasRepresentableProperty_of_cover {f : StackHom X Y} {g : StackHom Y Z}
    (P Q : MorphismProperty Scheme.{u}) [MorphismProperty.DescendsAlong P Q]
    [P.IsStableUnderComposition] (hf : f.IsRepresentable) (hg : g.IsRepresentable)
    (hfc : f.HasRepresentablePropertyOnCover P Q)
    (hgc : g.HasRepresentablePropertyOnCover P Q) :
    HasRepresentableProperty (Pseudofunctor.StrongTrans.vcomp f g) P :=
  comp_hasRepresentableProperty P (hasRepresentableProperty_of_cover P Q hf hfc)
    (hasRepresentableProperty_of_cover P Q hg hgc)

/-- Descent is compatible with arbitrary genuine two-pullbacks: the second projection of any
genuine bicategorical pullback inherits the descended property. -/
theorem twoPullbackSnd_hasRepresentableProperty_of_cover {f : StackHom X Z} {g : StackHom Y Z}
    (W : StackTwoPullback.Genuine f g) (P Q : MorphismProperty Scheme.{u})
    [MorphismProperty.DescendsAlong P Q] [P.IsMultiplicative] (hf : f.IsRepresentable)
    (hfc : f.HasRepresentablePropertyOnCover P Q) :
    W.snd.HasRepresentableProperty P :=
  twoPullbackSnd_hasRepresentableProperty f g W P
    (hasRepresentableProperty_of_cover P Q hf hfc)

/-- Descent is compatible with equivalences of the source and target stacks. -/
theorem hasRepresentableProperty_of_cover_equivalence {X' Y' : FppfStack.{u}}
    (f : StackHom X Y) (f' : StackHom X' Y')
    (source : StackEquivalenceData X X') (target : StackEquivalenceData Y Y')
    (compatible : StackIso2 (Pseudofunctor.StrongTrans.vcomp source.hom f')
      (Pseudofunctor.StrongTrans.vcomp f target.hom))
    (P Q : MorphismProperty Scheme.{u}) [MorphismProperty.DescendsAlong P Q]
    [P.IsMultiplicative] (hf : f.IsRepresentable)
    (hfc : f.HasRepresentablePropertyOnCover P Q) : f'.HasRepresentableProperty P :=
  (hasRepresentableProperty_equivalence_iff f f' source target compatible P).1
    (hasRepresentableProperty_of_cover P Q hf hfc)

end StackHom

end GromovWitten.AlgebraicGeometry
