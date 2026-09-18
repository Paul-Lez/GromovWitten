/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.EmbeddingIndependence
import GromovWitten.AlgebraicGeometry.Cones.IntrinsicConeGluing

/-!
# The glued intrinsic normal cone of a family of presentations (polynomial model)

`Cones/EmbeddingIndependence.lean` proves that two polynomial presentations `A[x_σ] ↠ S` and
`A[x_{σ'}] ↠ S` of the same `A`-algebra `S = Γ(U)` have canonically equivalent quotient
groupoids `[C_{U/M}/T_M|_U](B)`, and that the comparison functors satisfy the Behrend–Fantechi
cocycle condition (`compareFunctor`, `liftIso`, `compareFunctorCompIso`, `cocycleIso`).
`Cones/IntrinsicConeGluing.lean` glues an abstract family of groupoids along such a cocycle.
This file puts the two together.

## The input data

`PresentationFamily A S ι` is the (hypothesis-free) datum of a family of polynomial
presentations of one affine scheme: variables `var i`, presentations
`pres i : A[x_{var i}] →ₐ[A] S`, and a chosen lift `lift i j : var j → A[x_{var i}]` of the
generators of the `j`-th presentation into the `i`-th one, with `lift_spec` saying that the
lifts are indeed lifts.  Every field is data or the defining property of the data; nothing is
assumed which the file then uses as a conclusion.

## The gluing datum and the glued groupoid

For a test algebra `B`, `P.fibre B i` is the quotient groupoid of the `i`-th presentation,
`P.transFunctor B i j` the comparison functor of the chosen lift, `P.unitIso B i` the
canonical isomorphism `transFunctor i i ≅ 𝟭` and `P.cocycleFunctorIso B i j k` the
Behrend–Fantechi cocycle isomorphism.  The two unit coherences and the tetrahedron identity
are **proved** (`transFunctor_map_unit`, `unit_transFunctor`, `tetrahedron_aux`), so

* `PresentationFamily.gluingData : GluingData (P.fibre B)`

is unconditional.  All three coherences reduce, through `ConeGroupoid.Hom.ext`, to identities
between tangent vectors `var l → B`, and these are consequences of the first-order comparison
`point_degreeOneRaw_sub` of two lifts (the chain rule for the Taylor derivation), of the
additivity of the degree-one class (`point_degreeOne_add`) and of the transport formula
`presMap_degreeOneRaw`.

`P.intrinsicCone B := Glue (P.gluingData B)` is the glued groupoid, and
`PresentationFamily.fibreEquivalence` states that **every single presentation computes it**:
the chart inclusion `P.fibre B i ⥤ P.intrinsicCone B` is an equivalence of groupoids.

## What is not here

Naturality in the test algebra is `PresentationFamily.restrictHom`: restriction of `B`-points
along a ring map `B →+* B'` (`restrictFunctor`) is a morphism of gluing data, so the glued
groupoids are the fibres of a prestack on test algebras.  Functoriality of `B ↦ restrictHom` is
not formalised (`GluingHom`s cannot yet be composed), so the result is a family of restriction
functors, not yet a pseudofunctor.

The charts of this file all present the *same* algebra `S`: this is the fibre of the intrinsic
normal cone over a point lying in all the charts, glued over all local embeddings of that
affine.  Varying the open subset (so that the `i`-th chart presents `Γ(U_i)` and the comparison
lives over `U_i ∩ U_j`) needs the localisation comparison of `Cones/SmoothAmbient.lean`, and is
not carried out here.  The fppf stackification is likewise left open.
-/

namespace GromovWitten.AlgebraicGeometry

namespace IntrinsicConeGluing

open CategoryTheory AffineNormalCone MvPolynomial ConeTranslation ConeRefinement
  EmbeddingIndependence GroupoidGluing

universe u

noncomputable section

/-! ### Degree-one classes: two computational lemmas -/

section Degree

variable {A : Type u} [CommRing A] {σ σ' : Type u} {I : Ideal (Amb A σ)}
  {B : Type u} [CommRing B]

/-- Two lifts which differ by elements of `I` induce the same map to the degree-zero part of a
`B`-point of `gr_I`. -/
theorem comp_algebraMap_liftHom_eq {h h' : σ' → Amb A σ} (hI : ∀ t, h' t - h t ∈ I)
    (φ : Gr I →+* B) :
    (φ.comp (algebraMap (Amb A σ) (Gr I))).comp (liftHom h) =
      (φ.comp (algebraMap (Amb A σ) (Gr I))).comp (liftHom h') := by
  refine RingHom.ext fun r ↦ ?_
  have hmem : liftHom h r - liftHom h' r ∈ I := by
    have hneg := neg_mem (liftHom_sub_mem hI r)
    rwa [neg_sub] at hneg
  simp only [RingHom.comp_apply]
  rw [← sub_eq_zero, ← map_sub, ← map_sub, algebraMap_gr_eq_zero I hmem, map_zero]

/-- A version of `point_degreeOneRaw_sub` in which the element of `I` whose degree-one class is
computed is given separately, together with the identification of it as a difference of lifts. -/
theorem point_degreeOne_of_eq {h h' : σ' → Amb A σ} (hI : ∀ t, h' t - h t ∈ I)
    (φ : Gr I →+* B) (f : Amb A σ') (a : Amb A σ) (ha : a ∈ I)
    (hfa : a = liftHom h' f - liftHom h f) :
    φ (degreeOneRaw (Amb A σ) I ⟨a, ha⟩) =
      eval₂ ((φ.comp (algebraMap (Amb A σ) (Gr I))).comp (liftHom h))
        (fun t ↦ φ (degreeOneRaw (Amb A σ) I ⟨h' t - h t, hI t⟩)) (taylor A σ' f) := by
  subst hfa
  exact point_degreeOneRaw_sub hI φ f ha

/-- The degree-one class at a `B`-point is additive. -/
theorem point_degreeOne_add (φ : Gr I →+* B) (a b : Amb A σ) (ha : a ∈ I) (hb : b ∈ I) :
    φ (degreeOneRaw (Amb A σ) I ⟨a, ha⟩) + φ (degreeOneRaw (Amb A σ) I ⟨b, hb⟩) =
      φ (degreeOneRaw (Amb A σ) I ⟨a + b, Ideal.add_mem _ ha hb⟩) := by
  rw [← map_add, ← map_add]
  rfl

end Degree

/-! ### Restriction along a map of test algebras -/

section Restrict

variable {A : Type u} [CommRing A] {σ σ' : Type u} {I : Ideal (Amb A σ)}
  {B B' : Type u} [CommRing B] [CommRing B']

/-- The tangent translation commutes with the restriction of `B`-points along `B →+* B'`. -/
theorem comp_translatePoint (f : B →+* B') (φ : Gr I →+* B) (v : σ → B) :
    f.comp (translatePoint I φ v) = translatePoint I (f.comp φ) (fun i ↦ f (v i)) := by
  refine ConeTranslation.gr_ringHom_ext I (fun r ↦ ?_) fun x ↦ ?_
  · rw [RingHom.comp_apply, translatePoint_algebraMap, translatePoint_algebraMap,
      RingHom.comp_apply]
  · rw [RingHom.comp_apply, translatePoint_degreeOne, translatePoint_degreeOne, map_add,
      RingHom.comp_apply, eval₂_comp_left]
    rfl

/-- **Restriction of the quotient groupoid along a map of test algebras.** -/
def restrictFunctor (I : Ideal (Amb A σ)) (f : B →+* B') :
    ConeGroupoid I B ⥤ ConeGroupoid I B' where
  obj x := ⟨f.comp x.point⟩
  map {_ _} g := ⟨fun i ↦ f (g.val i), by rw [← comp_translatePoint, g.translate_eq]⟩
  map_id x := ConeGroupoid.Hom.ext (funext fun _ ↦ map_zero f)
  map_comp g h := ConeGroupoid.Hom.ext (funext fun i ↦ map_add f (g.val i) (h.val i))

/-- The comparison of two presentations commutes with the restriction of test algebras. -/
theorem compareVec_comp_point (h : σ' → Amb A σ) (f : B →+* B') (φ : Gr I →+* B) (v : σ → B) :
    compareVec h (f.comp φ) (fun i ↦ f (v i)) = fun t ↦ f (compareVec h φ v t) := by
  funext t
  simp only [compareVec]
  rw [eval₂_comp_left]
  rfl

end Restrict

/-! ### Families of presentations -/

/-- **A family of polynomial presentations of one and the same affine scheme**, together with a
choice of lifts between them.  This is pure data: `var i` are the variables of the `i`-th
polynomial ring, `pres i` the `i`-th presentation `A[x_{var i}] ↠ S`, `lift i j` a chosen lift
of the generators of the `j`-th presentation into the `i`-th polynomial ring, and `lift_spec`
the statement that it is a lift. -/
structure PresentationFamily (A : Type u) [CommRing A] (S : Type u) [CommRing S] [Algebra A S]
    (ι : Type u) where
  /-- The variables of the `i`-th presentation. -/
  var : ι → Type u
  /-- The `i`-th presentation of `S`. -/
  pres : ∀ i, Amb A (var i) →ₐ[A] S
  /-- The chosen lift of the generators of the `j`-th presentation into the `i`-th one. -/
  lift : ∀ i j, var j → Amb A (var i)
  /-- The chosen lifts are lifts. -/
  lift_spec : ∀ i j t, pres i (lift i j t) = pres j (X t)

namespace PresentationFamily

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S] {ι : Type u}
  (P : PresentationFamily A S ι) (B : Type u) [CommRing B]

/-- The quotient groupoid `[C_{U/M_i}/T_{M_i}|_U](B)` of the `i`-th presentation. -/
abbrev fibre (i : ι) : Type u := ConeGroupoid (presIdeal (P.pres i)) B

variable {B}

/-- The composite of two chosen lifts is again a lift. -/
theorem lift_comp_spec (i j k : ι) (t : P.var k) :
    P.pres i (liftHom (P.lift i j) (P.lift j k t)) = P.pres k (X t) := by
  rw [liftHom_apply_eq (P.lift_spec i j), P.lift_spec j k]

/-- The chosen lift `i → k` differs from the composite of the chosen lifts `i → j → k` by an
element of the ideal of the `i`-th presentation. -/
theorem cocycle_mem (i j k : ι) (t : P.var k) :
    P.lift i k t - liftHom (P.lift i j) (P.lift j k t) ∈ presIdeal (P.pres i) :=
  lift_sub_mem_presIdeal (P.lift_comp_spec i j k) (P.lift_spec i k) t

/-- The chosen lift of a chart into itself differs from the identity by an element of the ideal
of the presentation. -/
theorem unit_mem (i : ι) (t : P.var i) :
    (X t : Amb A (P.var i)) - P.lift i i t ∈ presIdeal (P.pres i) :=
  lift_sub_mem_presIdeal (P.lift_spec i i) (fun _ ↦ rfl) t

variable (B)

/-- The comparison functor between the quotient groupoids of two presentations of the family. -/
def transFunctor (i j : ι) : P.fibre B i ⥤ P.fibre B j :=
  compareFunctor (presIdeal (P.pres i)) (presIdeal (P.pres j)) (P.lift i j)
    (map_liftHom_presIdeal_le (P.lift_spec i j)) B

/-- The tangent vector comparing the chosen lift of a chart into itself with the identity. -/
def unitVec (i : ι) (x : P.fibre B i) : P.var i → B :=
  fun t ↦ x.point (degreeOneRaw (Amb A (P.var i)) (presIdeal (P.pres i))
    ⟨X t - P.lift i i t, P.unit_mem i t⟩)

/-- The tangent vector comparing the chosen lift `i → k` with the composite `i → j → k`. -/
def cocycleVec (i j k : ι) (x : P.fibre B i) : P.var k → B :=
  fun t ↦ x.point (degreeOneRaw (Amb A (P.var i)) (presIdeal (P.pres i))
    ⟨P.lift i k t - liftHom (P.lift i j) (P.lift j k t), P.cocycle_mem i j k t⟩)

/-- The comparison functor of a chart with itself is canonically isomorphic to the identity. -/
def unitIso (i : ι) : P.transFunctor B i i ≅ 𝟭 (P.fibre B i) :=
  presentationLiftIso (P.lift_spec i i) (fun _ ↦ rfl) B ≪≫ presentationIdIso B

/-- The Behrend–Fantechi cocycle isomorphism of the family. -/
def cocycleFunctorIso (i j k : ι) :
    P.transFunctor B i j ⋙ P.transFunctor B j k ≅ P.transFunctor B i k :=
  cocycleIso (P.lift_spec i j) (P.lift_spec j k) (P.lift_spec i k) B

theorem transFunctor_obj_point (i j : ι) (x : P.fibre B i) :
    ((P.transFunctor B i j).obj x).point =
      x.point.comp (presMap (presIdeal (P.pres i)) (presIdeal (P.pres j)) (P.lift i j)
        (map_liftHom_presIdeal_le (P.lift_spec i j))) :=
  rfl

theorem transFunctor_map_val (i j : ι) {x y : P.fibre B i} (f : x ⟶ y) :
    ((P.transFunctor B i j).map f).val = compareVec (P.lift i j) x.point f.val :=
  rfl

theorem unitIso_hom_app_val (i : ι) (x : P.fibre B i) :
    ((P.unitIso B i).hom.app x).val = P.unitVec B i x := by
  change P.unitVec B i x + 0 = _
  rw [add_zero]

theorem cocycleFunctorIso_hom_app_val (i j k : ι) (x : P.fibre B i) :
    ((P.cocycleFunctorIso B i j k).hom.app x).val = P.cocycleVec B i j k x := by
  change (0 : P.var k → B) + P.cocycleVec B i j k x = _
  rw [zero_add]

/-! ### The coherences -/

/-- The degree-zero part of a `B`-point transported to another chart. -/
theorem comp_algebraMap_transFunctor (i j : ι) (x : P.fibre B i) :
    ((P.transFunctor B i j).obj x).point.comp
        (algebraMap (Amb A (P.var j)) (Gr (presIdeal (P.pres j)))) =
      (x.point.comp (algebraMap (Amb A (P.var i)) (Gr (presIdeal (P.pres i))))).comp
        (liftHom (P.lift i j)) := by
  refine RingHom.ext fun r ↦ ?_
  rw [RingHom.comp_apply, P.transFunctor_obj_point, RingHom.comp_apply, presMap_algebraMap,
    RingHom.comp_apply, RingHom.comp_apply]

/-- **The first unit coherence.** -/
theorem transFunctor_map_unit (i j : ι) (x : P.fibre B i) :
    (P.transFunctor B i j).map ((P.unitIso B i).hom.app x) =
      (P.cocycleFunctorIso B i i j).hom.app x := by
  refine ConeGroupoid.Hom.ext ?_
  rw [P.transFunctor_map_val, P.unitIso_hom_app_val, P.cocycleFunctorIso_hom_app_val]
  refine funext fun t ↦ ?_
  have key := point_degreeOne_of_eq (P.unit_mem i) x.point (P.lift i j t)
    (P.lift i j t - liftHom (P.lift i i) (P.lift i j t)) (P.cocycle_mem i i j t)
    (by rw [liftHom_id, RingHom.id_apply])
  rw [← P.comp_algebraMap_transFunctor B i i x] at key
  exact key.symm

/-- **The second unit coherence.** -/
theorem unit_transFunctor (i j : ι) (x : P.fibre B i) :
    (P.unitIso B j).hom.app ((P.transFunctor B i j).obj x) =
      (P.cocycleFunctorIso B i j j).hom.app x := by
  refine ConeGroupoid.Hom.ext ?_
  rw [P.unitIso_hom_app_val, P.cocycleFunctorIso_hom_app_val]
  refine funext fun t ↦ ?_
  change ((P.transFunctor B i j).obj x).point (degreeOneRaw (Amb A (P.var j))
    (presIdeal (P.pres j)) ⟨X t - P.lift j j t, P.unit_mem j t⟩) = _
  rw [P.transFunctor_obj_point, RingHom.comp_apply, presMap_degreeOneRaw]
  refine congrArg x.point (congrArg _ (Subtype.ext ?_))
  change liftHom (P.lift i j) (X t - P.lift j j t) =
    P.lift i j t - liftHom (P.lift i j) (P.lift j j t)
  rw [map_sub, liftHom_X]

/-- The degree-zero part of a `B`-point of the doubly transported chart. -/
theorem comp_algebraMap_trans (i j k : ι) (x : P.fibre B i) :
    (((P.transFunctor B i j ⋙ P.transFunctor B j k).obj x).point.comp
        (algebraMap (Amb A (P.var k)) (Gr (presIdeal (P.pres k))))) =
      (x.point.comp (algebraMap (Amb A (P.var i)) (Gr (presIdeal (P.pres i))))).comp
        (liftHom fun s ↦ liftHom (P.lift i j) (P.lift j k s)) := by
  refine RingHom.ext fun r ↦ ?_
  change ((P.transFunctor B j k).obj ((P.transFunctor B i j).obj x)).point
    (algebraMap (Amb A (P.var k)) (Gr (presIdeal (P.pres k))) r) = _
  rw [P.transFunctor_obj_point, RingHom.comp_apply, presMap_algebraMap,
    P.transFunctor_obj_point, RingHom.comp_apply, presMap_algebraMap, RingHom.comp_apply,
    RingHom.comp_apply, liftHom_comp, RingHom.comp_apply]

/-- **The tetrahedron identity** for the cocycle isomorphisms of a family of presentations. -/
theorem tetrahedron_aux (i j k l : ι) (x : P.fibre B i) :
    (P.transFunctor B k l).map ((P.cocycleFunctorIso B i j k).hom.app x) ≫
        (P.cocycleFunctorIso B i k l).hom.app x =
      (P.cocycleFunctorIso B j k l).hom.app ((P.transFunctor B i j).obj x) ≫
        (P.cocycleFunctorIso B i j l).hom.app x := by
  refine ConeGroupoid.Hom.ext ?_
  rw [ConeGroupoid.comp_val, ConeGroupoid.comp_val, P.transFunctor_map_val,
    P.cocycleFunctorIso_hom_app_val, P.cocycleFunctorIso_hom_app_val,
    P.cocycleFunctorIso_hom_app_val, P.cocycleFunctorIso_hom_app_val]
  refine funext fun t ↦ ?_
  have hleft : compareVec (P.lift k l)
      ((P.transFunctor B i j ⋙ P.transFunctor B j k).obj x).point
      (P.cocycleVec B i j k x) t =
      x.point (degreeOneRaw (Amb A (P.var i)) (presIdeal (P.pres i))
        ⟨liftHom (P.lift i k) (P.lift k l t) -
          liftHom (fun s ↦ liftHom (P.lift i j) (P.lift j k s)) (P.lift k l t),
          liftHom_sub_mem (P.cocycle_mem i j k) (P.lift k l t)⟩) := by
    simp only [compareVec]
    rw [P.comp_algebraMap_trans B i j k x]
    exact (point_degreeOne_of_eq (P.cocycle_mem i j k) x.point (P.lift k l t) _
      (liftHom_sub_mem (P.cocycle_mem i j k) (P.lift k l t)) rfl).symm
  have hright : P.cocycleVec B j k l ((P.transFunctor B i j).obj x) t =
      x.point (degreeOneRaw (Amb A (P.var i)) (presIdeal (P.pres i))
        ⟨liftHom (P.lift i j)
            (P.lift j l t - liftHom (P.lift j k) (P.lift k l t)),
          map_liftHom_presIdeal_le (P.lift_spec i j)
            (Ideal.mem_map_of_mem _ (P.cocycle_mem j k l t))⟩) := by
    change ((P.transFunctor B i j).obj x).point (degreeOneRaw (Amb A (P.var j))
      (presIdeal (P.pres j)) ⟨P.lift j l t - liftHom (P.lift j k) (P.lift k l t),
        P.cocycle_mem j k l t⟩) = _
    rw [P.transFunctor_obj_point, RingHom.comp_apply, presMap_degreeOneRaw]
  rw [Pi.add_apply, Pi.add_apply, hleft, hright]
  change _ + x.point (degreeOneRaw (Amb A (P.var i)) (presIdeal (P.pres i))
      ⟨P.lift i l t - liftHom (P.lift i k) (P.lift k l t), P.cocycle_mem i k l t⟩) =
    _ + x.point (degreeOneRaw (Amb A (P.var i)) (presIdeal (P.pres i))
      ⟨P.lift i l t - liftHom (P.lift i j) (P.lift j l t), P.cocycle_mem i j l t⟩)
  rw [point_degreeOne_add, point_degreeOne_add]
  refine congrArg x.point (congrArg _ (Subtype.ext ?_))
  change liftHom (P.lift i k) (P.lift k l t) -
      liftHom (fun s ↦ liftHom (P.lift i j) (P.lift j k s)) (P.lift k l t) +
      (P.lift i l t - liftHom (P.lift i k) (P.lift k l t)) =
    liftHom (P.lift i j) (P.lift j l t - liftHom (P.lift j k) (P.lift k l t)) +
      (P.lift i l t - liftHom (P.lift i j) (P.lift j l t))
  rw [map_sub, liftHom_comp, RingHom.comp_apply]
  ring

/-! ### The glued groupoid -/

/-- **The gluing datum of a family of presentations.**  All coherences are theorems. -/
def gluingData : GluingData (P.fibre B) where
  trans := P.transFunctor B
  unit := P.unitIso B
  cocycle := P.cocycleFunctorIso B
  cocycle_unit_left := P.transFunctor_map_unit B
  cocycle_unit_right := P.unit_transFunctor B
  tetrahedron := P.tetrahedron_aux B

/-- **The glued intrinsic quotient groupoid** of a family of presentations: the `B`-points of
the intrinsic normal cone stack, glued from all the local presentations at once. -/
abbrev intrinsicCone : Type u := Glue (P.gluingData B)

/-- **Every presentation computes the glued groupoid.** -/
theorem inc_isEquivalence (i : ι) : (Glue.inc (P.gluingData B) i).IsEquivalence :=
  Glue.inc_isEquivalence _ i

/-- The equivalence between the quotient groupoid of any one presentation and the glued
intrinsic quotient groupoid. -/
def fibreEquivalence (i : ι) : P.fibre B i ≌ P.intrinsicCone B :=
  Glue.incEquivalence (P.gluingData B) i

/-- The comparison functor of two presentations of the family is an equivalence, recovered from
the gluing datum. -/
def transEquivalence (i j : ι) : P.fibre B i ≌ P.fibre B j :=
  (P.gluingData B).transEquivalence i j

/-- **Restriction along a map of test algebras is a morphism of gluing data**, so that the glued
groupoids form a prestack on the test algebras. -/
def restrictHom {B' : Type u} [CommRing B'] (f : B →+* B') :
    GluingHom (P.gluingData B) (P.gluingData B') where
  map i := restrictFunctor (presIdeal (P.pres i)) f
  commIso i j := NatIso.ofComponents (fun _ ↦ CategoryTheory.Iso.refl _) (fun {x _} g ↦ by
    refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    exact ConeGroupoid.Hom.ext (compareVec_comp_point (P.lift i j) f x.point g.val))
  commIso_unit i x := ConeGroupoid.Hom.ext (funext fun t ↦ by
    change (0 : B') + f (P.unitVec B i x t + 0) = f (P.unitVec B i x t) + 0
    rw [add_zero, add_zero, zero_add])
  commIso_cocycle i j k x := ConeGroupoid.Hom.ext (funext fun t ↦ by
    have hz : compareVec (P.lift j k)
        ((P.transFunctor B' i j).obj ((restrictFunctor (presIdeal (P.pres i)) f).obj x)).point
        (0 : P.var j → B') = 0 := compareVec_zero _
    change -f (P.cocycleVec B i j k x t) + -(0 : B') +
        (compareVec (P.lift j k)
            ((P.transFunctor B' i j).obj ((restrictFunctor (presIdeal (P.pres i)) f).obj x)).point
            (0 : P.var j → B') t + (0 : B')) =
      (0 : B') + f (-P.cocycleVec B i j k x t + -(0 : B))
    rw [hz, Pi.zero_apply, map_add, map_neg, map_neg, map_zero]
    ring)

end PresentationFamily

end

end IntrinsicConeGluing

end GromovWitten.AlgebraicGeometry
