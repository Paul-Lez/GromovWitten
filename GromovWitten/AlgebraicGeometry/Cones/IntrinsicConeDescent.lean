/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.IntrinsicConeGluingCover
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Zariski descent of the cone groupoid in the test algebra

Fix the polynomial model `P = Amb A σ = A[x_i]`, an ideal `I` of `P`, and a test algebra `B`.
`ConeRefinement.ConeGroupoid I B` is the groupoid of `B`-points of the quotient stack
`[C_{U/M}/T_M|_U]` of `Cones/RefinementQuotient.lean`.  This file proves that this groupoid is a
**Zariski stack in the test algebra**: it can be computed from a Zariski cover of `Spec B`.

## The affine sheaf condition

A cover is a set `s : Set B` with `Ideal.span s = ⊤`; the corresponding charts are the
localisations `B_a = Localization.Away a` for `a ∈ s`, and the overlaps are `B_{ab}` and
`B_{abc}`.  `ConeDescent.awayRes` is the restriction map `B_g → B_h` for `g ∣ h` (the unique map
of `B`-algebras, by `ConeDescent.eq_awayRes`), and `resL`, `resR`, `res₁₂`, `res₂₃`, `res₁₃` are
the restrictions to the double and triple overlaps.  `ConeDescent.eq_of_span_eq_top` is the
separatedness of the cover and `ConeDescent.existsUnique_glue` the sheaf condition (deduced from
`Localization.existsUnique_algebraMap_eq_of_span_eq_top`), with the two corollaries
`ConeDescent.exists_glue_vec` (gluing tangent vectors) and `ConeDescent.exists_glue_ringHom`
(gluing points of the cone).

## The descent groupoid and the comparison functor

`ConeDescent.DescentGroupoid I s` is the groupoid of descent data: a `B_a`-point `chart a` of the
affine normal cone for every `a ∈ s`, a tangent vector `vec a b : σ → B_{ab}` carrying the first
restricted point to the second (`translate_eq`), and the cocycle condition over the triple
overlaps.  Morphisms are families of tangent vectors on the charts compatible with the `vec a b`;
`instCategory` and `instGroupoid` prove that this is a groupoid.  `ConeDescent.toDescent` is the
comparison functor, restricting a `B`-point to every chart and gluing by the zero vector.

## The descent theorem

`ConeDescent.toDescent_faithful` and `ConeDescent.toDescent_full` are the two halves of full
faithfulness, both consequences of the sheaf condition for tangent vectors.
`ConeDescent.exists_eq_toDescentObj` is essential surjectivity for descent data with vanishing
identifying vectors, and it is *exact*: such a datum is the image of a `B`-point on the nose.
For the general case the identifying vectors have to be trivialised, which is the vanishing of
`H¹(Spec B, 𝒪^σ)`; it is isolated as the predicate `ConeDescent.CechVanishing` and *proved* for
finite covers in `ConeDescent.exists_sub_eq_of_cocycle` and `ConeDescent.cechVanishing_of_finite`
by the classical clearing-of-denominators argument.  `ConeDescent.untwist` and
`ConeDescent.untwistHom` turn a Čech primitive into an isomorphism with a datum with vanishing
identifying vectors, whence `ConeDescent.toDescent_essSurj`, and finally
`ConeDescent.toDescent_isEquivalence_of_finite` and `ConeDescent.descentEquivalence`:
for a finite cover the comparison functor is an equivalence, unconditionally.

## What is not here

The cover is a cover of the *test algebra*, not of the ambient space (that is
`Cones/IntrinsicConeGluingCover.lean`).  Čech vanishing is proved only for finite covers, so the
descent theorem is stated for finite covers; for an infinite cover the general theorem
`ConeDescent.toDescent_isEquivalence` still needs `ConeDescent.CechVanishing` as a hypothesis.
There is no fppf or étale descent here, and no comparison with `Cones/Stack.lean`.
-/

namespace GromovWitten.AlgebraicGeometry

namespace ConeDescent

universe u

/-! ### Restriction maps between localisations away from an element -/

section Localisation

variable {B : Type u} [CommRing B]

/-- The restriction map `B_g → B_h` between two localisations of `B`, available whenever `g`
divides `h` (so that `g` is invertible in `B_h`). -/
noncomputable def awayRes (g h : B) (hgh : g ∣ h) :
    Localization.Away g →+* Localization.Away h :=
  IsLocalization.Away.lift (g := algebraMap B (Localization.Away h)) g
    (IsLocalization.Away.isUnit_of_dvd (S := Localization.Away h) h hgh)

@[simp]
theorem awayRes_algebraMap (g h : B) (hgh : g ∣ h) (b : B) :
    awayRes g h hgh (algebraMap B (Localization.Away g) b) =
      algebraMap B (Localization.Away h) b :=
  IsLocalization.Away.lift_eq _ _ _

/-- The restriction map is a map of `B`-algebras. -/
theorem awayRes_comp_algebraMap (g h : B) (hgh : g ∣ h) :
    (awayRes g h hgh).comp (algebraMap B (Localization.Away g)) =
      algebraMap B (Localization.Away h) :=
  RingHom.ext fun b ↦ awayRes_algebraMap g h hgh b

/-- The restriction map is the unique map of `B`-algebras `B_g → B_h`. -/
theorem eq_awayRes (g h : B) (hgh : g ∣ h) (φ : Localization.Away g →+* Localization.Away h)
    (hφ : ∀ b : B, φ (algebraMap B (Localization.Away g) b) =
      algebraMap B (Localization.Away h) b) : φ = awayRes g h hgh :=
  IsLocalization.ringHom_ext (Submonoid.powers g)
    (RingHom.ext fun b ↦ (hφ b).trans (awayRes_algebraMap g h hgh b).symm)

/-- Restriction `B_g → B_{gh}` from the first factor. -/
noncomputable def resL (g h : B) : Localization.Away g →+* Localization.Away (g * h) :=
  awayRes g (g * h) (dvd_mul_right g h)

/-- Restriction `B_h → B_{gh}` from the second factor. -/
noncomputable def resR (g h : B) : Localization.Away h →+* Localization.Away (g * h) :=
  awayRes h (g * h) (dvd_mul_left h g)

@[simp]
theorem resL_algebraMap (g h : B) (b : B) :
    resL g h (algebraMap B (Localization.Away g) b) =
      algebraMap B (Localization.Away (g * h)) b :=
  awayRes_algebraMap _ _ _ b

@[simp]
theorem resR_algebraMap (g h : B) (b : B) :
    resR g h (algebraMap B (Localization.Away h) b) =
      algebraMap B (Localization.Away (g * h)) b :=
  awayRes_algebraMap _ _ _ b

/-- Restriction `B_{gh} → B_{ghk}` to a triple overlap. -/
noncomputable def res₁₂ (g h k : B) :
    Localization.Away (g * h) →+* Localization.Away (g * h * k) :=
  awayRes _ _ (dvd_mul_right (g * h) k)

/-- Restriction `B_{hk} → B_{ghk}` to a triple overlap. -/
noncomputable def res₂₃ (g h k : B) :
    Localization.Away (h * k) →+* Localization.Away (g * h * k) :=
  awayRes _ _ ⟨g, by ring⟩

/-- Restriction `B_{gk} → B_{ghk}` to a triple overlap. -/
noncomputable def res₁₃ (g h k : B) :
    Localization.Away (g * k) →+* Localization.Away (g * h * k) :=
  awayRes _ _ ⟨h, by ring⟩

/-! ### The Zariski equaliser -/

variable (s : Set B)

/-- **Separatedness of the Zariski topology on an affine scheme.**  An element of `B` is
determined by its images in the localisations `B_a` for `a` ranging over a set of generators of
the unit ideal. -/
theorem eq_of_span_eq_top (hs : Ideal.span s = ⊤) {u v : B}
    (h : ∀ a : s, algebraMap B (Localization.Away (a : B)) u =
      algebraMap B (Localization.Away (a : B)) v) : u = v := by
  have key : ∀ a : s, ∃ n : ℕ, (a : B) ^ n * u = (a : B) ^ n * v := by
    intro a
    obtain ⟨⟨c, n, hn⟩, hc⟩ :=
      (IsLocalization.eq_iff_exists (Submonoid.powers (a : B))
        (Localization.Away (a : B))).1 (h a)
    exact ⟨n, by rw [show (a : B) ^ n = c from hn]; exact hc⟩
  choose n hn using key
  have htop : Ideal.span (Set.range fun a : s ↦ (a : B) ^ n a) = ⊤ :=
    Ideal.span_range_pow_eq_top s hs n
  have hzero : ∀ r ∈ Ideal.span (Set.range fun a : s ↦ (a : B) ^ n a), r * (u - v) = 0 := by
    intro r hr
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hr
    · rintro x ⟨a, rfl⟩
      rw [mul_sub, hn a, sub_self]
    · rw [zero_mul]
    · intro x y _ _ hx hy
      rw [add_mul, hx, hy, add_zero]
    · intro c x _ hx
      rw [smul_eq_mul, mul_assoc, hx, mul_zero]
  have h1 : (1 : B) ∈ Ideal.span (Set.range fun a : s ↦ (a : B) ^ n a) := by
    rw [htop]; trivial
  have := hzero 1 h1
  rw [one_mul, sub_eq_zero] at this
  exact this

/-- **The sheaf condition for the structure sheaf of an affine scheme**, in the form of the
equaliser `B → ∏ B_a ⇉ ∏ B_{ab}`: a family of sections over a cover by basic opens which agree
on the overlaps comes from a unique element of `B`. -/
theorem existsUnique_glue (hs : Ideal.span s = ⊤)
    (c : ∀ a : s, Localization.Away (a : B))
    (hc : ∀ a b : s, resL (a : B) (b : B) (c a) = resR (a : B) (b : B) (c b)) :
    ∃! u : B, ∀ a : s, algebraMap B (Localization.Away (a : B)) u = c a := by
  refine Localization.existsUnique_algebraMap_eq_of_span_eq_top s hs c fun a b ↦ ?_
  have h1 : IsLocalization.Away.awayToAwayRight (P := Localization.Away ((a : B) * (b : B)))
      (a : B) (b : B) = resL (a : B) (b : B) :=
    eq_awayRes _ _ _ _ fun x ↦ IsLocalization.Away.awayToAwayRight_eq _ _ x
  have h2 : IsLocalization.Away.awayToAwayLeft (P := Localization.Away ((a : B) * (b : B)))
      (b : B) (a : B) = resR (a : B) (b : B) :=
    eq_awayRes _ _ _ _ fun x ↦ IsLocalization.Away.awayToAwayLeft_eq _ _ x
  rw [DFunLike.congr_fun h1 (c a), DFunLike.congr_fun h2 (c b)]
  exact hc a b

/-- Gluing a compatible family of tangent vectors over a Zariski cover of the test algebra. -/
theorem exists_glue_vec {σ : Type u} (hs : Ideal.span s = ⊤)
    (c : ∀ a : s, σ → Localization.Away (a : B))
    (hc : ∀ (a b : s) (i : σ), resL (a : B) (b : B) (c a i) = resR (a : B) (b : B) (c b i)) :
    ∃ v : σ → B, ∀ (a : s) (i : σ),
      algebraMap B (Localization.Away (a : B)) (v i) = c a i := by
  choose v hv _ using fun i : σ ↦ existsUnique_glue s hs (fun a ↦ c a i) fun a b ↦ hc a b i
  exact ⟨v, fun a i ↦ hv i a⟩

/-- Gluing a compatible family of ring maps over a Zariski cover of the test algebra. -/
theorem exists_glue_ringHom {T : Type u} [CommRing T] (hs : Ideal.span s = ⊤)
    (φ : ∀ a : s, T →+* Localization.Away (a : B))
    (hφ : ∀ (a b : s) (t : T),
      resL (a : B) (b : B) (φ a t) = resR (a : B) (b : B) (φ b t)) :
    ∃ ψ : T →+* B, ∀ a : s,
      (algebraMap B (Localization.Away (a : B))).comp ψ = φ a := by
  choose ψ hψ _ using fun t : T ↦ existsUnique_glue s hs (fun a ↦ φ a t) fun a b ↦ hφ a b t
  refine ⟨{ toFun := ψ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ },
    fun a ↦ RingHom.ext fun t ↦ hψ t a⟩
  · refine eq_of_span_eq_top s hs fun a ↦ ?_
    rw [hψ 1 a, map_one, map_one]
  · intro x y
    refine eq_of_span_eq_top s hs fun a ↦ ?_
    rw [hψ (x * y) a, map_mul, map_mul, hψ x a, hψ y a]
  · refine eq_of_span_eq_top s hs fun a ↦ ?_
    rw [hψ 0 a, map_zero, map_zero]
  · intro x y
    refine eq_of_span_eq_top s hs fun a ↦ ?_
    rw [hψ (x + y) a, map_add, map_add, hψ x a, hψ y a]

end Localisation

/-! ### The descent groupoid -/

section Descent

open CategoryTheory ConeTranslation ConeRefinement

variable {A : Type u} [CommRing A] {σ : Type u} (I : Ideal (Amb A σ))
  {B : Type u} [CommRing B] (s : Set B)

/-- **Descent data for the cone groupoid along a Zariski cover of the test algebra.**  A family
of `B_a`-points of `[C_{U/M}/T_M|_U]`, one for each element `a` of a generating set `s` of the
unit ideal of `B`, together with tangent vectors over the overlaps identifying them, subject to
the cocycle condition over the triple overlaps. -/
structure DescentGroupoid where
  /-- The `B_a`-point of the affine normal cone on the chart `a`. -/
  chart : ∀ a : s, Gr I →+* Localization.Away (a : B)
  /-- The tangent vector identifying the two charts over the overlap `B_{ab}`. -/
  vec : ∀ a b : s, σ → Localization.Away ((a : B) * (b : B))
  /-- The identifying vector really carries the first restricted point to the second one. -/
  translate_eq : ∀ a b : s,
    translatePoint I ((resL (a : B) (b : B)).comp (chart a)) (vec a b) =
      (resR (a : B) (b : B)).comp (chart b)
  /-- The cocycle condition over the triple overlaps `B_{abc}`. -/
  cocycle : ∀ (a b c : s) (i : σ),
    res₁₂ (a : B) (b : B) (c : B) (vec a b i) + res₂₃ (a : B) (b : B) (c : B) (vec b c i) =
      res₁₃ (a : B) (b : B) (c : B) (vec a c i)

namespace DescentGroupoid

variable {I s}

/-- Extensionality for descent data. -/
theorem ext' {x y : DescentGroupoid I s} (hchart : x.chart = y.chart) (hvec : x.vec = y.vec) :
    x = y := by
  cases x; cases y; subst hchart; subst hvec; rfl

/-- A morphism of descent data: a tangent vector on every chart, carrying the source point to
the target point and compatible with the identifying vectors over the overlaps. -/
@[ext]
structure Hom (x y : DescentGroupoid I s) where
  /-- The translating tangent vector on each chart. -/
  val : ∀ a : s, σ → Localization.Away (a : B)
  /-- It carries the source point to the target point on every chart. -/
  translate_eq : ∀ a : s, translatePoint I (x.chart a) (val a) = y.chart a
  /-- It is compatible with the identifying vectors over the overlaps. -/
  compat : ∀ (a b : s) (i : σ),
    resL (a : B) (b : B) (val a i) + y.vec a b i =
      x.vec a b i + resR (a : B) (b : B) (val b i)

/-- Descent data for the cone groupoid form a category. -/
instance instCategory : Category (DescentGroupoid I s) where
  Hom := Hom
  id x :=
    { val := 0
      translate_eq := fun a ↦ translatePoint_zero I (x.chart a)
      compat := fun a b i ↦ by
        change resL (a : B) (b : B) 0 + x.vec a b i = x.vec a b i + resR (a : B) (b : B) 0
        rw [map_zero, map_zero, zero_add, add_zero] }
  comp {x y z} f g :=
    { val := f.val + g.val
      translate_eq := fun a ↦ by
        change translatePoint I (x.chart a) (f.val a + g.val a) = z.chart a
        rw [← translatePoint_add, f.translate_eq a, g.translate_eq a]
      compat := fun a b i ↦ by
        change resL (a : B) (b : B) (f.val a i + g.val a i) + z.vec a b i =
          x.vec a b i + resR (a : B) (b : B) (f.val b i + g.val b i)
        rw [map_add, map_add]
        linear_combination f.compat a b i + g.compat a b i }
  id_comp f := Hom.ext (zero_add _)
  comp_id f := Hom.ext (add_zero _)
  assoc f g h := Hom.ext (add_assoc _ _ _)

@[simp]
theorem id_val (x : DescentGroupoid I s) : (𝟙 x : x ⟶ x).val = 0 :=
  rfl

@[simp]
theorem comp_val {x y z : DescentGroupoid I s} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).val = f.val + g.val :=
  rfl

/-- Descent data for the cone groupoid form a groupoid. -/
instance instGroupoid : Groupoid (DescentGroupoid I s) where
  inv {x y} f :=
    { val := -f.val
      translate_eq := fun a ↦ by
        change translatePoint I (y.chart a) (-f.val a) = x.chart a
        rw [← f.translate_eq a, translatePoint_add, add_neg_cancel, translatePoint_zero]
      compat := fun a b i ↦ by
        change resL (a : B) (b : B) (-f.val a i) + x.vec a b i =
          y.vec a b i + resR (a : B) (b : B) (-f.val b i)
        rw [map_neg, map_neg]
        linear_combination -f.compat a b i }
  inv_comp f := Hom.ext (neg_add_cancel _)
  comp_inv f := Hom.ext (add_neg_cancel _)

end DescentGroupoid

/-! ### The comparison functor -/

/-- The descent datum attached to a `B`-point of the cone groupoid: restrict it to every chart
of the cover and identify the restrictions by the zero tangent vector. -/
noncomputable def toDescentObj (x : ConeGroupoid I B) : DescentGroupoid I s where
  chart a := (algebraMap B (Localization.Away (a : B))).comp x.point
  vec _ _ := 0
  translate_eq a b := by
    rw [translatePoint_zero]
    refine RingHom.ext fun z ↦ ?_
    simp only [RingHom.comp_apply, resL_algebraMap, resR_algebraMap]
  cocycle a b c i := by
    change res₁₂ (a : B) (b : B) (c : B) 0 + res₂₃ (a : B) (b : B) (c : B) 0 =
      res₁₃ (a : B) (b : B) (c : B) 0
    rw [map_zero, map_zero, map_zero, zero_add]

@[simp]
theorem toDescentObj_chart (x : ConeGroupoid I B) (a : s) :
    (toDescentObj I s x).chart a = (algebraMap B (Localization.Away (a : B))).comp x.point :=
  rfl

@[simp]
theorem toDescentObj_vec (x : ConeGroupoid I B) : (toDescentObj I s x).vec = 0 :=
  rfl

/-- The restriction of a morphism of the cone groupoid to the charts of the cover. -/
noncomputable def toDescentMap {x y : ConeGroupoid I B} (f : x ⟶ y) :
    toDescentObj I s x ⟶ toDescentObj I s y where
  val a i := algebraMap B (Localization.Away (a : B)) (f.val i)
  translate_eq a := by
    change translatePoint I ((algebraMap B (Localization.Away (a : B))).comp x.point) _ = _
    rw [← IntrinsicConeGluing.comp_translatePoint, f.translate_eq]
    rfl
  compat a b i := by
    change resL (a : B) (b : B) (algebraMap B _ (f.val i)) + 0 =
      0 + resR (a : B) (b : B) (algebraMap B _ (f.val i))
    rw [resL_algebraMap, resR_algebraMap, add_zero, zero_add]

/-- **The comparison functor** from the `B`-points of `[C_{U/M}/T_M|_U]` to descent data along a
Zariski cover of the test algebra `B`. -/
noncomputable def toDescent : ConeGroupoid I B ⥤ DescentGroupoid I s where
  obj := toDescentObj I s
  map := toDescentMap I s
  map_id _ := DescentGroupoid.Hom.ext (funext fun _ ↦ funext fun _ ↦ map_zero _)
  map_comp _ _ := DescentGroupoid.Hom.ext (funext fun _ ↦ funext fun _ ↦ map_add _ _ _)

@[simp]
theorem toDescent_map_val {x y : ConeGroupoid I B} (f : x ⟶ y) (a : s) (i : σ) :
    ((toDescent I s).map f).val a i = algebraMap B (Localization.Away (a : B)) (f.val i) :=
  rfl

end Descent

/-! ### Full faithfulness of the comparison functor -/

section FullyFaithful

open CategoryTheory ConeTranslation ConeRefinement

variable {A : Type u} [CommRing A] {σ : Type u} (I : Ideal (Amb A σ))
  {B : Type u} [CommRing B] (s : Set B)

/-- **The comparison functor is faithful**: a tangent vector over `B` is determined by its
restrictions to the charts of a Zariski cover. -/
theorem toDescent_faithful (hs : Ideal.span s = ⊤) : (toDescent I s).Faithful where
  map_injective {_ _} _ _ h :=
    ConeGroupoid.Hom.ext (funext fun i ↦ eq_of_span_eq_top s hs fun a ↦
      congrFun (congrFun (congrArg DescentGroupoid.Hom.val h) a) i)

/-- **The comparison functor is full**: a family of tangent vectors on the charts of a Zariski
cover agreeing on the overlaps comes from a tangent vector over `B`. -/
theorem toDescent_full (hs : Ideal.span s = ⊤) : (toDescent I s).Full where
  map_surjective {x y} F := by
    have hcompat : ∀ (a b : s) (i : σ),
        resL (a : B) (b : B) (F.val a i) = resR (a : B) (b : B) (F.val b i) := by
      intro a b i
      have h := F.compat a b i
      change resL (a : B) (b : B) (F.val a i) + 0 = 0 + resR (a : B) (b : B) (F.val b i) at h
      rwa [add_zero, zero_add] at h
    obtain ⟨w, hw⟩ := exists_glue_vec s hs (fun a ↦ F.val a) hcompat
    have key : ∀ a : s, (algebraMap B (Localization.Away (a : B))).comp
        (translatePoint I x.point w) =
        (algebraMap B (Localization.Away (a : B))).comp y.point := by
      intro a
      rw [IntrinsicConeGluing.comp_translatePoint,
        show (fun i ↦ algebraMap B (Localization.Away (a : B)) (w i)) = F.val a from
          funext fun i ↦ hw a i]
      exact F.translate_eq a
    refine ⟨⟨w, RingHom.ext fun z ↦ eq_of_span_eq_top s hs fun a ↦ ?_⟩,
      DescentGroupoid.Hom.ext (funext fun a ↦ funext fun i ↦ hw a i)⟩
    exact RingHom.congr_fun (key a) z

/-! ### Essential surjectivity -/

/-- **Zariski descent for the points of the affine normal cone.**  A descent datum whose
identifying tangent vectors are all zero comes from a genuine `B`-point of the cone groupoid. -/
theorem exists_eq_toDescentObj (hs : Ideal.span s = ⊤) (y : DescentGroupoid I s)
    (hy : y.vec = 0) : ∃ x : ConeGroupoid I B, toDescentObj I s x = y := by
  have hcompat : ∀ (a b : s) (t : Gr I),
      resL (a : B) (b : B) (y.chart a t) = resR (a : B) (b : B) (y.chart b t) := by
    intro a b t
    have h := y.translate_eq a b
    rw [show y.vec a b = 0 from congrFun (congrFun hy a) b, translatePoint_zero] at h
    exact RingHom.congr_fun h t
  obtain ⟨ψ, hψ⟩ := exists_glue_ringHom s hs y.chart hcompat
  exact ⟨⟨ψ⟩, DescentGroupoid.ext' (funext fun a ↦ hψ a) hy.symm⟩

/-- **Čech vanishing hypothesis** for the cover `s` of `Spec B` and the trivial vector bundle
with fibre `σ`: every additive `1`-cocycle of tangent vectors on the double overlaps of the
cover is a coboundary.  This is the vanishing of `H¹(Spec B, 𝒪_{Spec B}^σ)`, true for every
affine scheme, but not proved here. -/
def CechVanishing (σ : Type u) {B : Type u} [CommRing B] (s : Set B) : Prop :=
  ∀ v : ∀ a b : s, σ → Localization.Away ((a : B) * (b : B)),
    (∀ (a b c : s) (i : σ),
      res₁₂ (a : B) (b : B) (c : B) (v a b i) + res₂₃ (a : B) (b : B) (c : B) (v b c i) =
        res₁₃ (a : B) (b : B) (c : B) (v a c i)) →
    ∃ w : ∀ a : s, σ → Localization.Away (a : B),
      ∀ (a b : s) (i : σ),
        v a b i = resR (a : B) (b : B) (w b i) - resL (a : B) (b : B) (w a i)

/-- Trivialising the identifying vectors of a descent datum with the help of a Čech
coboundary `w`: translating the chart over `a` by `-w a` produces a descent datum whose
identifying vectors all vanish. -/
noncomputable def untwist (y : DescentGroupoid I s)
    (w : ∀ a : s, σ → Localization.Away (a : B))
    (hw : ∀ (a b : s) (i : σ),
      y.vec a b i = resR (a : B) (b : B) (w b i) - resL (a : B) (b : B) (w a i)) :
    DescentGroupoid I s where
  chart a := translatePoint I (y.chart a) (-(w a))
  vec _ _ := 0
  translate_eq a b := by
    rw [translatePoint_zero, IntrinsicConeGluing.comp_translatePoint,
      IntrinsicConeGluing.comp_translatePoint, ← y.translate_eq a b, translatePoint_add]
    congr 1
    funext i
    simp only [Pi.add_apply, Pi.neg_apply, map_neg, hw a b i]
    ring
  cocycle a b c i := by
    change res₁₂ (a : B) (b : B) (c : B) 0 + res₂₃ (a : B) (b : B) (c : B) 0 =
      res₁₃ (a : B) (b : B) (c : B) 0
    rw [map_zero, map_zero, map_zero, zero_add]

/-- The Čech coboundary is a morphism from the untwisted descent datum to the original one. -/
noncomputable def untwistHom (y : DescentGroupoid I s)
    (w : ∀ a : s, σ → Localization.Away (a : B))
    (hw : ∀ (a b : s) (i : σ),
      y.vec a b i = resR (a : B) (b : B) (w b i) - resL (a : B) (b : B) (w a i)) :
    untwist I s y w hw ⟶ y where
  val := w
  translate_eq a := by
    change translatePoint I (translatePoint I (y.chart a) (-(w a))) (w a) = y.chart a
    rw [translatePoint_add, neg_add_cancel, translatePoint_zero]
  compat a b i := by
    change resL (a : B) (b : B) (w a i) + y.vec a b i = 0 + resR (a : B) (b : B) (w b i)
    rw [hw a b i]
    ring

/-- **The comparison functor is essentially surjective**, granted the Čech vanishing
hypothesis: every descent datum is isomorphic to one coming from a `B`-point. -/
theorem toDescent_essSurj (hs : Ideal.span s = ⊤) (hC : CechVanishing σ s) :
    (toDescent I s).EssSurj where
  mem_essImage y := by
    obtain ⟨w, hw⟩ := hC y.vec y.cocycle
    obtain ⟨x, hx⟩ := exists_eq_toDescentObj I s hs (untwist I s y w hw) rfl
    refine ⟨x, ?_⟩
    change Nonempty (toDescentObj I s x ≅ y)
    rw [hx]
    exact ⟨(Groupoid.isoEquivHom _ _).symm (untwistHom I s y w hw)⟩

/-- **The polynomial-model cone groupoid is a Zariski stack in the test algebra**: granted the
Čech vanishing hypothesis, the comparison functor is an equivalence between the `B`-points of
`[C_{U/M}/T_M|_U]` and descent data along the Zariski cover of `Spec B` by the basic opens of a
generating family `s` of the unit ideal. -/
theorem toDescent_isEquivalence (hs : Ideal.span s = ⊤) (hC : CechVanishing σ s) :
    (toDescent I s).IsEquivalence := by
  have _ := toDescent_faithful I s hs
  have _ := toDescent_full I s hs
  have _ := toDescent_essSurj I s hs hC
  exact { }

/-- The equivalence of groupoids between the `B`-points of `[C_{U/M}/T_M|_U]` and the descent
data along a Zariski cover of `Spec B`, granted the Čech vanishing hypothesis. -/
theorem nonempty_descentEquivalence (hs : Ideal.span s = ⊤) (hC : CechVanishing σ s) :
    Nonempty (ConeGroupoid I B ≌ DescentGroupoid I s) := by
  have _ := toDescent_isEquivalence I s hs hC
  exact ⟨(toDescent I s).asEquivalence⟩

end FullyFaithful

/-! ### Čech vanishing for a finite cover by basic opens -/

section Cech

variable {B : Type u} [CommRing B] (s : Set B)

@[simp]
theorem res₁₂_algebraMap (g h k : B) (b : B) :
    res₁₂ g h k (algebraMap B (Localization.Away (g * h)) b) =
      algebraMap B (Localization.Away (g * h * k)) b :=
  awayRes_algebraMap _ _ _ b

@[simp]
theorem res₂₃_algebraMap (g h k : B) (b : B) :
    res₂₃ g h k (algebraMap B (Localization.Away (h * k)) b) =
      algebraMap B (Localization.Away (g * h * k)) b :=
  awayRes_algebraMap _ _ _ b

@[simp]
theorem res₁₃_algebraMap (g h k : B) (b : B) :
    res₁₃ g h k (algebraMap B (Localization.Away (g * k)) b) =
      algebraMap B (Localization.Away (g * h * k)) b :=
  awayRes_algebraMap _ _ _ b

/-- An element of `B` killed by a power of `g` dies in the localisation `B_g`. -/
theorem algebraMap_eq_zero_of_pow_mul_eq_zero {g : B} {x : B} {k : ℕ} (h : g ^ k * x = 0) :
    algebraMap B (Localization.Away g) x = 0 := by
  have h0 : algebraMap B (Localization.Away g) x = algebraMap B (Localization.Away g) 0 :=
    (IsLocalization.eq_iff_exists (Submonoid.powers g) (Localization.Away g)).2
      ⟨⟨g ^ k, ⟨k, rfl⟩⟩, by rw [mul_zero]; exact h⟩
  rwa [map_zero] at h0

/-- Raising the denominator of a fraction in `B_g`. -/
theorem mul_pow_add_eq {g : B} {z : Localization.Away g} {y : B} {n k : ℕ}
    (h : z * algebraMap B (Localization.Away g) g ^ n = algebraMap B (Localization.Away g) y) :
    z * algebraMap B (Localization.Away g) g ^ (n + k) =
      algebraMap B (Localization.Away g) (g ^ k * y) := by
  rw [map_mul, map_pow, ← h, pow_add]
  ring

/-- Raising the exponent in a relation killed by a power of `g`. -/
theorem pow_add_mul_eq_zero {g x : B} {k j : ℕ} (h : g ^ k * x = 0) : g ^ (j + k) * x = 0 := by
  rw [pow_add, mul_assoc, h, mul_zero]

/-- **Vanishing of the first Čech cohomology of the structure sheaf of an affine scheme** for a
finite cover by basic opens: an additive `1`-cocycle on the double overlaps is a coboundary.
This is the local triviality input for Zariski descent of torsors under the tangent bundle. -/
theorem exists_sub_eq_of_cocycle [Finite s] (hs : Ideal.span s = ⊤)
    (v : ∀ a b : s, Localization.Away ((a : B) * (b : B)))
    (hv : ∀ a b c : s, res₁₂ (a : B) (b : B) (c : B) (v a b) +
        res₂₃ (a : B) (b : B) (c : B) (v b c) = res₁₃ (a : B) (b : B) (c : B) (v a c)) :
    ∃ w : ∀ a : s, Localization.Away (a : B),
      ∀ a b : s, v a b = resR (a : B) (b : B) (w b) - resL (a : B) (b : B) (w a) := by
  classical
  cases nonempty_fintype ↥s
  -- Step 1: write every `v a b` with a denominator `(ab)^N` for one and the same `N`.
  obtain ⟨N, r, hrspec⟩ : ∃ (N : ℕ) (r : s → s → B), ∀ a b : s,
      v a b * algebraMap B (Localization.Away ((a : B) * (b : B))) ((a : B) * (b : B)) ^ N =
        algebraMap B (Localization.Away ((a : B) * (b : B))) (r a b) := by
    choose n y hy using fun a b : s ↦ IsLocalization.Away.surj
      (S := Localization.Away ((a : B) * (b : B))) ((a : B) * (b : B)) (v a b)
    refine ⟨Finset.univ.sup fun p : s × s ↦ n p.1 p.2, fun a b ↦
      ((a : B) * (b : B)) ^ ((Finset.univ.sup fun p : s × s ↦ n p.1 p.2) - n a b) * y a b,
      fun a b ↦ ?_⟩
    have hle : n a b ≤ Finset.univ.sup fun p : s × s ↦ n p.1 p.2 :=
      Finset.le_sup (f := fun p : s × s ↦ n p.1 p.2) (Finset.mem_univ (a, b))
    have h := mul_pow_add_eq (k := (Finset.univ.sup fun p : s × s ↦ n p.1 p.2) - n a b) (hy a b)
    rwa [Nat.add_sub_cancel' hle] at h
  -- Step 2: the cocycle relation, cleared of denominators, inside `B`.
  have htriple : ∀ a b c : s, ∃ m : ℕ, ((a : B) * (b : B) * (c : B)) ^ m *
      (r a b * (c : B) ^ N + r b c * (a : B) ^ N - r a c * (b : B) ^ N) = 0 := by
    intro a b c
    have h12 := congrArg (res₁₂ (a : B) (b : B) (c : B)) (hrspec a b)
    have h23 := congrArg (res₂₃ (a : B) (b : B) (c : B)) (hrspec b c)
    have h13 := congrArg (res₁₃ (a : B) (b : B) (c : B)) (hrspec a c)
    rw [map_mul, map_pow, res₁₂_algebraMap, res₁₂_algebraMap] at h12
    rw [map_mul, map_pow, res₂₃_algebraMap, res₂₃_algebraMap] at h23
    rw [map_mul, map_pow, res₁₃_algebraMap, res₁₃_algebraMap] at h13
    have hmul : ∀ x y : B, algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B))) (x * y) =
        algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B))) x *
          algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B))) y :=
      fun x y ↦ map_mul _ _ _
    have hpow : ∀ x : B, ∀ j : ℕ,
        algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B))) (x ^ j) =
          algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B))) x ^ j :=
      fun x j ↦ map_pow _ _ _
    have habc : algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B)))
        ((a : B) * (b : B) * (c : B)) =
        algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B))) (a : B) *
          algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B))) (b : B) *
          algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B))) (c : B) := by
      rw [hmul, hmul]
    have hab : algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B)))
        ((a : B) * (b : B)) =
        algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B))) (a : B) *
          algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B))) (b : B) := hmul _ _
    have hbc : algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B)))
        ((b : B) * (c : B)) =
        algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B))) (b : B) *
          algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B))) (c : B) := hmul _ _
    have hac : algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B)))
        ((a : B) * (c : B)) =
        algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B))) (a : B) *
          algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B))) (c : B) := hmul _ _
    rw [hab] at h12
    rw [hbc] at h23
    rw [hac] at h13
    have hsum : algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B)))
        (r a b * (c : B) ^ N + r b c * (a : B) ^ N) =
        algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B)))
          (r a c * (b : B) ^ N) := by
      rw [map_add, hmul, hmul, hmul, hpow, hpow, hpow, ← h12, ← h13, ← h23]
      linear_combination
        (algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B))) (a : B) ^ N *
          algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B))) (b : B) ^ N *
          algebraMap B (Localization.Away ((a : B) * (b : B) * (c : B))) (c : B) ^ N) *
          hv a b c
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq
      (S := Localization.Away ((a : B) * (b : B) * (c : B))) ((a : B) * (b : B) * (c : B)) hsum
    exact ⟨m, by linear_combination hm⟩
  -- Step 3: a uniform exponent `M` in the cleared cocycle relation.
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ a b c : s, ((a : B) * (b : B) * (c : B)) ^ M *
      (r a b * (c : B) ^ N + r b c * (a : B) ^ N - r a c * (b : B) ^ N) = 0 := by
    choose m hm using htriple
    refine ⟨Finset.univ.sup fun p : s × s × s ↦ m p.1 p.2.1 p.2.2, fun a b c ↦ ?_⟩
    have hle : m a b c ≤ Finset.univ.sup fun p : s × s × s ↦ m p.1 p.2.1 p.2.2 :=
      Finset.le_sup (f := fun p : s × s × s ↦ m p.1 p.2.1 p.2.2) (Finset.mem_univ (a, b, c))
    have h := pow_add_mul_eq_zero
      (j := (Finset.univ.sup fun p : s × s × s ↦ m p.1 p.2.1 p.2.2) - m a b c) (hm a b c)
    rwa [Nat.sub_add_cancel hle] at h
  -- Step 4: a partition of unity for the exponent `M + N`.
  obtain ⟨e, he⟩ : ∃ e : s → B, ∑ a : s, e a * (a : B) ^ (M + N) = 1 :=
    Ideal.mem_span_range_iff_exists_fun.1 (by
      rw [Ideal.span_range_pow_eq_top s hs fun _ ↦ M + N]; trivial)
  -- Step 5: the Čech primitive.
  refine ⟨fun x ↦ algebraMap B (Localization.Away (x : B)) (∑ c : s, e c * (c : B) ^ M * r c x) *
    IsLocalization.Away.invSelf (x : B) ^ N, fun a b ↦ ?_⟩
  have hkey : ((a : B) * (b : B)) ^ M *
      ((∑ c : s, e c * (c : B) ^ M * r c b) * (a : B) ^ N -
        (∑ c : s, e c * (c : B) ^ M * r c a) * (b : B) ^ N - r a b) = 0 := by
    have step : ∀ c : s, ((a : B) * (b : B)) ^ M *
        (e c * (c : B) ^ M * r c b * (a : B) ^ N - e c * (c : B) ^ M * r c a * (b : B) ^ N) =
        e c * (((a : B) * (b : B)) ^ M * r a b) * (c : B) ^ (M + N) := fun c ↦ by
      linear_combination (-(e c)) * hM c a b
    have e1 : ((a : B) * (b : B)) ^ M *
        ((∑ c : s, e c * (c : B) ^ M * r c b) * (a : B) ^ N -
          (∑ c : s, e c * (c : B) ^ M * r c a) * (b : B) ^ N) =
        ∑ c : s, e c * (((a : B) * (b : B)) ^ M * r a b) * (c : B) ^ (M + N) := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ ↦ step c
    have e2 : ∑ c : s, e c * (((a : B) * (b : B)) ^ M * r a b) * (c : B) ^ (M + N) =
        (∑ c : s, e c * (c : B) ^ (M + N)) * (((a : B) * (b : B)) ^ M * r a b) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ ↦ by ring
    have e3 := e1.trans (e2.trans (by rw [he, one_mul]))
    linear_combination e3
  -- Step 6: compare the two sides after clearing the denominator `(ab)^N`.
  have hab : algebraMap B (Localization.Away ((a : B) * (b : B))) ((a : B) * (b : B)) =
      algebraMap B (Localization.Away ((a : B) * (b : B))) (a : B) *
        algebraMap B (Localization.Away ((a : B) * (b : B))) (b : B) := map_mul _ _ _
  have hunitL : resL (a : B) (b : B)
      (IsLocalization.Away.invSelf (a : B) : Localization.Away (a : B)) *
      algebraMap B (Localization.Away ((a : B) * (b : B))) (a : B) = 1 := by
    have h := congrArg (resL (a : B) (b : B))
      (IsLocalization.Away.mul_invSelf (S := Localization.Away (a : B)) (a : B))
    rw [map_mul, map_one, resL_algebraMap] at h
    linear_combination h
  have hunitR : resR (a : B) (b : B)
      (IsLocalization.Away.invSelf (b : B) : Localization.Away (b : B)) *
      algebraMap B (Localization.Away ((a : B) * (b : B))) (b : B) = 1 := by
    have h := congrArg (resR (a : B) (b : B))
      (IsLocalization.Away.mul_invSelf (S := Localization.Away (b : B)) (b : B))
    rw [map_mul, map_one, resR_algebraMap] at h
    linear_combination h
  have hwa : resL (a : B) (b : B)
      (algebraMap B (Localization.Away (a : B)) (∑ c : s, e c * (c : B) ^ M * r c a) *
        IsLocalization.Away.invSelf (a : B) ^ N) *
      algebraMap B (Localization.Away ((a : B) * (b : B))) (a : B) ^ N =
      algebraMap B (Localization.Away ((a : B) * (b : B)))
        (∑ c : s, e c * (c : B) ^ M * r c a) := by
    rw [map_mul, map_pow, resL_algebraMap, mul_assoc, ← mul_pow, hunitL, one_pow, mul_one]
  have hwb : resR (a : B) (b : B)
      (algebraMap B (Localization.Away (b : B)) (∑ c : s, e c * (c : B) ^ M * r c b) *
        IsLocalization.Away.invSelf (b : B) ^ N) *
      algebraMap B (Localization.Away ((a : B) * (b : B))) (b : B) ^ N =
      algebraMap B (Localization.Away ((a : B) * (b : B)))
        (∑ c : s, e c * (c : B) ^ M * r c b) := by
    rw [map_mul, map_pow, resR_algebraMap, mul_assoc, ← mul_pow, hunitR, one_pow, mul_one]
  have hz2 : algebraMap B (Localization.Away ((a : B) * (b : B)))
        (∑ c : s, e c * (c : B) ^ M * r c b) *
        algebraMap B (Localization.Away ((a : B) * (b : B))) (a : B) ^ N -
      algebraMap B (Localization.Away ((a : B) * (b : B)))
        (∑ c : s, e c * (c : B) ^ M * r c a) *
        algebraMap B (Localization.Away ((a : B) * (b : B))) (b : B) ^ N =
      algebraMap B (Localization.Away ((a : B) * (b : B))) (r a b) := by
    have hz := algebraMap_eq_zero_of_pow_mul_eq_zero (g := (a : B) * (b : B)) hkey
    rw [map_sub, map_sub, map_mul, map_mul, map_pow, map_pow, sub_eq_zero] at hz
    exact hz
  have h1 : v a b * (algebraMap B (Localization.Away ((a : B) * (b : B))) (a : B) ^ N *
      algebraMap B (Localization.Away ((a : B) * (b : B))) (b : B) ^ N) =
      algebraMap B (Localization.Away ((a : B) * (b : B))) (r a b) := by
    rw [← mul_pow, ← hab]
    exact hrspec a b
  refine ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away ((a : B) * (b : B)))
    ((a : B) * (b : B))).pow N).mul_left_inj.mp ?_
  dsimp only
  rw [hab, mul_pow]
  linear_combination h1 -
    algebraMap B (Localization.Away ((a : B) * (b : B))) (a : B) ^ N * hwb +
    algebraMap B (Localization.Away ((a : B) * (b : B))) (b : B) ^ N * hwa - hz2

/-- Čech vanishing for the trivial bundle with fibre `σ`, componentwise from the rank-one
case. -/
theorem cechVanishing_of_finite (σ : Type u) [Finite s] (hs : Ideal.span s = ⊤) :
    CechVanishing σ s := by
  intro v hv
  have h : ∀ i : σ, ∃ w : ∀ a : s, Localization.Away (a : B),
      ∀ a b : s, v a b i = resR (a : B) (b : B) (w b) - resL (a : B) (b : B) (w a) :=
    fun i ↦ exists_sub_eq_of_cocycle s hs (fun a b ↦ v a b i) fun a b c ↦ hv a b c i
  choose w hw using h
  exact ⟨fun a i ↦ w i a, fun a b i ↦ hw i a b⟩

end Cech

/-! ### The Zariski descent theorem -/

section Main

open CategoryTheory ConeTranslation ConeRefinement

variable {A : Type u} [CommRing A] {σ : Type u} (I : Ideal (Amb A σ))
  {B : Type u} [CommRing B] (s : Set B)

/-- **The comparison functor is an equivalence for a finite cover.**  No hypothesis beyond
`Ideal.span s = ⊤` and the finiteness of the cover: the Čech vanishing input is supplied by
`ConeDescent.cechVanishing_of_finite`. -/
theorem toDescent_isEquivalence_of_finite [Finite s] (hs : Ideal.span s = ⊤) :
    (toDescent I s).IsEquivalence :=
  toDescent_isEquivalence I s hs (cechVanishing_of_finite s σ hs)

/-- **The polynomial-model cone groupoid is a Zariski stack in the test algebra.**  For a finite
family `s` of elements of `B` generating the unit ideal, the `B`-points of `[C_{U/M}/T_M|_U]`
are equivalent to the descent data along the corresponding cover of `Spec B` by basic opens. -/
noncomputable def descentEquivalence [Finite s] (hs : Ideal.span s = ⊤) :
    ConeGroupoid I B ≌ DescentGroupoid I s :=
  haveI := toDescent_isEquivalence_of_finite I s hs
  (toDescent I s).asEquivalence

/-- The equivalence of `ConeDescent.descentEquivalence` is realised by the comparison
functor. -/
theorem descentEquivalence_functor [Finite s] (hs : Ideal.span s = ⊤) :
    (descentEquivalence I s hs).functor = toDescent I s :=
  rfl

end Main





end ConeDescent

end GromovWitten.AlgebraicGeometry
