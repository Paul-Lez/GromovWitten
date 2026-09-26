/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.IntrinsicConeDescent

/-!
# Zariski descent of the cone groupoid for infinite covers

`Cones/IntrinsicConeDescent.lean` proves Zariski descent of `ConeRefinement.ConeGroupoid I B`
along a cover `s : Set B` of the unit ideal of the test algebra `B`, but only under the
hypothesis `ConeDescent.CechVanishing σ s`, and proves that hypothesis only for **finite** covers
(`ConeDescent.cechVanishing_of_finite`).  This file removes the finiteness hypothesis: it proves
`ConeDescent.CechVanishing σ s` for *every* cover `s` with `Ideal.span s = ⊤`, by reducing to a
finite spanning subcover.

## The reduction to a finite subcover

`ConeDescent.exists_finset_span_eq_top` extracts a finite `s₀ ⊆ s` with `Ideal.span s₀ = ⊤` from
`Ideal.span s = ⊤`.  `ConeDescent.exists_eq_sub_of_isTrivialization` is the comparison lemma: if
`t₁ ⊆ t₂` are two covers with `Ideal.span t₁ = ⊤` and `w₁`, `w₂` both trivialise the *same*
cocycle (`w₁` on `t₁`, `w₂` on `t₂`), then `w₂` and `w₁` differ, on all of `t₁`, by (the image of)
a single element of `B` — this is exactly the sheaf condition `ConeDescent.existsUnique_glue`
applied to the family `w₂ - w₁`.

`ConeDescent.exists_sub_eq_of_cocycle_of_span_eq_top` is the main construction: fix a finite
spanning `s₀ ⊆ s` and a reference trivialisation `w₀` of the cocycle on `s₀`
(`ConeDescent.exists_sub_eq_of_cocycle`).  For every chart `x ∈ s`, trivialise the cocycle on the
finite cover `insert x s₀` and correct it against `w₀` on `s₀` using the comparison lemma, to
define `w x`.  To check that this `w` satisfies the cocycle-splitting identity for an *arbitrary*
pair `a, b ∈ s`, compare both single-chart trivialisations against a *third* trivialisation on the
finite cover `insert b (insert a s₀)`: the two correction terms obtained this way agree on `s₀`,
hence (since `s₀` spans) agree in `B`, and cancel in the final identity.

`ConeDescent.cechVanishing_of_span_eq_top` wraps this componentwise, exactly as
`ConeDescent.cechVanishing_of_finite` does for the finite case.  Consequently
`ConeDescent.toDescent_isEquivalence_of_span_eq_top` and `ConeDescent.descentEquivalence'` remove
the `[Finite s]` hypothesis from `ConeDescent.toDescent_isEquivalence_of_finite` and
`ConeDescent.descentEquivalence`: **Zariski descent for the cone groupoid holds for every cover**.

## What is not here

This file does not construct the `DescentGroupoid.restrict` comparison functor between
`DescentGroupoid I s` and `DescentGroupoid I s₀` for a spanning subcover; it establishes
`CechVanishing` for general `s` directly, which already gives the unconditional descent
equivalence via the (already unconditional in `s`) `ConeDescent.toDescent_isEquivalence`, so the
restriction functor is not needed for that purpose.
-/

namespace GromovWitten.AlgebraicGeometry

namespace ConeDescent

universe u

variable {B : Type u} [CommRing B]

/-- **Reduction to a finite spanning subset.**  Every generating set of the unit ideal contains a
finite generating subset. -/
theorem exists_finset_span_eq_top {s : Set B} (hs : Ideal.span s = ⊤) :
    ∃ s₀ : Finset B, (↑s₀ : Set B) ⊆ s ∧ Ideal.span (↑s₀ : Set B) = ⊤ := by
  have h1 : (1 : B) ∈ Ideal.span s := hs ▸ Submodule.mem_top
  obtain ⟨T, hTs, hT1⟩ := Submodule.mem_span_finite_of_mem_span h1
  exact ⟨T, hTs, Ideal.eq_top_iff_one _ |>.mpr hT1⟩

/-- **Comparison of two trivialisations of the same cocycle on nested covers.**  If `t₁ ⊆ t₂`
are two covers of the test algebra with `t₁` spanning the unit ideal, and `w₁`, `w₂` trivialise
the same additive `1`-cocycle (`w₁` on `t₁`, `w₂` on `t₂`), then `w₂` and `w₁` agree, on all of
`t₁`, up to the restriction of a single element of `B` — the sheaf condition applied to the
matching family `w₂ - w₁`. -/
theorem exists_eq_sub_of_isTrivialization {t1 t2 : Set B} (ht : t1 ⊆ t2)
    (ht1 : Ideal.span t1 = ⊤) (w1 : ∀ a : t1, Localization.Away (a : B))
    (w2 : ∀ a : t2, Localization.Away (a : B))
    (hmatch : ∀ a b : t1,
      resR (a : B) (b : B) (w2 (Set.inclusion ht b)) -
          resL (a : B) (b : B) (w2 (Set.inclusion ht a)) =
        resR (a : B) (b : B) (w1 b) - resL (a : B) (b : B) (w1 a)) :
    ∃ g : B, ∀ a : t1, algebraMap B (Localization.Away (a : B)) g =
      w2 (Set.inclusion ht a) - w1 a := by
  have hcompat : ∀ a b : t1, resL (a : B) (b : B) (w2 (Set.inclusion ht a) - w1 a) =
      resR (a : B) (b : B) (w2 (Set.inclusion ht b) - w1 b) := by
    intro a b
    have h := hmatch a b
    rw [map_sub, map_sub]
    linear_combination -h
  obtain ⟨g, hg, -⟩ := existsUnique_glue t1 ht1 (fun a ↦ w2 (Set.inclusion ht a) - w1 a) hcompat
  exact ⟨g, hg⟩

/-- **Vanishing of the first Čech cohomology of the structure sheaf of an affine scheme**, for an
*arbitrary* cover by basic opens: an additive `1`-cocycle on the double overlaps is a coboundary.
This removes the `[Finite s]` hypothesis of `ConeDescent.exists_sub_eq_of_cocycle`, by reducing to
a finite spanning subcover and comparing trivialisations on overlapping finite covers via
`exists_eq_sub_of_isTrivialization`. -/
theorem exists_sub_eq_of_cocycle_of_span_eq_top {s : Set B} (hs : Ideal.span s = ⊤)
    (v : ∀ a b : s, Localization.Away ((a : B) * (b : B)))
    (hv : ∀ a b c : s, res₁₂ (a : B) (b : B) (c : B) (v a b) +
        res₂₃ (a : B) (b : B) (c : B) (v b c) = res₁₃ (a : B) (b : B) (c : B) (v a c)) :
    ∃ w : ∀ a : s, Localization.Away (a : B),
      ∀ a b : s, v a b = resR (a : B) (b : B) (w b) - resL (a : B) (b : B) (w a) := by
  classical
  obtain ⟨s₀, hs₀sub, hs₀span⟩ := exists_finset_span_eq_top hs
  set t0 : Set B := (↑s₀ : Set B) with ht0def
  have ht0sub : t0 ⊆ s := hs₀sub
  have ht0span : Ideal.span t0 = ⊤ := hs₀span
  -- A reference trivialisation of the cocycle on the finite spanning subcover `t0`.
  obtain ⟨w0, hw0⟩ := exists_sub_eq_of_cocycle t0 ht0span
    (fun a b ↦ v (Set.inclusion ht0sub a) (Set.inclusion ht0sub b))
    (fun a b c ↦ hv (Set.inclusion ht0sub a) (Set.inclusion ht0sub b) (Set.inclusion ht0sub c))
  have hsub : ∀ x : s, (insert (x : B) t0 : Set B) ⊆ s := fun x ↦
    Set.insert_subset x.2 ht0sub
  have hstep : ∀ x : s, Ideal.span (insert (x : B) t0 : Set B) = ⊤ := fun x ↦ by
    have h1 : Ideal.span t0 ≤ Ideal.span (insert (x : B) t0 : Set B) :=
      Ideal.span_mono (Set.subset_insert _ _)
    rw [ht0span] at h1
    exact top_le_iff.mp h1
  have hfin : ∀ x : s, Finite (insert (x : B) t0 : Set B) := fun _ ↦ by infer_instance
  have ht0sub' : ∀ x : s, t0 ⊆ (insert (x : B) t0 : Set B) := fun _ ↦ Set.subset_insert _ _
  have hxmem : ∀ x : s, (x : B) ∈ (insert (x : B) t0 : Set B) := fun _ ↦ Set.mem_insert _ _
  -- For every chart `x`, trivialise the cocycle on `insert x t0` and correct it against `w0`.
  have hex2 : ∀ x : s, ∃ (wx : ∀ a : (insert (x : B) t0 : Set B), Localization.Away (a : B))
      (g : B),
      (∀ a b : (insert (x : B) t0 : Set B),
         v (Set.inclusion (hsub x) a) (Set.inclusion (hsub x) b) =
           resR (a : B) (b : B) (wx b) - resL (a : B) (b : B) (wx a)) ∧
      (∀ a : t0, algebraMap B (Localization.Away (a : B)) g =
          wx (Set.inclusion (ht0sub' x) a) - w0 a) := by
    intro x
    have := hfin x
    obtain ⟨wx, hwx⟩ := exists_sub_eq_of_cocycle (insert (x : B) t0 : Set B) (hstep x)
      (fun a b ↦ v (Set.inclusion (hsub x) a) (Set.inclusion (hsub x) b))
      (fun a b c ↦ hv (Set.inclusion (hsub x) a) (Set.inclusion (hsub x) b)
        (Set.inclusion (hsub x) c))
    obtain ⟨g, hg⟩ := exists_eq_sub_of_isTrivialization (ht0sub' x) ht0span w0 wx (fun a b ↦ by
      have h1 : v (Set.inclusion ht0sub a) (Set.inclusion ht0sub b) =
          resR (a : B) (b : B) (wx (Set.inclusion (ht0sub' x) b)) -
            resL (a : B) (b : B) (wx (Set.inclusion (ht0sub' x) a)) :=
        hwx (Set.inclusion (ht0sub' x) a) (Set.inclusion (ht0sub' x) b)
      rw [← h1, hw0 a b])
    exact ⟨wx, g, hwx, hg⟩
  choose wx g hwx hg using hex2
  refine ⟨fun x ↦ wx x ⟨(x : B), hxmem x⟩ - algebraMap B (Localization.Away (x : B)) (g x), ?_⟩
  intro a b
  -- Compare both single-chart trivialisations against a common finite spanning superset.
  set tab : Set B := insert (b : B) (insert (a : B) t0) with htabdef
  have hexta_sub_tab : (insert (a : B) t0 : Set B) ⊆ tab := Set.subset_insert _ _
  have hextb_sub_tab : (insert (b : B) t0 : Set B) ⊆ tab :=
    Set.insert_subset_insert (Set.subset_insert _ _)
  have htab_sub : tab ⊆ s := Set.insert_subset b.2 (hsub a)
  have htab_span : Ideal.span tab = ⊤ := by
    have h1 : Ideal.span (insert (a : B) t0 : Set B) ≤ Ideal.span tab :=
      Ideal.span_mono (Set.subset_insert _ _)
    rw [hstep a] at h1
    exact top_le_iff.mp h1
  have hfintab : Finite tab := by infer_instance
  obtain ⟨wab, hwab⟩ := exists_sub_eq_of_cocycle tab htab_span
    (fun p q ↦ v (Set.inclusion htab_sub p) (Set.inclusion htab_sub q))
    (fun p q r ↦ hv (Set.inclusion htab_sub p) (Set.inclusion htab_sub q)
      (Set.inclusion htab_sub r))
  obtain ⟨ha, hha⟩ := exists_eq_sub_of_isTrivialization hexta_sub_tab (hstep a) (wx a) wab
    (fun p q ↦ by
      have h1 : v (Set.inclusion (hsub a) p) (Set.inclusion (hsub a) q) =
          resR (p : B) (q : B) (wab (Set.inclusion hexta_sub_tab q)) -
            resL (p : B) (q : B) (wab (Set.inclusion hexta_sub_tab p)) :=
        hwab (Set.inclusion hexta_sub_tab p) (Set.inclusion hexta_sub_tab q)
      rw [← h1, hwx a p q])
  obtain ⟨hb, hhb⟩ := exists_eq_sub_of_isTrivialization hextb_sub_tab (hstep b) (wx b) wab
    (fun p q ↦ by
      have h1 : v (Set.inclusion (hsub b) p) (Set.inclusion (hsub b) q) =
          resR (p : B) (q : B) (wab (Set.inclusion hextb_sub_tab q)) -
            resL (p : B) (q : B) (wab (Set.inclusion hextb_sub_tab p)) :=
        hwab (Set.inclusion hextb_sub_tab p) (Set.inclusion hextb_sub_tab q)
      rw [← h1, hwx b p q])
  have ht0_tab_a : t0 ⊆ tab := (ht0sub' a).trans hexta_sub_tab
  -- The two correction terms agree on `t0`, hence (since `t0` spans) agree in `B`.
  have hkey : ∀ c : t0, algebraMap B (Localization.Away (c : B)) (ha + g a) =
      algebraMap B (Localization.Away (c : B)) (hb + g b) := by
    intro c
    have hA : algebraMap B (Localization.Away (c : B)) ha =
        wab (Set.inclusion ht0_tab_a c) - wx a (Set.inclusion (ht0sub' a) c) :=
      hha (Set.inclusion (ht0sub' a) c)
    have hB : algebraMap B (Localization.Away (c : B)) hb =
        wab (Set.inclusion ht0_tab_a c) - wx b (Set.inclusion (ht0sub' b) c) :=
      hhb (Set.inclusion (ht0sub' b) c)
    have hGa : algebraMap B (Localization.Away (c : B)) (g a) =
        wx a (Set.inclusion (ht0sub' a) c) - w0 c := hg a c
    have hGb : algebraMap B (Localization.Away (c : B)) (g b) =
        wx b (Set.inclusion (ht0sub' b) c) - w0 c := hg b c
    rw [map_add, map_add]
    linear_combination hA + hGa - hB - hGb
  have hk : ha + g a = hb + g b := eq_of_span_eq_top t0 ht0span hkey
  have haval : wab (Set.inclusion hexta_sub_tab ⟨(a : B), hxmem a⟩) =
      wx a ⟨(a : B), hxmem a⟩ + algebraMap B (Localization.Away (a : B)) ha := by
    linear_combination -hha ⟨(a : B), hxmem a⟩
  have hbval : wab (Set.inclusion hextb_sub_tab ⟨(b : B), hxmem b⟩) =
      wx b ⟨(b : B), hxmem b⟩ + algebraMap B (Localization.Away (b : B)) hb := by
    linear_combination -hhb ⟨(b : B), hxmem b⟩
  have hvab : v a b = resR (a : B) (b : B) (wab (Set.inclusion hextb_sub_tab ⟨(b : B), hxmem b⟩)) -
      resL (a : B) (b : B) (wab (Set.inclusion hexta_sub_tab ⟨(a : B), hxmem a⟩)) :=
    hwab (Set.inclusion hexta_sub_tab ⟨(a : B), hxmem a⟩)
      (Set.inclusion hextb_sub_tab ⟨(b : B), hxmem b⟩)
  have e1 : resR (a : B) (b : B) (wab (Set.inclusion hextb_sub_tab ⟨(b : B), hxmem b⟩)) =
      resR (a : B) (b : B) (wx b ⟨(b : B), hxmem b⟩) +
        algebraMap B (Localization.Away ((a : B) * (b : B))) hb := by
    rw [hbval, map_add, resR_algebraMap]
  have e2 : resL (a : B) (b : B) (wab (Set.inclusion hexta_sub_tab ⟨(a : B), hxmem a⟩)) =
      resL (a : B) (b : B) (wx a ⟨(a : B), hxmem a⟩) +
        algebraMap B (Localization.Away ((a : B) * (b : B))) ha := by
    rw [haval, map_add, resL_algebraMap]
  have e3 : algebraMap B (Localization.Away ((a : B) * (b : B))) ha +
      algebraMap B (Localization.Away ((a : B) * (b : B))) (g a) =
      algebraMap B (Localization.Away ((a : B) * (b : B))) hb +
      algebraMap B (Localization.Away ((a : B) * (b : B))) (g b) := by
    rw [← map_add, ← map_add, hk]
  change v a b = resR (a : B) (b : B)
      (wx b ⟨(b : B), hxmem b⟩ - algebraMap B (Localization.Away (b : B)) (g b)) -
    resL (a : B) (b : B) (wx a ⟨(a : B), hxmem a⟩ - algebraMap B (Localization.Away (a : B)) (g a))
  rw [map_sub, map_sub, resR_algebraMap, resL_algebraMap]
  linear_combination hvab + e1 - e2 - e3

/-- **Čech vanishing for the trivial bundle with fibre `σ`, for an arbitrary cover.**  Removes
the `[Finite s]` hypothesis of `ConeDescent.cechVanishing_of_finite`, componentwise from
`exists_sub_eq_of_cocycle_of_span_eq_top`. -/
theorem cechVanishing_of_span_eq_top (σ : Type u) {s : Set B} (hs : Ideal.span s = ⊤) :
    CechVanishing σ s := by
  intro v hv
  have h : ∀ i : σ, ∃ w : ∀ a : s, Localization.Away (a : B),
      ∀ a b : s, v a b i = resR (a : B) (b : B) (w b) - resL (a : B) (b : B) (w a) :=
    fun i ↦ exists_sub_eq_of_cocycle_of_span_eq_top hs (fun a b ↦ v a b i)
      fun a b c ↦ hv a b c i
  choose w hw using h
  exact ⟨fun a i ↦ w i a, fun a b i ↦ hw i a b⟩

/-! ### The general Zariski descent theorem -/

section Main

open CategoryTheory ConeTranslation ConeRefinement

variable {A : Type u} [CommRing A] {σ : Type u} (I : Ideal (Amb A σ)) (s : Set B)

/-- **The comparison functor is an equivalence for an arbitrary cover.**  No hypothesis beyond
`Ideal.span s = ⊤`: the Čech vanishing input is supplied by
`ConeDescent.cechVanishing_of_span_eq_top`, removing the finiteness hypothesis of
`ConeDescent.toDescent_isEquivalence_of_finite`. -/
theorem toDescent_isEquivalence_of_span_eq_top (hs : Ideal.span s = ⊤) :
    (toDescent I s).IsEquivalence :=
  toDescent_isEquivalence I s hs (cechVanishing_of_span_eq_top σ hs)

/-- **The polynomial-model cone groupoid is a Zariski stack in the test algebra**, for an
arbitrary family `s` of elements of `B` generating the unit ideal: the `B`-points of
`[C_{U/M}/T_M|_U]` are equivalent to the descent data along the corresponding cover of `Spec B`
by basic opens.  This removes the finiteness hypothesis of `ConeDescent.descentEquivalence`. -/
noncomputable def descentEquivalence' (hs : Ideal.span s = ⊤) :
    ConeGroupoid I B ≌ DescentGroupoid I s :=
  haveI := toDescent_isEquivalence_of_span_eq_top I s hs
  (toDescent I s).asEquivalence

/-- The equivalence of `ConeDescent.descentEquivalence'` is realised by the comparison
functor. -/
theorem descentEquivalence'_functor (hs : Ideal.span s = ⊤) :
    (descentEquivalence' I s hs).functor = toDescent I s :=
  rfl

end Main

end ConeDescent

end GromovWitten.AlgebraicGeometry
