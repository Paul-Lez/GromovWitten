/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChowGroup

/-!
# Čech line bundle data, rational sections, and their divisor cycles

The cycle-level input for the first Chern class `c₁(L) ∩ [V]` of Fulton's Intersection Theory
§2.3–2.5: a line bundle on a scheme `X` presented by a Čech cocycle of transition units on an
affine open cover, a rational section of its restriction to an integral closed subscheme
`V ⊆ X`, the order of vanishing of a rational section at a codimension-one point of `V`, and the
associated divisor cycle on `V` (and, pushed forward, on `X`).

## Main declarations

* `LineBundleData X` — a Čech cocycle of transition units on an affine open cover of `X`;
  `LineBundleData.trivial`, `LineBundleData.tensor`, `LineBundleData.inv`.
* `LineBundleData.unitAt` — the class, in the function field of an integral closed subscheme
  `V`, of a transition unit restricted along `V`'s generic point.
* `LineBundleData.RationalSection` — a rational section of `L` along `V`, presented as a
  function-field unit in one chart; `RationalSection.coord` — its expression in any other chart
  containing the generic point.
* `RationalSection.ord` — the order of vanishing of a rational section at a codimension-one
  point of `V`, independent of the chart used to compute it.
* `RationalSection.divisorCycle`, `RationalSection.divisor` — the associated Weil divisor cycle
  on `V`, and its pushforward to `X`.

## Convention

The transition unit `g j j'` is the factor relating the local generators `e_j = g j j' • e_{j'}`
of the two charts.  A rational section `s` with coordinate `f` in the chart `j₀` (i.e.
`s = f • e_{j₀}`) has coordinate `unitAt j j₀ * f` in the chart `j`.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open GromovWitten.AlgebraicGeometry.IntersectionTheory

/-- Restrict a unit of the sections of the structure sheaf over an open `V` to a unit of the
sections over a smaller open `U ≤ V`. -/
noncomputable def resUnit {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V) (u : Γ(X, V)ˣ) :
    Γ(X, U)ˣ :=
  Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom u

@[simp]
lemma resUnit_refl {X : Scheme.{u}} {U : X.Opens} (u : Γ(X, U)ˣ) :
    resUnit (le_refl U) u = u := by
  apply Units.ext
  change (X.presheaf.map (homOfLE (le_refl U)).op).hom u = u
  simp

lemma resUnit_trans {X : Scheme.{u}} {U V W : X.Opens} (h1 : U ≤ V) (h2 : V ≤ W)
    (u : Γ(X, W)ˣ) :
    resUnit h1 (resUnit h2 u) = resUnit (h1.trans h2) u := by
  apply Units.ext
  change (X.presheaf.map (homOfLE h1).op).hom ((X.presheaf.map (homOfLE h2).op).hom u) =
      (X.presheaf.map (homOfLE (h1.trans h2)).op).hom u
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

@[simp]
lemma resUnit_one {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V) :
    resUnit h (1 : Γ(X, V)ˣ) = 1 := by
  apply Units.ext
  change (X.presheaf.map (homOfLE h).op).hom 1 = 1
  simp

lemma resUnit_mul {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V) (u v : Γ(X, V)ˣ) :
    resUnit h (u * v) = resUnit h u * resUnit h v := by
  apply Units.ext
  change (X.presheaf.map (homOfLE h).op).hom (u * v) =
      (X.presheaf.map (homOfLE h).op).hom u * (X.presheaf.map (homOfLE h).op).hom v
  simp

/-- Restriction of units is compatible with inversion. -/
lemma resUnit_inv {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V) (u : Γ(X, V)ˣ) :
    resUnit h u⁻¹ = (resUnit h u)⁻¹ :=
  map_inv (Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom) u

/-- A line bundle on `X` presented by a Čech cocycle of transition units on an affine open
cover.  The convention is that the local generators `e_j` of the charts satisfy
`e_j = g j j' • e_{j'}`. -/
structure LineBundleData (X : Scheme.{u}) where
  /-- The index type of the affine open cover. -/
  J : Type u
  /-- The affine open cover. -/
  U : J → X.affineOpens
  /-- The cover really covers `X`. -/
  covers : ∀ x : X, ∃ j, x ∈ (U j : X.Opens)
  /-- The transition unit of the pair of charts `j`, `j'`, a unit of the sections over the
  overlap. -/
  g : ∀ j j' : J, Γ(X, (U j : X.Opens) ⊓ (U j' : X.Opens))ˣ
  /-- The transition unit of a chart with itself is trivial. -/
  g_self : ∀ j, g j j = 1
  /-- The cocycle condition on a triple overlap. -/
  g_cocycle : ∀ j j' j'' : J,
    resUnit inf_le_left (g j j') * resUnit (inf_le_inf inf_le_right (le_refl (U j'' : X.Opens)))
        (g j' j'') =
      resUnit (inf_le_inf inf_le_left (le_refl (U j'' : X.Opens))) (g j j'')

namespace LineBundleData

variable {X : Scheme.{u}}

/-- The trivial line bundle: the cover by all affine opens of `X`, with all transition units
equal to `1`. -/
noncomputable def trivial (X : Scheme.{u}) : LineBundleData X where
  J := X.affineOpens
  U := id
  covers x := by
    obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ (⊤ : X.Opens) by simp)
    exact ⟨⟨U, hU⟩, hxU⟩
  g _ _ := 1
  g_self _ := rfl
  g_cocycle _ _ _ := by simp

/-- A second Čech cocycle of transition units on the exact same affine open cover as `L`: the
data needed to form a tensor factor `M` without having to transport across a chart-type
equality. -/
structure Cocycle (L : LineBundleData X) where
  /-- The transition unit of the second cocycle. -/
  g : ∀ j j' : L.J, Γ(X, (L.U j : X.Opens) ⊓ (L.U j' : X.Opens))ˣ
  /-- The transition unit of a chart with itself is trivial. -/
  g_self : ∀ j, g j j = 1
  /-- The cocycle condition on a triple overlap. -/
  g_cocycle : ∀ j j' j'' : L.J,
    resUnit inf_le_left (g j j') *
        resUnit (inf_le_inf inf_le_right (le_refl (L.U j'' : X.Opens))) (g j' j'') =
      resUnit (inf_le_inf inf_le_left (le_refl (L.U j'' : X.Opens))) (g j j'')

/-- The line bundle data on `L`'s cover determined by a second cocycle `M`. -/
noncomputable def Cocycle.toLineBundleData {L : LineBundleData X} (M : Cocycle L) :
    LineBundleData X where
  J := L.J
  U := L.U
  covers := L.covers
  g := M.g
  g_self := M.g_self
  g_cocycle := M.g_cocycle

/-- The transition units of `L` form a cocycle on `L`'s own cover, so `L` can be recovered from
`Cocycle.toLineBundleData`. -/
def selfCocycle (L : LineBundleData X) : Cocycle L where
  g := L.g
  g_self := L.g_self
  g_cocycle := L.g_cocycle

/-- The tensor product of two line bundle data on the same index type and open cover: multiply
the transition units. -/
noncomputable def tensor (L : LineBundleData X) (M : Cocycle L) : LineBundleData X where
  J := L.J
  U := L.U
  covers := L.covers
  g j j' := L.g j j' * M.g j j'
  g_self j := by rw [L.g_self, M.g_self, one_mul]
  g_cocycle j j' j'' := by
    rw [resUnit_mul, resUnit_mul, resUnit_mul, mul_mul_mul_comm, L.g_cocycle, M.g_cocycle]

/-- The inverse cocycle of `L`, i.e. the transition data of the dual line bundle on the same
cover: invert every transition unit. -/
noncomputable def inv (L : LineBundleData X) : Cocycle L where
  g j j' := (L.g j j')⁻¹
  g_self j := by rw [L.g_self, inv_one]
  g_cocycle j j' j'' := by
    have h := L.g_cocycle j j' j''
    have h' : (resUnit inf_le_left (L.g j j') *
        resUnit (inf_le_inf inf_le_right (le_refl (L.U j'' : X.Opens))) (L.g j' j''))⁻¹ =
        (resUnit (inf_le_inf inf_le_left (le_refl (L.U j'' : X.Opens))) (L.g j j''))⁻¹ := by
      rw [h]
    rwa [mul_inv_rev, ← resUnit_inv, ← resUnit_inv, ← resUnit_inv, mul_comm] at h'

/-- The dual line bundle data: the inverse cocycle realised as line bundle data on the same
cover. -/
noncomputable def dual (L : LineBundleData X) : LineBundleData X := L.inv.toLineBundleData

end LineBundleData

/-- Combine membership in two opens into membership in their infimum.  Stated as a standalone
helper so that call sites unify against a clean signature instead of re-elaborating an ascribed
anonymous constructor (which is prone to inserting mismatched coercions). -/
lemma memInf {X : Scheme.{u}} {U U' : X.Opens} {x : X} (h : x ∈ U) (h' : x ∈ U') :
    x ∈ U ⊓ U' := ⟨h, h'⟩

namespace IntegralClosedSubscheme

variable {X : Scheme.{u}} (V : IntegralClosedSubscheme X)

/-- The image in `X` of the generic point of `V`, written `η_V` in the docstrings below. -/
noncomputable abbrev eta : X := V.inclusion.base (genericPoint V.scheme)

/-- `η_V` lies in every open of `X` meeting the image of `V`.  Since the generic point of `V`
is dense, it lies in every nonempty open of `V`, in particular in the preimage of such an open. -/
lemma eta_mem_of_mem_preimage {U : X.Opens} {x : V.scheme} (hx : V.inclusion.base x ∈ U) :
    V.eta ∈ U :=
  ((genericPoint_spec V.scheme).mem_open_set_iff (V.inclusion ⁻¹ᵁ U).isOpen).mpr
    ⟨x, Set.mem_univ x, hx⟩

/-- The ring hom from the sections of `X` over an open `U` containing `η_V` to the function
field of `V`: the germ of the section at `η_V` (computed in `X`), pushed along the stalk map of
`V`'s inclusion at `V`'s generic point. -/
noncomputable def toFunctionField (U : X.Opens) (h : V.eta ∈ U) :
    Γ(X, U) →+* V.scheme.functionField :=
  (V.inclusion.stalkMap (genericPoint V.scheme)).hom.comp (X.presheaf.germ U V.eta h).hom

/-- `toFunctionField` does not depend on which open (containing `η_V`) a section is presented
over: restricting to a smaller open first does not change the result. -/
lemma toFunctionField_res {U₀ U₁ : X.Opens} (h01 : U₀ ≤ U₁) (h0 : V.eta ∈ U₀) (h1 : V.eta ∈ U₁)
    (s : Γ(X, U₁)) :
    V.toFunctionField U₀ h0 ((X.presheaf.map (homOfLE h01).op).hom s) =
      V.toFunctionField U₁ h1 s := by
  simp only [toFunctionField, RingHom.comp_apply]
  congr 1
  exact X.presheaf.germ_res_apply (homOfLE h01) V.eta h0 s

/-- `toFunctionField` agrees with first pulling a section of `X` back to `V` along the
inclusion, then taking its germ at `V`'s generic point (i.e. `germToFunctionField`). -/
lemma toFunctionField_eq_germToFunctionField_app (U : X.Opens) (h : V.eta ∈ U) (a : Γ(X, U)) :
    haveI : Nonempty (V.inclusion ⁻¹ᵁ U) := ⟨⟨genericPoint V.scheme, h⟩⟩
    V.toFunctionField U h a =
      V.scheme.germToFunctionField (V.inclusion ⁻¹ᵁ U) ((V.inclusion.app U).hom a) := by
  simp only [toFunctionField, RingHom.comp_apply, Scheme.germToFunctionField]
  exact _root_.AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply V.inclusion U
    (genericPoint V.scheme) h a

end IntegralClosedSubscheme

namespace LineBundleData

variable {X : Scheme.{u}} (L : LineBundleData X) (V : IntegralClosedSubscheme X)

/-- The class, in the function field of `V`, of the transition unit `g j j'` restricted along
`V`'s generic point `η_V`.  Requires `η_V` to map into the overlap `U j ⊓ U j'`. -/
noncomputable def unitAt (j j' : L.J) (h : V.eta ∈ (L.U j : X.Opens) ⊓ (L.U j' : X.Opens)) :
    V.scheme.functionFieldˣ :=
  Units.map (V.toFunctionField _ h).toMonoidHom (L.g j j')

@[simp]
lemma unitAt_self (j : L.J) (h : V.eta ∈ (L.U j : X.Opens) ⊓ (L.U j : X.Opens)) :
    L.unitAt V j j h = 1 := by
  apply Units.ext
  simp [unitAt, L.g_self]

/-- The transition units restricted to `V` satisfy the same cocycle condition as on `X`. -/
lemma unitAt_mul (j j' j'' : L.J)
    (h : V.eta ∈ (L.U j : X.Opens) ⊓ (L.U j' : X.Opens) ⊓ (L.U j'' : X.Opens)) :
    L.unitAt V j j' h.1 * L.unitAt V j' j'' ⟨h.1.2, h.2⟩ =
      L.unitAt V j j'' ⟨h.1.1, h.2⟩ := by
  apply Units.ext
  have hval := congrArg Units.val (L.g_cocycle j j' j'')
  simp only [Units.val_mul, resUnit, Units.coe_map] at hval
  change V.toFunctionField ((L.U j : X.Opens) ⊓ (L.U j' : X.Opens)) h.1
        (L.g j j' : Γ(X, (L.U j : X.Opens) ⊓ (L.U j' : X.Opens))) *
      V.toFunctionField ((L.U j' : X.Opens) ⊓ (L.U j'' : X.Opens)) ⟨h.1.2, h.2⟩
        (L.g j' j'' : Γ(X, (L.U j' : X.Opens) ⊓ (L.U j'' : X.Opens))) =
    V.toFunctionField ((L.U j : X.Opens) ⊓ (L.U j'' : X.Opens)) ⟨h.1.1, h.2⟩
      (L.g j j'' : Γ(X, (L.U j : X.Opens) ⊓ (L.U j'' : X.Opens)))
  rw [← V.toFunctionField_res inf_le_left h h.1
      (L.g j j' : Γ(X, (L.U j : X.Opens) ⊓ (L.U j' : X.Opens))),
    ← V.toFunctionField_res (inf_le_inf inf_le_right (le_refl (L.U j'' : X.Opens))) h
      ⟨h.1.2, h.2⟩ (L.g j' j'' : Γ(X, (L.U j' : X.Opens) ⊓ (L.U j'' : X.Opens))),
    ← V.toFunctionField_res (inf_le_inf inf_le_left (le_refl (L.U j'' : X.Opens))) h
      ⟨h.1.1, h.2⟩ (L.g j j'' : Γ(X, (L.U j : X.Opens) ⊓ (L.U j'' : X.Opens))),
    ← RingHom.map_mul]
  congr 1

/-- Inverting the transition unit and restricting to `V` commute. -/
lemma unitAt_inv (j j' : L.J) (h : V.eta ∈ (L.U j : X.Opens) ⊓ (L.U j' : X.Opens)) :
    L.unitAt V j' j (by simpa [inf_comm] using h) = (L.unitAt V j j' h)⁻¹ := by
  have h' := L.unitAt_mul V j j' j ⟨h, h.1⟩
  rw [L.unitAt_self V j ⟨h.1, h.1⟩] at h'
  exact (inv_eq_of_mul_eq_one_right h').symm

/-- The transition units of a tensor product restrict to the product of the restricted
transition units. -/
lemma unitAt_tensor (M : Cocycle L) (j j' : L.J)
    (h : V.eta ∈ (L.U j : X.Opens) ⊓ (L.U j' : X.Opens)) :
    (L.tensor M).unitAt V j j' h = L.unitAt V j j' h * M.toLineBundleData.unitAt V j j' h := by
  apply Units.ext
  change (V.toFunctionField _ h : Γ(X, _) →+* _) (L.g j j' * M.g j j' : Γ(X, _)) =
      (V.toFunctionField _ h : Γ(X, _) →+* _) (L.g j j' : Γ(X, _)) *
        (V.toFunctionField _ h : Γ(X, _) →+* _) (M.g j j' : Γ(X, _))
  exact map_mul _ _ _

/-- A rational section of `L` along `V`: presented, in a chart `j₀` containing `η_V`, by the
function-field unit `f`.  Informally `s = f • e_{j₀}`. -/
structure RationalSection (L : LineBundleData X) (V : IntegralClosedSubscheme X) where
  /-- The distinguished chart in which the section is presented. -/
  j₀ : L.J
  /-- The distinguished chart contains `V`'s generic point. -/
  hj₀ : V.eta ∈ (L.U j₀ : X.Opens)
  /-- The coordinate of the section in the distinguished chart. -/
  f : V.scheme.functionFieldˣ

namespace RationalSection

variable {L V} (s : L.RationalSection V)

/-- The coordinate of a rational section in any chart `j` containing `η_V`. -/
noncomputable def coord (j : L.J) (hj : V.eta ∈ (L.U j : X.Opens)) : V.scheme.functionFieldˣ :=
  L.unitAt V j s.j₀ (memInf hj s.hj₀) * s.f

@[simp]
lemma coord_j₀ : s.coord s.j₀ s.hj₀ = s.f := by
  simp only [coord, L.unitAt_self, one_mul]

/-- The coordinates of a rational section in two charts are related by the transition unit. -/
lemma coord_eq_unitAt_mul_coord (j j' : L.J) (hj : V.eta ∈ (L.U j : X.Opens))
    (hj' : V.eta ∈ (L.U j' : X.Opens)) :
    s.coord j hj = L.unitAt V j j' (memInf hj hj') * s.coord j' hj' := by
  rw [coord, coord, ← mul_assoc]
  congr 1
  exact (L.unitAt_mul V j j' s.j₀ (memInf (memInf hj hj') s.hj₀)).symm

/-- The order of vanishing of a rational section at a point of `V`: the order of its coordinate
in a chart whose image in `X` contains the image of the point, computed via one such chart
chosen using `L.covers`.  Independent of that choice by `ord_well_defined`. -/
noncomputable def ord (x : V.scheme) : ℤ :=
  V.scheme.ord
    (s.coord (L.covers (V.inclusion.base x)).choose
      (V.eta_mem_of_mem_preimage (L.covers (V.inclusion.base x)).choose_spec)) x

/-- The order of a rational section at a point does not depend on the chart used to compute it,
as long as the chart's image in `X` contains the image of the point. -/
lemma ord_well_defined (j : L.J) (x : V.scheme)
    (hxj : V.inclusion.base x ∈ (L.U j : X.Opens)) :
    s.ord x = V.scheme.ord (s.coord j (V.eta_mem_of_mem_preimage hxj)) x := by
  set j₁ := (L.covers (V.inclusion.base x)).choose
  set hxj₁ := (L.covers (V.inclusion.base x)).choose_spec
  change V.scheme.ord (s.coord j₁ (V.eta_mem_of_mem_preimage hxj₁)) x = _
  rw [s.coord_eq_unitAt_mul_coord j₁ j (V.eta_mem_of_mem_preimage hxj₁)
    (V.eta_mem_of_mem_preimage hxj), Units.val_mul,
    Scheme.ord_mul (Units.ne_zero _) (Units.ne_zero _)]
  have hunit0 : V.scheme.ord
      (L.unitAt V j₁ j (memInf (V.eta_mem_of_mem_preimage hxj₁) (V.eta_mem_of_mem_preimage hxj)) :
        V.scheme.functionField) x = 0 := by
    rw [show (L.unitAt V j₁ j
          (memInf (V.eta_mem_of_mem_preimage hxj₁) (V.eta_mem_of_mem_preimage hxj)) :
          V.scheme.functionField) =
        V.toFunctionField ((L.U j₁ : X.Opens) ⊓ (L.U j : X.Opens))
          (memInf (V.eta_mem_of_mem_preimage hxj₁) (V.eta_mem_of_mem_preimage hxj))
          (L.g j₁ j : Γ(X, (L.U j₁ : X.Opens) ⊓ (L.U j : X.Opens))) from rfl,
      V.toFunctionField_eq_germToFunctionField_app]
    have : Nonempty (V.inclusion ⁻¹ᵁ ((L.U j₁ : X.Opens) ⊓ (L.U j : X.Opens))) :=
      ⟨⟨x, memInf hxj₁ hxj⟩⟩
    exact Scheme.ord_of_isUnit ((L.g j₁ j).isUnit.map (V.inclusion.app _).hom) (memInf hxj₁ hxj)
  rw [hunit0, zero_add]

/-- The Weil divisor cycle of a rational section on `V`: its coefficient at a point is the order
of vanishing there. -/
noncomputable def divisorCycle : AlgebraicCycle V.scheme ℚ where
  toFun x := (s.ord x : ℚ)
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' z _ := by
    obtain ⟨j, hzj⟩ := L.covers (V.inclusion.base z)
    have hj : V.eta ∈ (L.U j : X.Opens) := V.eta_mem_of_mem_preimage hzj
    obtain ⟨t, ht, hfinite⟩ := V.scheme.ord_support_locallyFinite (s.coord j hj) z
    refine ⟨t ∩ (V.inclusion ⁻¹ᵁ (L.U j : X.Opens) : Set V.scheme),
      Filter.inter_mem ht ((V.inclusion ⁻¹ᵁ (L.U j : X.Opens)).isOpen.mem_nhds hzj), ?_⟩
    apply hfinite.subset
    rintro x ⟨⟨hxt, hxpre⟩, hxord⟩
    refine ⟨hxt, ?_⟩
    intro hord0
    apply hxord
    change (s.ord x : ℚ) = 0
    rw [s.ord_well_defined j x hxpre]
    exact_mod_cast hord0

@[simp]
lemma divisorCycle_apply (x : V.scheme) : s.divisorCycle x = (s.ord x : ℚ) := rfl

/-- The divisor of a rational section, pushed forward to `X`. -/
noncomputable def divisor (dimension : DimensionFunction X) : AlgebraicCycle X ℚ :=
  V.pushforward dimension s.divisorCycle

/-- Scaling a rational section by a unit of the function field of `V`: same chart, coordinate
multiplied by the scalar. -/
noncomputable def smul (f : V.scheme.functionFieldˣ) (s : L.RationalSection V) :
    L.RationalSection V :=
  ⟨s.j₀, s.hj₀, f * s.f⟩

@[simp]
lemma smul_coord (f : V.scheme.functionFieldˣ) (j : L.J) (hj : V.eta ∈ (L.U j : X.Opens)) :
    (s.smul f).coord j hj = f * s.coord j hj := by
  simp only [coord, smul]
  exact mul_left_comm (L.unitAt V j s.j₀ (memInf hj s.hj₀)) f s.f

/-- The order of a scaled section is the order of the scalar plus the order of the section. -/
lemma smul_ord (f : V.scheme.functionFieldˣ) (x : V.scheme) :
    (s.smul f).ord x = V.scheme.ord (f : V.scheme.functionField) x + s.ord x := by
  obtain ⟨j, hzj⟩ := L.covers (V.inclusion.base x)
  have hj : V.eta ∈ (L.U j : X.Opens) := V.eta_mem_of_mem_preimage hzj
  rw [(s.smul f).ord_well_defined j x hzj, s.ord_well_defined j x hzj, s.smul_coord f j hj,
    Units.val_mul, Scheme.ord_mul (Units.ne_zero _) (Units.ne_zero _)]

/-- Scaling a rational section by a unit `f` adds the principal divisor of `f` to the divisor
cycle. -/
lemma smul_divisorCycle (f : V.scheme.functionFieldˣ) :
    (s.smul f).divisorCycle =
      V.scheme.principalCycle (f : V.scheme.functionField) + s.divisorCycle := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  simp only [divisorCycle_apply, Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
    Scheme.principalCycle_apply, smul_ord]
  push_cast
  ring

/-- For the trivial line bundle, the order of a rational section at a point agrees with the
order of vanishing of its coordinate as a rational function. -/
lemma ord_trivial {V : IntegralClosedSubscheme X} (s : (LineBundleData.trivial X).RationalSection V)
    (x : V.scheme) : s.ord x = V.scheme.ord (s.f : V.scheme.functionField) x := by
  obtain ⟨j, hzj⟩ := (LineBundleData.trivial X).covers ((V.inclusion).base x)
  have hj : V.eta ∈ ((LineBundleData.trivial X).U j : X.Opens) := V.eta_mem_of_mem_preimage hzj
  rw [s.ord_well_defined j x hzj, coord]
  have hg1 : (LineBundleData.trivial X).g j s.j₀ = 1 := rfl
  have : (LineBundleData.trivial X).unitAt V j s.j₀ (memInf hj s.hj₀) = 1 := by
    unfold LineBundleData.unitAt
    rw [hg1, map_one]
  rw [this, one_mul]

/-- For the trivial line bundle, the divisor cycle of a rational section is the principal cycle
of its coordinate. -/
lemma divisorCycle_trivial {V : IntegralClosedSubscheme X}
    (s : (LineBundleData.trivial X).RationalSection V) :
    s.divisorCycle = V.scheme.principalCycle (s.f : V.scheme.functionField) := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  simp [divisorCycle_apply, Scheme.principalCycle_apply, ord_trivial]

/-- Present a rational section in a different distinguished chart: the same underlying section,
recorded via a different chart `j₀'` using the transition unit. -/
noncomputable def reChart (s : L.RationalSection V) (j₀' : L.J)
    (hj₀' : V.eta ∈ (L.U j₀' : X.Opens)) : L.RationalSection V :=
  ⟨j₀', hj₀', L.unitAt V j₀' s.j₀ (memInf hj₀' s.hj₀) * s.f⟩

/-- Re-charting a rational section does not change its coordinate in any chart. -/
lemma coord_reChart (s : L.RationalSection V) (j₀' : L.J) (hj₀' : V.eta ∈ (L.U j₀' : X.Opens))
    (j : L.J) (hj : V.eta ∈ (L.U j : X.Opens)) :
    (s.reChart j₀' hj₀').coord j hj = s.coord j hj := by
  simp only [coord, reChart, ← mul_assoc]
  congr 1
  exact L.unitAt_mul V j j₀' s.j₀ (memInf (memInf hj hj₀') s.hj₀)

/-- Re-charting a rational section does not change its order at any point. -/
lemma ord_reChart (s : L.RationalSection V) (j₀' : L.J) (hj₀' : V.eta ∈ (L.U j₀' : X.Opens))
    (x : V.scheme) : (s.reChart j₀' hj₀').ord x = s.ord x := by
  obtain ⟨j, hzj⟩ := L.covers (V.inclusion.base x)
  have hj : V.eta ∈ (L.U j : X.Opens) := V.eta_mem_of_mem_preimage hzj
  rw [(s.reChart j₀' hj₀').ord_well_defined j x hzj, s.ord_well_defined j x hzj,
    s.coord_reChart j₀' hj₀' j hj]

/-- Re-charting a rational section does not change its divisor cycle. -/
lemma divisorCycle_reChart (s : L.RationalSection V) (j₀' : L.J)
    (hj₀' : V.eta ∈ (L.U j₀' : X.Opens)) :
    (s.reChart j₀' hj₀').divisorCycle = s.divisorCycle := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  simp [divisorCycle_apply, ord_reChart]

/-- Re-charting a rational section does not change its divisor on `X`. -/
lemma divisor_eq_of_chart_change (dimension : DimensionFunction X) (s : L.RationalSection V)
    (j₀' : L.J) (hj₀' : V.eta ∈ (L.U j₀' : X.Opens)) :
    (s.reChart j₀' hj₀').divisor dimension = s.divisor dimension := by
  simp only [divisor, divisorCycle_reChart]

/-- Every line bundle admits a rational section along `V`. -/
lemma exists_rationalSection : Nonempty (L.RationalSection V) := by
  obtain ⟨j₀, hj₀⟩ := L.covers V.eta
  exact ⟨⟨j₀, hj₀, 1⟩⟩

/-- Replacing a rational section's coordinate `s.f` by another unit `g` (same chart) is scaling
by `g * s.f⁻¹`. -/
lemma mk_eq_smul (s : L.RationalSection V) (g : V.scheme.functionFieldˣ) :
    (⟨s.j₀, s.hj₀, g⟩ : L.RationalSection V) = s.smul (g * s.f⁻¹) := by
  simp only [smul]
  congr 1
  rw [mul_assoc, inv_mul_cancel, mul_one]

/-- Two rational sections with the same distinguished chart differ by the principal cycle of the
ratio of their coordinates. -/
lemma divisorCycle_sub_mk (s : L.RationalSection V) (g : V.scheme.functionFieldˣ) :
    s.divisorCycle - (⟨s.j₀, s.hj₀, g⟩ : L.RationalSection V).divisorCycle =
      V.scheme.principalCycle ((s.f * g⁻¹ : V.scheme.functionFieldˣ) : V.scheme.functionField) := by
  rw [mk_eq_smul s g, s.smul_divisorCycle]
  have hinv : (s.f * g⁻¹ : V.scheme.functionFieldˣ) = (g * s.f⁻¹ : V.scheme.functionFieldˣ)⁻¹ := by
    rw [mul_inv_rev, inv_inv]
  rw [hinv, Units.val_inv_eq_inv_val,
    V.scheme.principalCycle_inv (Units.ne_zero _)]
  abel

/-- Two rational sections of the same line bundle `L` along `V` differ, after pushing forward to
`X`, by the divisor of a rational function on `V`; hence their divisors on `X` are rationally
equivalent. -/
lemma divisor_mem_totalRationalRelations_of_sub (dimension : DimensionFunction X)
    (s t : L.RationalSection V) :
    s.divisor dimension - t.divisor dimension ∈ totalRationalRelations X dimension := by
  set t' : L.RationalSection V := ⟨s.j₀, s.hj₀, L.unitAt V s.j₀ t.j₀ (memInf s.hj₀ t.hj₀) * t.f⟩
    with ht'
  have ht'eq : t' = t.reChart s.j₀ s.hj₀ := rfl
  have hdiv : t.divisor dimension = t'.divisor dimension := by
    rw [ht'eq, (t.divisor_eq_of_chart_change dimension s.j₀ s.hj₀).symm]
  rw [hdiv]
  have hcyc : s.divisorCycle - t'.divisorCycle =
      V.scheme.principalCycle ((s.f * t'.f⁻¹ : V.scheme.functionFieldˣ) : V.scheme.functionField) :=
    s.divisorCycle_sub_mk t'.f
  have hsub : s.divisor dimension - t'.divisor dimension =
      V.pushforward dimension (s.divisorCycle - t'.divisorCycle) := by
    simp only [divisor]
    exact (map_sub (GromovWitten.AlgebraicGeometry.IntersectionTheory.AlgebraicCycle.mapLinear
      V.inclusion (fun z ↦ dimension (V.inclusion.base z)) dimension) s.divisorCycle
      t'.divisorCycle).symm
  rw [hsub, hcyc]
  exact Submodule.subset_span
    ⟨⟨V, (s.f * t'.f⁻¹ : V.scheme.functionFieldˣ)⟩, rfl⟩

/-- The tensor product of a rational section of `L` and a rational section of a second cocycle
`M` on the same cover, along the same subscheme `V`: a rational section of `L.tensor M`. The
second section is re-charted to `s`'s chart before multiplying coordinates. -/
noncomputable def tensor (M : LineBundleData.Cocycle L) (t : M.toLineBundleData.RationalSection V) :
    (L.tensor M).RationalSection V :=
  ⟨s.j₀, s.hj₀, s.f * (t.reChart s.j₀ s.hj₀).f⟩

/-- The coordinate of a tensor-product section is the product of the coordinates of the
factors (after re-charting the second factor to a common chart). -/
lemma tensor_coord (M : LineBundleData.Cocycle L) (t : M.toLineBundleData.RationalSection V)
    (j : L.J) (hj : V.eta ∈ (L.U j : X.Opens)) :
    (s.tensor M t).coord j hj = s.coord j hj * (t.reChart s.j₀ s.hj₀).coord j hj := by
  simp only [coord, tensor]
  rw [L.unitAt_tensor V M j s.j₀ (memInf hj s.hj₀)]
  exact mul_mul_mul_comm _ _ _ _

/-- The order of a tensor-product section is the sum of the orders of its factors. -/
lemma tensor_ord (M : LineBundleData.Cocycle L) (t : M.toLineBundleData.RationalSection V)
    (x : V.scheme) : (s.tensor M t).ord x = s.ord x + t.ord x := by
  obtain ⟨j, hzj⟩ := L.covers (V.inclusion.base x)
  have hj : V.eta ∈ (L.U j : X.Opens) := V.eta_mem_of_mem_preimage hzj
  rw [(s.tensor M t).ord_well_defined j x hzj, s.ord_well_defined j x hzj,
    s.tensor_coord M t j hj, Units.val_mul,
    Scheme.ord_mul (Units.ne_zero _) (Units.ne_zero _),
    ← (t.reChart s.j₀ s.hj₀).ord_well_defined j x hzj, t.ord_reChart s.j₀ s.hj₀ x]

/-- The divisor cycle of a tensor product is the sum of the divisor cycles of its factors. -/
lemma tensor_divisorCycle (M : LineBundleData.Cocycle L)
    (t : M.toLineBundleData.RationalSection V) :
    (s.tensor M t).divisorCycle = s.divisorCycle + t.divisorCycle := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  simp [divisorCycle_apply, tensor_ord]

end RationalSection

end LineBundleData

end GromovWitten.AlgebraicGeometry.IntersectionTheory
