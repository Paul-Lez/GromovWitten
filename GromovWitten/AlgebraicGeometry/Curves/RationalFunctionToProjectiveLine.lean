/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import GromovWitten.AlgebraicGeometry.ProjectiveLine

/-!
# The morphism to `ℙ¹` defined by a rational function

Let `W` be an integral scheme and `r` a nonzero element of its function field `K(W)`.  This file
constructs the *domain of definition* of `r`, namely the largest open subset of `W` on which `r`
is a regular function, and — once `W` is a curve, so that `r` or `r⁻¹` is regular at every
point — the induced morphism `W ⟶ ℙ¹_k`.

## Main declarations

### The domain of definition of a rational function (`X` integral)

* `Scheme.RegularRep X r` — a local representative `(U, s)` of a rational function `r`: an open
  set `U` containing the generic point together with a section over `U` whose germ at the generic
  point is `r`.
* `Scheme.regularLocus r` — the union of all such `U`; the open locus where `r` is regular.
* `Scheme.regularSection r : Γ(X, regularLocus r)` — the regular function on `regularLocus r`
  defined by `r`, obtained by gluing the local representatives (the sheaf condition);
  `Scheme.germ_regularSection` identifies its germ at the generic point with `r`, and
  `Scheme.eq_regularSection` says it is the unique such section.
* `Scheme.mem_regularLocus_iff` — `x ∈ regularLocus r` iff `r` lies in the image of the local
  ring `𝒪_{X,x} → K(X)`.
* `Scheme.regularLocus_sup_regularLocus_inv_eq_top` — if every local ring of `X` is a valuation
  ring (e.g. `X` a regular curve, by `Scheme.valuationRing_stalk`) then
  `regularLocus r ⊔ regularLocus r⁻¹ = ⊤`.

### The morphism to `ℙ¹_k` (`W` a `k`-scheme, `f : W ⟶ Spec k`)

* `RationalFunction.toChart f U σ : U ⟶ 𝔸¹_k` — the morphism to the first standard chart defined
  by a regular function `σ` on an open set `U`, with `toChart_comp_chartToSpecK` (it is a morphism
  over `Spec k`), `homOfLE_comp_toChart` (naturality in `U`) and `toChart_appTop_coord` (it pulls
  the coordinate `t` back to `σ`).
* `RationalFunction.toChart_chartZero_eq_toChart_chartOne` — the gluing identity: if `σ * τ = 1`
  then `toChart σ ≫ chartZero = toChart τ ≫ chartOne`, both factoring through `Spec k[t,t⁻¹]`.
* `RationalFunction.ChartPair W r` — gluing data for `r`: two open sets covering `W` carrying
  regular functions representing `r` and `r⁻¹`; `ChartPair.toProjectiveLine` is the glued morphism
  `W ⟶ ℙ¹_k`, with `ChartPair.toProjectiveLine_comp_structureMap` (it is a morphism of
  `k`-schemes) and `ChartPair.base_genericPoint` (it is dominant if `r` is transcendental).
* `RationalFunction.toProjectiveLine f hv r hr` — the morphism attached to the canonical gluing
  data of a nonzero `r` on a scheme whose local rings are valuation rings.
* `RationalFunction.isProper_toProjectiveLine`, `RationalFunction.finite_preimage_singleton` and
  `RationalFunction.isFinite_toProjectiveLine` — the morphism is proper, has finite fibres, and is
  finite, under the explicit hypotheses that `ℙ¹_k` be separated over `k`, that `W` be proper over
  `k` and one-dimensional, and that `r` be transcendental over `k`.

-/

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace GromovWitten.AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}}

section RegularLocus

variable [IsIntegral X]

/-- A local representative of a rational function `r` on an integral scheme `X`: an open set `U`
containing the generic point, together with a section of the structure sheaf over `U` whose germ
at the generic point is `r`.  (The germ at the generic point is by definition the map
`Γ(X, U) → K(X)`, see `Scheme.germToFunctionField`.) -/
structure RegularRep (X : Scheme.{u}) [IrreducibleSpace X] (r : X.functionField) where
  /-- The open set on which the representative is defined. -/
  U : X.Opens
  /-- The generic point lies in `U`. -/
  mem : genericPoint X ∈ U
  /-- The section representing `r`. -/
  s : Γ(X, U)
  /-- The section represents `r`. -/
  germ_eq : X.presheaf.germ U (genericPoint X) mem s = r

/-- **The domain of definition of a rational function**: the union of all the opens on which `r`
is given by a regular function.  It is the largest open subset of `X` on which `r` is regular,
see `Scheme.mem_regularLocus_iff`. -/
def regularLocus (r : X.functionField) : X.Opens := ⨆ p : RegularRep X r, p.U

/-- Each local representative is defined on an open subset of the domain of definition. -/
lemma le_regularLocus (r : X.functionField) (p : RegularRep X r) : p.U ≤ regularLocus r :=
  le_iSup (fun p : RegularRep X r => p.U) p

/-- Every rational function has a local representative around the generic point. -/
lemma nonempty_regularRep (r : X.functionField) : Nonempty (RegularRep X r) := by
  obtain ⟨U, hU, s, hs⟩ := X.presheaf.exists_germ_eq (x := genericPoint X) r
  exact ⟨U, hU, s, hs⟩

/-- A local representative of `r` around the generic point. -/
noncomputable def genericRep (r : X.functionField) : RegularRep X r :=
  (nonempty_regularRep r).some

lemma genericPoint_mem_regularLocus (r : X.functionField) :
    genericPoint X ∈ regularLocus r :=
  le_regularLocus r (genericRep r) (genericRep r).mem

instance nonempty_regularLocus (r : X.functionField) : Nonempty (regularLocus r) :=
  ⟨⟨genericPoint X, genericPoint_mem_regularLocus r⟩⟩

/-- Every nonempty open subset of an irreducible space contains the generic point. -/
lemma genericPoint_mem_of_nonempty (U : X.Opens) [Nonempty U] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

/-- **The regular locus of `r` is exactly the set of points where `r` lies in the local ring.** -/
lemma mem_regularLocus_iff {r : X.functionField} {x : X} :
    x ∈ regularLocus r ↔ ∃ ρ : X.presheaf.stalk x, algebraMap _ X.functionField ρ = r := by
  constructor
  · intro hx
    obtain ⟨p, hp⟩ := Opens.mem_iSup.mp hx
    have : Nonempty p.U := ⟨⟨genericPoint X, p.mem⟩⟩
    refine ⟨X.presheaf.germ p.U x hp p.s, ?_⟩
    rw [X.algebraMap_germ_eq_germToFunctionField hp p.s]
    exact p.germ_eq
  · rintro ⟨ρ, hρ⟩
    obtain ⟨U, hxU, s, hs⟩ := X.presheaf.exists_germ_eq ρ
    have hne : Nonempty U := ⟨⟨x, hxU⟩⟩
    have hgen : genericPoint X ∈ U := genericPoint_mem_of_nonempty U
    have hres : X.presheaf.germ U (genericPoint X) hgen s = r := by
      rw [← X.algebraMap_germ_eq_germToFunctionField hxU s, hs, hρ]
    exact le_regularLocus r ⟨U, hgen, s, hres⟩ hxU

/-- The local representatives of `r` form a compatible family of sections. -/
lemma regularRep_isCompatible (r : X.functionField) :
    TopCat.Presheaf.IsCompatible X.presheaf (fun p : RegularRep X r => p.U)
      (fun p => p.s) := by
  intro p q
  have hmem : genericPoint X ∈ p.U ⊓ q.U := ⟨p.mem, q.mem⟩
  refine germ_injective_of_isIntegral X (genericPoint X) hmem ?_
  rw [X.presheaf.germ_res_apply (Opens.infLELeft p.U q.U) _ hmem,
    X.presheaf.germ_res_apply (Opens.infLERight p.U q.U) _ hmem, p.germ_eq, q.germ_eq]

/-- **A rational function is a regular function on its domain of definition.** -/
noncomputable def regularSection (r : X.functionField) : Γ(X, regularLocus r) :=
  (X.sheaf.existsUnique_gluing' (fun p : RegularRep X r => p.U) (regularLocus r)
    (fun p => homOfLE (le_regularLocus r p)) le_rfl (fun p => p.s)
    (regularRep_isCompatible r)).exists.choose

/-- The regular function defined by `r` restricts to each of its local representatives. -/
lemma map_regularSection (r : X.functionField) (p : RegularRep X r) :
    X.presheaf.map (homOfLE (le_regularLocus r p)).op (regularSection r) = p.s :=
  (X.sheaf.existsUnique_gluing' (fun p : RegularRep X r => p.U) (regularLocus r)
    (fun p => homOfLE (le_regularLocus r p)) le_rfl (fun p => p.s)
    (regularRep_isCompatible r)).exists.choose_spec p

/-- **The regular function defined by `r` on its domain of definition represents `r`.** -/
lemma germ_regularSection (r : X.functionField) :
    X.presheaf.germ (regularLocus r) (genericPoint X) (genericPoint_mem_regularLocus r)
      (regularSection r) = r := by
  have h2 := X.presheaf.germ_res_apply (homOfLE (le_regularLocus r (genericRep r)))
    (genericPoint X) (genericRep r).mem (regularSection r)
  rw [← h2, map_regularSection r (genericRep r), (genericRep r).germ_eq]

/-- **At every point where `r` or `r⁻¹` is integral over the local ring**, the point lies in the
domain of definition of `r` or of `r⁻¹`.  Consequently, if all local rings of `X` are valuation
rings — e.g. if `X` is a regular integral curve, where the local ring at a closed point is a
discrete valuation ring and the local ring at the generic point is the function field — then the
two domains of definition cover `X`. -/
theorem regularLocus_sup_regularLocus_inv_eq_top
    (hv : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (r : X.functionField) :
    regularLocus r ⊔ regularLocus r⁻¹ = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  have := hv x
  rcases ValuationRing.isInteger_or_isInteger (X.presheaf.stalk x) r with ⟨ρ, hρ⟩ | ⟨ρ, hρ⟩
  · exact Opens.mem_sup.mpr (Or.inl (mem_regularLocus_iff.mpr ⟨ρ, hρ⟩))
  · exact Opens.mem_sup.mpr (Or.inr (mem_regularLocus_iff.mpr ⟨ρ, hρ⟩))

/-- On an integral scheme whose local rings at the non-generic points are discrete valuation
rings (e.g. a regular integral curve) every local ring is a valuation ring: the local ring at the
generic point is the function field, which is a field. -/
theorem valuationRing_stalk (hdvr : ∀ x : X, x ≠ genericPoint X →
    IsDiscreteValuationRing (X.presheaf.stalk x)) (x : X) : ValuationRing (X.presheaf.stalk x) := by
  by_cases hx : x = genericPoint X
  · subst hx
    exact ValuationRing.of_field _
  · have := hdvr x hx
    infer_instance

/-- **The regular function representing a rational function on its domain of definition is
unique.** -/
lemma eq_regularSection {r : X.functionField} (s : Γ(X, regularLocus r))
    (hs : X.presheaf.germ (regularLocus r) (genericPoint X)
      (genericPoint_mem_regularLocus r) s = r) : s = regularSection r :=
  germ_injective_of_isIntegral X (genericPoint X) (genericPoint_mem_regularLocus r)
    (by rw [hs, germ_regularSection])

end RegularLocus

end Scheme

namespace RationalFunction

open ProjectiveLine

variable {k : Type u} [Field k] {W : Scheme.{u}} (f : W ⟶ Spec (CommRingCat.of k))

/-- The `k`-algebra structure on the sections of `𝒪_W` over an open set `U`, induced by the
structure morphism `f : W ⟶ Spec k`. -/
noncomputable def kSection (U : W.Opens) : CommRingCat.of k ⟶ Γ(W, U) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ U (le_top.trans (Opens.map_top _).ge)

/-- The `k`-algebra structures on sections are compatible with restriction. -/
lemma kSection_res {U V : W.Opens} (h : V ≤ U) :
    kSection f U ≫ W.presheaf.map (homOfLE h).op = kSection f V := by
  rw [kSection, kSection, Category.assoc, Scheme.Hom.appLE_map]

/-- The `k`-algebra map `k[t] → Γ(W, U)` sending the coordinate `t` to a section `σ`. -/
noncomputable def toChartHom (U : W.Opens) (σ : Γ(W, U)) :
    CommRingCat.of (Polynomial k) ⟶ Γ(W, U) :=
  CommRingCat.ofHom (Polynomial.eval₂RingHom (kSection f U).hom σ)

/-- **The morphism to the first standard chart `𝔸¹_k` of `ℙ¹_k` defined by a regular function**
`σ` on an open subset `U` of `W`. -/
noncomputable def toChart (U : W.Opens) (σ : Γ(W, U)) : U.toScheme ⟶ chart k :=
  U.toSpecΓ ≫ Spec.map (toChartHom f U σ)

/-- The ring maps `k[t] → Γ(W, U)` are compatible with restriction. -/
lemma toChartHom_res {U V : W.Opens} (h : V ≤ U) (σ : Γ(W, U)) :
    toChartHom f U σ ≫ W.presheaf.map (homOfLE h).op
      = toChartHom f V (W.presheaf.map (homOfLE h).op σ) := by
  have hC := kSection_res f h
  refine CommRingCat.hom_ext (Polynomial.ringHom_ext ?_ ?_)
  · intro a
    have := congrArg (fun g : CommRingCat.of k ⟶ Γ(W, V) => g.hom a) hC
    simpa [toChartHom] using this
  · simp [toChartHom]

/-- **Naturality of `toChart` in the open set**: the morphism attached to a section restricts to
the morphism attached to its restriction. -/
lemma homOfLE_comp_toChart {U V : W.Opens} (h : V ≤ U) (σ : Γ(W, U)) :
    W.homOfLE h ≫ toChart f U σ = toChart f V (W.presheaf.map (homOfLE h).op σ) := by
  rw [toChart, toChart, ← toChartHom_res f h σ, Spec.map_comp,
    Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc]

/-- A section with an inverse is a unit. -/
lemma isUnit_eval₂_X (U : W.Opens) (σ τ : Γ(W, U)) (hστ : σ * τ = 1) :
    IsUnit (Polynomial.eval₂RingHom (kSection f U).hom σ Polynomial.X) := by
  simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  exact ⟨⟨σ, τ, hστ, (mul_comm τ σ).trans hστ⟩, rfl⟩

/-- The `k`-algebra map `k[t, t⁻¹] → Γ(W, U)` sending `t` to a unit section `σ`, whose inverse
is `τ`. -/
noncomputable def toOverlapHom (U : W.Opens) (σ τ : Γ(W, U)) (hστ : σ * τ = 1) :
    CommRingCat.of (overlapRing k) ⟶ Γ(W, U) :=
  CommRingCat.ofHom (IsLocalization.Away.lift (S := overlapRing k) (Polynomial.X : Polynomial k)
    (g := Polynomial.eval₂RingHom (kSection f U).hom σ) (isUnit_eval₂_X f U σ τ hστ))

/-- The map `k[t,t⁻¹] → Γ(W, U)` extends the map `k[t] → Γ(W, U)`. -/
lemma algebraMap_comp_toOverlapHom (U : W.Opens) (σ τ : Γ(W, U)) (hστ : σ * τ = 1) :
    CommRingCat.ofHom (algebraMap (Polynomial k) (overlapRing k)) ≫ toOverlapHom f U σ τ hστ
      = toChartHom f U σ :=
  CommRingCat.hom_ext
    (IsLocalization.Away.lift_comp (Polynomial.X : Polynomial k) (isUnit_eval₂_X f U σ τ hστ))

/-- The map `k[t,t⁻¹] → Γ(W, U)` sends `t⁻¹` to the inverse section `τ`. -/
lemma toOverlapHom_tInv (U : W.Opens) (σ τ : Γ(W, U)) (hστ : σ * τ = 1) :
    (toOverlapHom f U σ τ hστ).hom (tInv k) = τ := by
  have h1 : (toOverlapHom f U σ τ hστ).hom
      (algebraMap (Polynomial k) (overlapRing k) Polynomial.X) = σ := by
    simpa only [toOverlapHom, CommRingCat.hom_ofHom, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X] using
      IsLocalization.Away.lift_eq (S := overlapRing k) (Polynomial.X : Polynomial k)
        (g := Polynomial.eval₂RingHom (kSection f U).hom σ)
        (isUnit_eval₂_X f U σ τ hστ) Polynomial.X
  have h2 := congrArg (toOverlapHom f U σ τ hστ).hom (algebraMap_X_mul_tInv k)
  rw [map_mul, map_one, h1] at h2
  refine Eq.symm ?_
  calc τ = τ * (σ * (toOverlapHom f U σ τ hστ).hom (tInv k)) := by rw [h2, mul_one]
    _ = (τ * σ) * (toOverlapHom f U σ τ hστ).hom (tInv k) := by rw [mul_assoc]
    _ = (toOverlapHom f U σ τ hστ).hom (tInv k) := by rw [mul_comm τ σ, hστ, one_mul]

/-- Composed with the transition map `s ↦ t⁻¹`, the map `k[t,t⁻¹] → Γ(W, U)` is the map
`k[s] → Γ(W, U)` sending the coordinate to the inverse section `τ`. -/
lemma flipHom_comp_toOverlapHom (U : W.Opens) (σ τ : Γ(W, U)) (hστ : σ * τ = 1) :
    CommRingCat.ofHom (flipHom k) ≫ toOverlapHom f U σ τ hστ = toChartHom f U τ := by
  refine CommRingCat.hom_ext (Polynomial.ringHom_ext ?_ ?_)
  · intro a
    have := congrArg (fun g : CommRingCat.of (Polynomial k) ⟶ Γ(W, U) => g.hom (Polynomial.C a))
      (algebraMap_comp_toOverlapHom f U σ τ hστ)
    simpa [toChartHom] using this
  · simp [toChartHom, toOverlapHom_tInv f U σ τ hστ]

/-- The morphism to the first chart factors through the overlap `Spec k[t,t⁻¹]`. -/
lemma toChart_comp_chartZero (U : W.Opens) (σ τ : Γ(W, U)) (hστ : σ * τ = 1) :
    toChart f U σ ≫ chartZero k
      = U.toSpecΓ ≫ Spec.map (toOverlapHom f U σ τ hστ) ≫ overlapι k := by
  rw [← overlapToChartZero_comp k, toChart, ← algebraMap_comp_toOverlapHom f U σ τ hστ,
    Spec.map_comp]
  simp only [Category.assoc]

/-- The morphism to the second chart defined by the inverse section factors through the overlap. -/
lemma toChart_comp_chartOne (U : W.Opens) (σ τ : Γ(W, U)) (hστ : σ * τ = 1) :
    toChart f U τ ≫ chartOne k
      = U.toSpecΓ ≫ Spec.map (toOverlapHom f U σ τ hστ) ≫ overlapι k := by
  rw [← overlapToChartOne_comp k, toChart, ← flipHom_comp_toOverlapHom f U σ τ hστ, Spec.map_comp]
  simp only [Category.assoc]

/-- **The gluing identity for the two standard charts of `ℙ¹_k`.**  If `σ` and `τ` are mutually
inverse regular functions on `U`, the morphism `U ⟶ 𝔸¹_k` given by `σ` followed by the first chart
agrees with the morphism given by `τ` followed by the second chart.  (Applying the lemma with `σ`
and `τ` interchanged gives the mirrored identity.) -/
theorem toChart_chartZero_eq_toChart_chartOne (U : W.Opens) (σ τ : Γ(W, U)) (hστ : σ * τ = 1) :
    toChart f U σ ≫ chartZero k = toChart f U τ ≫ chartOne k := by
  rw [toChart_comp_chartZero f U σ τ hστ, toChart_comp_chartOne f U σ τ hστ]

/-- The ring map `k → Γ(W, U)` factors through `k[t] → Γ(W, U)`. -/
lemma algebraMap_comp_toChartHom (U : W.Opens) (σ : Γ(W, U)) :
    CommRingCat.ofHom (algebraMap k (Polynomial k)) ≫ toChartHom f U σ = kSection f U := by
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  simp [toChartHom, Polynomial.algebraMap_eq]

/-- **The morphism to the standard chart is a morphism over `Spec k`.** -/
lemma toChart_comp_chartToSpecK (U : W.Opens) (σ : Γ(W, U)) :
    toChart f U σ ≫ chartToSpecK k = U.ι ≫ f := by
  rw [toChart, chartToSpecK, Category.assoc, ← Spec.map_comp, algebraMap_comp_toChartHom,
    kSection, Spec.map_comp, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc,
    Scheme.Opens.toSpecΓ_top, Category.assoc,
    AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id,
    Scheme.Hom.resLE_comp_ι]

/-- Two morphisms out of the pullback of a monomorphism with itself which differ only by the two
projections agree. -/
lemma pullback_self_hom_ext {A B Y : Scheme.{u}} (g : A ⟶ B) [Mono g] (h : A ⟶ Y) :
    pullback.fst g g ≫ h = pullback.snd g g ≫ h :=
  congrArg (· ≫ h) ((cancel_mono g).mp pullback.condition)

/-- **Two morphisms defined on two open subschemes of `W` which agree on the intersection agree
on the pullback** of the two open immersions.  This is the form of the compatibility condition
required by `AlgebraicGeometry.Scheme.Cover.glueMorphisms`. -/
lemma pullback_hom_ext {Y : Scheme.{u}} (U V : W.Opens) (g₀ : U.toScheme ⟶ Y) (g₁ : V.toScheme ⟶ Y)
    (h : W.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ g₀
      = W.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ g₁) :
    pullback.fst U.ι V.ι ≫ g₀ = pullback.snd U.ι V.ι ≫ g₁ := by
  have hrange : Set.range (W.homOfLE (inf_le_left : U ⊓ V ≤ U))
      = Set.range (pullback.fst U.ι V.ι) := by
    rw [IsOpenImmersion.range_pullbackFst, ← Scheme.Hom.coe_opensRange,
      Scheme.opensRange_homOfLE]
    have hmem : ∀ x : U.toScheme, U.ι.base x ∈ (U : Set W) := by
      intro x
      rw [← Scheme.Opens.range_ι U]
      exact Set.mem_range_self x
    rw [Scheme.Opens.opensRange_ι]
    exact Set.eq_of_subset_of_subset (fun x hx => hx.2) (fun x hx => ⟨hmem x, hx⟩)
  have hfst : (IsOpenImmersion.isoOfRangeEq _ _ hrange).hom ≫ pullback.fst U.ι V.ι
      = W.homOfLE (inf_le_left : U ⊓ V ≤ U) :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange
  have hsnd : (IsOpenImmersion.isoOfRangeEq _ _ hrange).hom ≫ pullback.snd U.ι V.ι
      = W.homOfLE (inf_le_right : U ⊓ V ≤ V) := by
    rw [← cancel_mono V.ι, Category.assoc, ← pullback.condition, Scheme.homOfLE_ι,
      ← Category.assoc, hfst, Scheme.homOfLE_ι]
  rw [← cancel_epi (IsOpenImmersion.isoOfRangeEq _ _ hrange).hom, ← Category.assoc,
    ← Category.assoc, hfst, hsnd]
  exact h

section Dominance

/-- The contraction of the zero ideal along an injective ring map is the zero ideal. -/
private lemma asIdeal_comap_eq_bot {R S : CommRingCat.{u}} (ψ : R ⟶ S) (p : PrimeSpectrum S)
    (hp : p.asIdeal = ⊥) (hψ : Function.Injective ψ.hom) :
    (PrimeSpectrum.comap ψ.hom p).asIdeal = ⊥ := by
  rw [PrimeSpectrum.comap_asIdeal, hp]
  exact Ideal.comap_bot_of_injective _ hψ

/-- **The canonical morphism `X ⟶ Spec Γ(X, ⊤)` of an integral scheme sends the generic point to
the generic point**, i.e. to the zero ideal. -/
lemma asIdeal_toSpecΓ_base_genericPoint (X : Scheme.{u}) [IsIntegral X] :
    PrimeSpectrum.asIdeal ((X.toSpecΓ).base (genericPoint X)) = ⊥ := by
  have hginj : Function.Injective (X.presheaf.germ ⊤ (genericPoint X) trivial) :=
    germ_injective_of_isIntegral X (U := ⊤) (genericPoint X) trivial
  have h : (X.toSpecΓ).base (genericPoint X)
      = PrimeSpectrum.comap (X.presheaf.Γgerm (genericPoint X)).hom
        (IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X))) :=
    Scheme.toSpecΓ_apply X _
  rw [h]
  refine asIdeal_comap_eq_bot _ _ ?_ hginj
  exact IsLocalRing.maximalIdeal_eq_bot

/-- The canonical morphism `U ⟶ Spec Γ(X, U)` of a nonempty open subscheme of an integral scheme
sends the generic point to the zero ideal. -/
lemma asIdeal_opensToSpecΓ_base_genericPoint {X : Scheme.{u}} [IsIntegral X] (U : X.Opens)
    [Nonempty U] :
    PrimeSpectrum.asIdeal ((U.toSpecΓ).base (genericPoint U.toScheme)) = ⊥ :=
  asIdeal_comap_eq_bot _ _ (asIdeal_toSpecΓ_base_genericPoint U.toScheme)
    (ConcreteCategory.bijective_of_isIso U.topIso.inv).injective

/-- **The morphism to the first standard chart is dominant** as soon as the corresponding ring map
`k[t] → Γ(W, U)` is injective: it sends the generic point to the generic point. -/
theorem toChart_base_genericPoint [IsIntegral W] (U : W.Opens) [Nonempty U] (σ : Γ(W, U))
    (hinj : Function.Injective (toChartHom f U σ).hom) :
    (toChart f U σ).base (genericPoint U.toScheme) = genericPoint (chart k) := by
  rw [genericPoint_eq_bot_of_affine]
  exact PrimeSpectrum.ext
    (asIdeal_comap_eq_bot _ _ (asIdeal_opensToSpecΓ_base_genericPoint U) hinj)

/-- The `k`-algebra structure on the function field of `W` induced by the structure morphism `f`. -/
noncomputable def kFunctionField [IsIntegral W] : CommRingCat.of k ⟶ W.functionField :=
  kSection f ⊤ ≫ W.presheaf.germ ⊤ (genericPoint W) trivial

/-- The composition of `k[t] → Γ(W, U)` with the germ at the generic point is the `k`-algebra map
`k[t] → K(W)` sending the coordinate to the rational function represented by `σ`. -/
lemma toChartHom_comp_germ [IsIntegral W] (U : W.Opens) (hU : genericPoint W ∈ U) (σ : Γ(W, U)) :
    toChartHom f U σ ≫ W.presheaf.germ U (genericPoint W) hU
      = CommRingCat.ofHom (Polynomial.eval₂RingHom (kFunctionField f).hom
          (W.presheaf.germ U (genericPoint W) hU σ)) := by
  refine CommRingCat.hom_ext (Polynomial.ringHom_ext ?_ ?_)
  · intro a
    have hres := congrArg (fun g : CommRingCat.of k ⟶ Γ(W, U) => g.hom a)
      (kSection_res f (le_top : U ≤ ⊤))
    simp only [ConcreteCategory.comp_apply] at hres
    simp only [toChartHom, kFunctionField, ConcreteCategory.comp_apply, CommRingCat.hom_ofHom,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, ← hres]
    exact W.presheaf.germ_res_apply (homOfLE (le_top : U ≤ ⊤)) _ hU _
  · simp [toChartHom]

/-- **If `r` is transcendental over `k`** — i.e. the `k`-algebra map `k[t] → K(W)`, `t ↦ r`, is
injective — then so is the ring map `k[t] → Γ(W, U)` attached to a section representing `r`. -/
lemma injective_toChartHom [IsIntegral W] (U : W.Opens) (hU : genericPoint W ∈ U) (σ : Γ(W, U))
    (htr : Function.Injective (Polynomial.eval₂RingHom (kFunctionField f).hom
      (W.presheaf.germ U (genericPoint W) hU σ))) :
    Function.Injective (toChartHom f U σ).hom := by
  intro a b hab
  refine htr ?_
  have ha := congrArg (fun g : CommRingCat.of (Polynomial k) ⟶ W.functionField => g.hom a)
    (toChartHom_comp_germ f U hU σ)
  have hb := congrArg (fun g : CommRingCat.of (Polynomial k) ⟶ W.functionField => g.hom b)
    (toChartHom_comp_germ f U hU σ)
  simp only [ConcreteCategory.comp_apply, CommRingCat.hom_ofHom] at ha hb
  rw [← ha, ← hb, hab]

end Dominance

section Glue

variable [IsIntegral W] {r : W.functionField}

/-- **Gluing data for the morphism to `ℙ¹_k` defined by a rational function `r`**: two open sets
covering `W`, each containing the generic point, carrying regular functions representing `r` and
`r⁻¹` respectively. -/
structure ChartPair (W : Scheme.{u}) [IsIntegral W] (r : W.functionField) where
  /-- The open set on which `r` is regular. -/
  U₀ : W.Opens
  /-- The open set on which `r⁻¹` is regular. -/
  U₁ : W.Opens
  /-- The generic point lies in `U₀`. -/
  mem₀ : genericPoint W ∈ U₀
  /-- The generic point lies in `U₁`. -/
  mem₁ : genericPoint W ∈ U₁
  /-- The regular function representing `r` on `U₀`. -/
  σ₀ : Γ(W, U₀)
  /-- The regular function representing `r⁻¹` on `U₁`. -/
  σ₁ : Γ(W, U₁)
  /-- `σ₀` represents `r`. -/
  germ₀ : W.presheaf.germ U₀ (genericPoint W) mem₀ σ₀ = r
  /-- `σ₁` represents `r⁻¹`. -/
  germ₁ : W.presheaf.germ U₁ (genericPoint W) mem₁ σ₁ = r⁻¹
  /-- The two open sets cover `W`. -/
  covers : U₀ ⊔ U₁ = ⊤

variable (d : ChartPair W r)

/-- The restrictions of the two sections of a `ChartPair` to any open subset containing the
generic point are mutually inverse. -/
lemma ChartPair.res_mul_res (hr : r ≠ 0) {Z : W.Opens} (h₀ : Z ≤ d.U₀) (h₁ : Z ≤ d.U₁)
    (hZ : genericPoint W ∈ Z) :
    W.presheaf.map (homOfLE h₀).op d.σ₀ * W.presheaf.map (homOfLE h₁).op d.σ₁ = 1 := by
  refine germ_injective_of_isIntegral W (genericPoint W) hZ ?_
  rw [map_mul, map_one, W.presheaf.germ_res_apply (homOfLE h₀) _ hZ,
    W.presheaf.germ_res_apply (homOfLE h₁) _ hZ, d.germ₀, d.germ₁, mul_inv_cancel₀ hr]

/-- The morphism `U₀ ⟶ ℙ¹_k` defined by `r` through the first standard chart. -/
noncomputable def ChartPair.hom₀ : d.U₀.toScheme ⟶ scheme k :=
  toChart f d.U₀ d.σ₀ ≫ chartZero k

/-- The morphism `U₁ ⟶ ℙ¹_k` defined by `r⁻¹` through the second standard chart. -/
noncomputable def ChartPair.hom₁ : d.U₁.toScheme ⟶ scheme k :=
  toChart f d.U₁ d.σ₁ ≫ chartOne k

/-- The two morphisms of a `ChartPair` agree on the intersection of the two open sets. -/
lemma ChartPair.homOfLE_hom₀ (hr : r ≠ 0) :
    W.homOfLE (inf_le_left : d.U₀ ⊓ d.U₁ ≤ d.U₀) ≫ d.hom₀ f
      = W.homOfLE (inf_le_right : d.U₀ ⊓ d.U₁ ≤ d.U₁) ≫ d.hom₁ f := by
  simp only [ChartPair.hom₀, ChartPair.hom₁, ← Category.assoc, homOfLE_comp_toChart]
  exact toChart_chartZero_eq_toChart_chartOne f _ _ _
    (d.res_mul_res hr inf_le_left inf_le_right ⟨d.mem₀, d.mem₁⟩)

/-- The mirrored form of `ChartPair.homOfLE_hom₀`, with the two open sets interchanged. -/
lemma ChartPair.homOfLE_hom₁ (hr : r ≠ 0) :
    W.homOfLE (inf_le_left : d.U₁ ⊓ d.U₀ ≤ d.U₁) ≫ d.hom₁ f
      = W.homOfLE (inf_le_right : d.U₁ ⊓ d.U₀ ≤ d.U₀) ≫ d.hom₀ f := by
  simp only [ChartPair.hom₀, ChartPair.hom₁, ← Category.assoc, homOfLE_comp_toChart]
  exact (toChart_chartZero_eq_toChart_chartOne f _ _ _
    (d.res_mul_res hr inf_le_right inf_le_left ⟨d.mem₁, d.mem₀⟩)).symm

/-- The two open sets of a `ChartPair`, as a `Bool`-indexed family. -/
def ChartPair.opens : Bool → W.Opens := fun b => bif b then d.U₀ else d.U₁

/-- The two open sets of a `ChartPair` form an open cover. -/
lemma ChartPair.isOpenCover : IsOpenCover d.opens := by
  rw [IsOpenCover, iSup_bool_eq]
  exact d.covers

/-- The open cover of `W` by the two open sets of a `ChartPair`. -/
noncomputable def ChartPair.cover : W.OpenCover :=
  W.openCoverOfIsOpenCover d.opens d.isOpenCover

/-- The two morphisms of a `ChartPair`, as a family indexed by the cover. -/
noncomputable def ChartPair.homFam : ∀ b : Bool, (d.cover).X b ⟶ scheme k
  | true => d.hom₀ f
  | false => d.hom₁ f

/-- **The morphism `W ⟶ ℙ¹_k` defined by a rational function**, glued from the two chart
morphisms of a `ChartPair`. -/
noncomputable def ChartPair.toProjectiveLine (hr : r ≠ 0) : W ⟶ scheme k :=
  d.cover.glueMorphisms (d.homFam f) (by
    intro b c
    cases b <;> cases c
    · exact pullback_self_hom_ext d.U₁.ι (d.homFam f false)
    · exact pullback_hom_ext d.U₁ d.U₀ (d.hom₁ f) (d.hom₀ f) (d.homOfLE_hom₁ f hr)
    · exact pullback_hom_ext d.U₀ d.U₁ (d.hom₀ f) (d.hom₁ f) (d.homOfLE_hom₀ f hr)
    · exact pullback_self_hom_ext d.U₀.ι (d.homFam f true))

/-- On `U₀` the glued morphism is the first chart morphism. -/
@[simp] lemma ChartPair.ι_toProjectiveLine₀ (hr : r ≠ 0) :
    d.U₀.ι ≫ d.toProjectiveLine f hr = d.hom₀ f :=
  d.cover.ι_glueMorphisms (d.homFam f) _ true

/-- On `U₁` the glued morphism is the second chart morphism. -/
@[simp] lemma ChartPair.ι_toProjectiveLine₁ (hr : r ≠ 0) :
    d.U₁.ι ≫ d.toProjectiveLine f hr = d.hom₁ f :=
  d.cover.ι_glueMorphisms (d.homFam f) _ false

/-- **The morphism to `ℙ¹_k` defined by a rational function is a morphism of `k`-schemes.** -/
theorem ChartPair.toProjectiveLine_comp_structureMap (hr : r ≠ 0) :
    d.toProjectiveLine f hr ≫ structureMap k = f := by
  refine d.cover.hom_ext _ _ fun b => ?_
  cases b
  · change d.U₁.ι ≫ d.toProjectiveLine f hr ≫ structureMap k = d.U₁.ι ≫ f
    rw [← Category.assoc, d.ι_toProjectiveLine₁ f hr, ChartPair.hom₁, Category.assoc,
      chartOne_comp_structureMap, toChart_comp_chartToSpecK]
  · change d.U₀.ι ≫ d.toProjectiveLine f hr ≫ structureMap k = d.U₀.ι ≫ f
    rw [← Category.assoc, d.ι_toProjectiveLine₀ f hr, ChartPair.hom₀, Category.assoc,
      chartZero_comp_structureMap, toChart_comp_chartToSpecK]

/-- **The glued morphism sends the generic point of `W` to the generic point of `ℙ¹_k`** as soon as
`r` is transcendental over `k`, i.e. the `k`-algebra map `k[t] → K(W)`, `t ↦ r`, is injective.
In particular the morphism is then dominant. -/
theorem ChartPair.base_genericPoint (hr : r ≠ 0)
    (htr : Function.Injective (Polynomial.eval₂RingHom (kFunctionField f).hom r)) :
    (d.toProjectiveLine f hr).base (genericPoint W) = genericPt k := by
  have hne : Nonempty d.U₀ := ⟨⟨genericPoint W, d.mem₀⟩⟩
  have hinj : Function.Injective (toChartHom f d.U₀ d.σ₀).hom := by
    refine injective_toChartHom f d.U₀ d.mem₀ d.σ₀ ?_
    rw [d.germ₀]
    exact htr
  have h1 : d.U₀.ι.base (genericPoint d.U₀.toScheme) = genericPoint W :=
    genericPoint_eq_of_isOpenImmersion d.U₀.ι
  have h2 : (toChart f d.U₀ d.σ₀).base (genericPoint d.U₀.toScheme) = genericPoint (chart k) :=
    toChart_base_genericPoint f d.U₀ d.σ₀ hinj
  rw [← h1, ← Scheme.Hom.comp_apply, d.ι_toProjectiveLine₀ f hr, ChartPair.hom₀,
    Scheme.Hom.comp_apply, h2]
  rfl

end Glue

section Coordinate

/-- The coordinate `t` of the first standard chart `𝔸¹_k = Spec k[t]`, as a global section. -/
noncomputable def coord : Γ(chart k, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv Polynomial.X

/-- The ring map underlying `toChart` is the composition of `toChartHom` with the identification
`Γ(W, U) ≅ Γ(U, ⊤)`. -/
lemma ΓSpecIso_inv_comp_toChart_appTop (U : W.Opens) (σ : Γ(W, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv ≫ (toChart f U σ).appTop
      = toChartHom f U σ ≫ U.topIso.inv := by
  rw [toChart, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop,
    Scheme.ΓSpecIso_naturality_assoc, Iso.inv_hom_id_assoc]

/-- **The morphism to the first standard chart pulls the coordinate `t` back to `σ`.** -/
theorem toChart_appTop_coord (U : W.Opens) (σ : Γ(W, U)) :
    (toChart f U σ).appTop (coord : Γ(chart k, ⊤)) = U.topIso.inv σ := by
  have h := congrArg (fun g : CommRingCat.of (Polynomial k) ⟶ Γ(U.toScheme, ⊤) =>
    g.hom Polynomial.X) (ΓSpecIso_inv_comp_toChart_appTop f U σ)
  simpa only [coord, toChartHom, ConcreteCategory.comp_apply, CommRingCat.hom_ofHom,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using h

end Coordinate

section Canonical

variable [IsIntegral W] (hv : ∀ x : W, ValuationRing (W.presheaf.stalk x)) (r : W.functionField)

/-- **The canonical gluing datum of a rational function** on an integral scheme all of whose local
rings are valuation rings (e.g. a regular integral curve): the domains of definition of `r` and of
`r⁻¹` cover `W`. -/
noncomputable def chartPairOfValuationRing : ChartPair W r where
  U₀ := Scheme.regularLocus r
  U₁ := Scheme.regularLocus r⁻¹
  mem₀ := Scheme.genericPoint_mem_regularLocus r
  mem₁ := Scheme.genericPoint_mem_regularLocus r⁻¹
  σ₀ := Scheme.regularSection r
  σ₁ := Scheme.regularSection r⁻¹
  germ₀ := Scheme.germ_regularSection r
  germ₁ := Scheme.germ_regularSection r⁻¹
  covers := Scheme.regularLocus_sup_regularLocus_inv_eq_top hv r

/-- **The morphism to `ℙ¹_k` defined by a nonzero rational function** on an integral `k`-scheme all
of whose local rings are valuation rings. -/
noncomputable def toProjectiveLine (hr : r ≠ 0) : W ⟶ scheme k :=
  (chartPairOfValuationRing hv r).toProjectiveLine f hr

/-- The morphism to `ℙ¹_k` defined by a rational function is a morphism of `k`-schemes. -/
theorem toProjectiveLine_comp_structureMap (hr : r ≠ 0) :
    toProjectiveLine f hv r hr ≫ structureMap k = f :=
  (chartPairOfValuationRing hv r).toProjectiveLine_comp_structureMap f hr

/-- On the domain of definition of `r`, the morphism to `ℙ¹_k` is the morphism to the first
standard chart defined by the regular function `r`. -/
theorem ι_toProjectiveLine (hr : r ≠ 0) :
    (Scheme.regularLocus r).ι ≫ toProjectiveLine f hv r hr
      = toChart f (Scheme.regularLocus r) (Scheme.regularSection r) ≫ chartZero k :=
  (chartPairOfValuationRing hv r).ι_toProjectiveLine₀ f hr

/-- **The morphism to `ℙ¹_k` defined by a rational function is proper** when `W` is proper over
`k`.  (`IsSeparated (structureMap k)`, i.e. separatedness of `ℙ¹_k` over `k`, is currently an
explicit hypothesis: it is not yet available for the glued model of `ℙ¹_k`.) -/
theorem isProper_toProjectiveLine [IsProper f] [IsSeparated (structureMap k)] (hr : r ≠ 0) :
    IsProper (toProjectiveLine f hv r hr) := by
  have h : IsProper (toProjectiveLine f hv r hr ≫ structureMap k) := by
    rw [toProjectiveLine_comp_structureMap]
    infer_instance
  exact IsProper.of_comp _ (structureMap k)

/-- **The morphism to `ℙ¹_k` defined by a rational function is locally of finite type** when `W`
is locally of finite type over `k`. -/
theorem locallyOfFiniteType_toProjectiveLine [LocallyOfFiniteType f] (hr : r ≠ 0) :
    LocallyOfFiniteType (toProjectiveLine f hv r hr) := by
  have h : LocallyOfFiniteType (toProjectiveLine f hv r hr ≫ structureMap k) := by
    rw [toProjectiveLine_comp_structureMap]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (structureMap k)

/-- **The morphism to `ℙ¹_k` defined by a rational function is finite as soon as its fibres are
finite**, by Zariski's main theorem (`IsFinite.of_isProper_of_locallyQuasiFinite`): it is proper
because `W` is proper over `k`, and locally quasi-finite because it is locally of finite type with
finite fibres.  Finiteness of the fibres is the remaining geometric input (for a nonconstant `r` on
an irreducible one-dimensional `W` the fibre over a closed point of a chart is the zero locus of
`r - c`, a proper closed subset of `W`, hence finite); `IsSeparated (structureMap k)` is likewise
an explicit hypothesis since separatedness of the glued `ℙ¹_k` is not yet available. -/
theorem isFinite_toProjectiveLine_of_finite_fibres [IsProper f]
    [IsSeparated (structureMap k)] (hr : r ≠ 0)
    (hfib : ∀ y : scheme k, ((toProjectiveLine f hv r hr) ⁻¹' {y}).Finite) :
    IsFinite (toProjectiveLine f hv r hr) := by
  have _ := isProper_toProjectiveLine f hv r hr
  have _ := locallyOfFiniteType_toProjectiveLine f hv r hr
  have _ : LocallyQuasiFinite (toProjectiveLine f hv r hr) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ hfib
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- Under a closed morphism of schemes, no closed point maps to a non-closed point. -/
lemma base_ne_of_isClosed {X Y : Scheme.{u}} (g : X ⟶ Y) [UniversallyClosed g] {y : Y}
    (hy : ¬ IsClosed ({y} : Set Y)) {x : X} (hx : IsClosed ({x} : Set X)) : g.base x ≠ y := by
  intro h
  refine hy ?_
  have himg := g.isClosedMap {x} hx
  rwa [Set.image_singleton, h] at himg

/-- The generic point of `ℙ¹_k` is not a closed point. -/
lemma not_isClosed_genericPt : ¬ IsClosed ({genericPt k} : Set (scheme k)) := by
  intro h
  have h1 : closure ({genericPt k} : Set (scheme k)) = {genericPt k} := h.closure_eq
  rw [closure_genericPt] at h1
  have h2 : genericPt k ∈ Set.range (chartZero k).base := ⟨genericPoint (chart k), rfl⟩
  rw [range_chartZero_eq_compl_infty] at h2
  have h3 : infty k ∈ ({genericPt k} : Set (scheme k)) := by rw [← h1]; trivial
  exact h2 (Set.mem_singleton_iff.mpr (Set.mem_singleton_iff.mp h3).symm)

/-- **The fibres of the morphism to `ℙ¹_k` defined by a rational function are finite**, provided
`W` is one dimensional (`hone`: every proper closed subset of `W` is finite, `hpt`: every point
other than the generic point is closed) and the morphism is dominant (`hdom`, the precise form of
the requirement that `r` be nonconstant). -/
theorem finite_preimage_singleton [IsProper f] [IsSeparated (structureMap k)] (hr : r ≠ 0)
    (hone : ∀ Z : Set W, IsClosed Z → Z ≠ Set.univ → Z.Finite)
    (hpt : ∀ x : W, x ≠ genericPoint W → IsClosed ({x} : Set W))
    (hdom : (toProjectiveLine f hv r hr).base (genericPoint W) = genericPt k)
    (y : scheme k) : ((toProjectiveLine f hv r hr) ⁻¹' {y}).Finite := by
  have _ := isProper_toProjectiveLine f hv r hr
  by_cases hy : IsClosed ({y} : Set (scheme k))
  · refine hone _ (hy.preimage (toProjectiveLine f hv r hr).continuous) ?_
    intro hfull
    have hgen : (toProjectiveLine f hv r hr).base (genericPoint W) = y := by
      have : genericPoint W ∈ (toProjectiveLine f hv r hr) ⁻¹' {y} := hfull ▸ Set.mem_univ _
      simpa using this
    rw [hdom] at hgen
    exact not_isClosed_genericPt (hgen ▸ hy)
  · refine Set.Subsingleton.finite fun a ha b hb => ?_
    have key : ∀ c ∈ (toProjectiveLine f hv r hr) ⁻¹' {y}, c = genericPoint W := by
      intro c hc
      by_contra hne
      exact base_ne_of_isClosed _ hy (hpt c hne) (by simpa using hc)
    rw [key a ha, key b hb]

/-- **The morphism to `ℙ¹_k` defined by a rational function which is transcendental over `k` on a
proper integral curve over `k` is finite.**  The one-dimensionality of `W` enters through `hone`
(every proper closed subset of `W` is finite) and `hpt` (every point other than the generic point
is closed), and `IsSeparated (structureMap k)` — separatedness of `ℙ¹_k` over `k` — is an explicit
hypothesis, not yet available for the glued model of `ℙ¹_k`. -/
theorem isFinite_toProjectiveLine [IsProper f] [IsSeparated (structureMap k)] (hr : r ≠ 0)
    (hone : ∀ Z : Set W, IsClosed Z → Z ≠ Set.univ → Z.Finite)
    (hpt : ∀ x : W, x ≠ genericPoint W → IsClosed ({x} : Set W))
    (htr : Function.Injective (Polynomial.eval₂RingHom (kFunctionField f).hom r)) :
    IsFinite (toProjectiveLine f hv r hr) :=
  isFinite_toProjectiveLine_of_finite_fibres f hv r hr
    (finite_preimage_singleton f hv r hr hone hpt
      ((chartPairOfValuationRing hv r).base_genericPoint f hr htr))

end Canonical

end RationalFunction

end GromovWitten.AlgebraicGeometry
