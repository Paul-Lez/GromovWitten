/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeHyperplaneObstruction

/-!
# Reindexing the hyperplane conormal complex onto the smaller polynomial ring (issue #75)

`RelativeVirtualClassBaseChange.lean` constructs, and `RelativeHyperplaneObstruction.lean` proves
to be an obstruction theory, the base change `hyperplaneHom φ` of a relative obstruction datum
`φ : E ⟶ relConormalComplex I` of `X = Spec (R ⧸ I) → Y = 𝔸^{Option τ'}`,
`R = k[x_σ, y_{Option τ'}]`, along the coordinate hyperplane `Y' = 𝔸^{τ'} ↪ Y`, `y₀ = 0`.  Its
target `hyperplaneConormalComplex I` is built from the ideal `I' = I + (y₀)` of the *unchanged*
ambient ring `R` together with the quotient `hyperplaneCotangent I = (I'/I'²) ⧸ ⟨[y₀]⟩`, so none of
the machinery of `RelativeAbsolute.lean` (`absHom`, `Gr`, `relProductMap`, `ResolvedCone.ideal`,
`relativeVirtualClass`) — all of which is stated for a target `relConormalComplex J` of an honest
ideal `J` of the ambient polynomial ring — applies to it.

This file removes that obstacle.  Write `R' = k[x_σ, y_{τ'}]` for the coordinate ring of
`𝔸^σ × Y'` and `ρ : R →ₐ[k] R'` for the reindexing map `x_i ↦ x_i`, `y_{some j} ↦ y_j`,
`y₀ ↦ 0`, and put `J = reindexIdeal I = ρ(I)`.

## Main results

* `reindexAlgHom` (`= ρ`), `reindexSection` (a section `ι` of `ρ`), `surjective_reindexAlgHom`,
  `comap_bot_reindexAlgHom` / `ker_reindexAlgHom`: `ker ρ = (y₀)`, proved from the elementwise
  statement `sub_reindexSection_reindexAlgHom_mem` (`f ≡ ι (ρ f) mod y₀`).
* `map_hyperplaneIdeal` (`ρ(I') = J`), `comap_reindexIdeal` (`ρ⁻¹(J) = I'`) and
  **`quotientReindexEquiv : Base (hyperplaneIdeal I) ≃ₐ[k] Base (reindexIdeal I)`**, i.e.
  `R ⧸ (I + (y₀)) ≃ R' ⧸ J`: the two descriptions of the coordinate ring of `X' = X ×_Y Y'`
  (`quotientReindexAlgEquiv` upgrades it to an isomorphism of `Base I`-algebras).
* **`hyperplaneCotangentReindexEquiv : hyperplaneCotangent I ≃+ J.Cotangent`**, semilinear along
  `quotientReindexEquiv`: the comparison map is `Ideal.mapCotangent` along `ρ`, descended through
  `Submodule.liftQSpanSingleton` because `ρ y₀ = 0`; it is surjective because `J = ρ(I')` and
  injective because `J² = ρ(I'²)` and `ker ρ = (y₀) ⊆ I'`
  (`mk_eq_zero_of_reindexCotangentMap_eq_zero`).
* `sigmaReindexEquiv : (σ → Base I') ≃+ (σ → Base J)` for the degree-one terms, and
  `sigmaReindexEquiv_hyperplaneDifferential`: the two relative conormal differentials correspond,
  because `ρ` commutes with the `σ`-partial derivatives (`reindexAlgHom_pderiv`).
* **`hyperplaneReindexIso`**: the three previous items packaged as a `SemilinearIso` (a new
  structure in this file: additive bijections in both degrees, semilinear along a ring isomorphism
  of the two base rings, commuting with the differentials).  A `LinearTwoTermComplex.Hom` or
  `HomotopyEquivalence` cannot be used, since the two complexes live over the two different
  (canonically isomorphic) rings `Base (hyperplaneIdeal I)` and `Base (reindexIdeal I)`.
* `isObstructionTheory_iff_elementwise`, `isObstructionTheory_of_addEquiv`,
  `isObstructionTheory_of_semilinearIso`: the obstruction-theory property is a purely additive
  condition on the four modules of a chain map, hence transports across such an isomorphism.
* **`reindexHom φ : E ⊗ Base J ⟶ relConormalComplex J`**, the transport of `hyperplaneHom φ`, and
  **`isObstructionTheory_reindexed_hyperplaneHom`**: it is a relative obstruction theory for
  `X' → Y'` whenever `φ` is one for `X → Y`, with no regularity hypothesis on `y₀`.
* `isObstructionTheory_reindexHom_iff` and, under the regularity hypothesis on `y₀`,
  `isObstructionTheory_reindexHom_iff_baseChange`: the reindexed datum is an obstruction theory
  exactly when `hyperplaneHom φ` is, resp. exactly when the plain degreewise base change of `φ` is.
* `virtualDimension_absHom_reindexHom`: the virtual dimension drops by exactly one,
  `vdim [X'/Y'] + 1 = vdim [X/Y]`.
* `relativeVirtualClass_hyperplane`, the resulting definition of `[X'/Y']^vir` as
  `RelativeAbsolute.relativeVirtualClass (reindexHom I φ)`, and
  `virtualClassAt_absHom_reindexHom` identifying it with the virtual class of the associated
  absolute obstruction theory.

## The comparison of normal cones

A first step towards the resolved-cone ideal identity is also proved: `ρ` induces a map of Rees
algebras (`reesReindexHom`) and hence a ring homomorphism `grReindexHom : gr_I(R) → gr_J(R')` of
associated graded rings, which is compatible with the structural maps of the coordinate rings
(`grReindexHom_algebraMap`) and with the degree-one conormal inclusions
(`grReindexHom_conormalToAssociatedGraded`), and which is **surjective**
(`surjective_grReindexHom`, `surjective_reesReindexHom`).  Geometrically: the normal cone of `X'`
in `𝔸^σ × Y'` is a closed subcone of the normal cone of `X` in `𝔸^σ × Y`, and of its base change
along `X' ↪ X`.

## What remains open

The **identity of resolved-cone ideals**, `RelativeAbsolute.ideal' (reindexHom I φ) =
(RelativeAbsolute.ideal' φ).map (…)`, and hence the **Gysin comparison**
`relativeVirtualClass_hyperplane = i^! [X/Y]^vir` for the regular embedding `i : Y' ↪ Y`, are not
proved here.  Both sides are now at least *statable* (which was the point of this file; for
instance `RelativeAbsolute.ideal' (reindexHom I φ)` is an ideal of
`SymmetricAlgebra (Base J) (Base J ⊗[Base I] E⁰)`), but the identity needs the converse of
`surjective_grReindexHom`, namely that `gr_I(R) ⊗_{Base I} Base J → gr_J(R')` is *injective*.  That
is a Tor-independence statement in every degree — `Iⁿ ∩ (y₀) = y₀ · Iⁿ` for all `n`, not just
`n = 1` as in `RelativeHyperplaneObstruction.hyperplaneCotangentEquiv` — and is not a repackaging
of anything available in this repository.

As in `RelativeAbsolute.lean`, `RelativeVirtualClassBaseChange.lean` and
`RelativeHyperplaneObstruction.lean` everything here is the affine model
`X = Spec (R ⧸ I) ⊆ 𝔸^σ × Y`, not the Deligne–Mumford-stack statement of Behrend–Fantechi §7.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeHyperplaneReindex

open LinearTwoTermComplex PicardCriteria

/-! ## Transporting the obstruction-theory property along a change of base ring -/

/-- **A semilinear isomorphism of two-term complexes** over a ring isomorphism `e : R ≃+* S`:
additive bijections in both degrees, semilinear along `e`, commuting with the differentials.  This
is the shape of the comparison between the hyperplane conormal complex over
`Base (hyperplaneIdeal I)` and the relative conormal complex over the *smaller* polynomial ring
modulo the reindexed ideal; a genuine `LinearTwoTermComplex.Hom` cannot be used because the two
complexes live over different (although canonically isomorphic) base rings. -/
structure SemilinearIso {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (E : LinearTwoTermComplex R) (F : LinearTwoTermComplex S) where
  /-- The degree-zero component, an additive bijection. -/
  degreeZero : E.degreeZero ≃+ F.degreeZero
  /-- The degree-one component, an additive bijection. -/
  degreeOne : E.degreeOne ≃+ F.degreeOne
  /-- Semilinearity of the degree-zero component along `e`. -/
  map_smul_degreeZero (r : R) (x : E.degreeZero) : degreeZero (r • x) = e r • degreeZero x
  /-- Semilinearity of the degree-one component along `e`. -/
  map_smul_degreeOne (r : R) (x : E.degreeOne) : degreeOne (r • x) = e r • degreeOne x
  /-- Compatibility with the two differentials. -/
  comm (x : E.degreeZero) : degreeOne (E.differential x) = F.differential (degreeZero x)

section Transfer

variable {R : Type u} [CommRing R] {E F : LinearTwoTermComplex R}

/-- **Elementwise characterisation of the obstruction-theory property.**  A chain map `φ` of
two-term complexes is an obstruction theory iff (i) every cycle of the target lifts to a cycle of
the source, (ii) a degree-one class of the source that becomes a boundary in the target was
already a boundary, and (iii) every degree-one element of the target is the image of a degree-one
element of the source, up to a boundary.  The point of this reformulation is that it mentions only
the *additive* structure of the four modules involved, so it can be transported along additive
bijections between complexes over *different* base rings. -/
theorem isObstructionTheory_iff_elementwise (φ : Hom E F) :
    IsObstructionTheory φ ↔
      ((∀ a : F.degreeZero, F.differential a = 0 →
            ∃ x : E.degreeZero, E.differential x = 0 ∧ φ.degreeZero x = a) ∧
        (∀ x : E.degreeOne, (∃ a : F.degreeZero, F.differential a = φ.degreeOne x) →
            ∃ b : E.degreeZero, E.differential b = x) ∧
        (∀ y : F.degreeOne, ∃ (x : E.degreeOne) (a : F.degreeZero),
            y - φ.degreeOne x = F.differential a)) := by
  constructor
  · intro h
    refine ⟨fun a ha => ?_, fun x hx => ?_, fun y => ?_⟩
    · obtain ⟨z, hz⟩ := h.surjective_kernelMap ⟨a, LinearMap.mem_ker.2 ha⟩
      exact ⟨z.1, LinearMap.mem_ker.1 z.2, congrArg Subtype.val hz⟩
    · obtain ⟨a, ha⟩ := hx
      have hzero : φ.cokernelMap (Submodule.Quotient.mk x) = 0 := by
        rw [Hom.cokernelMap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
        exact ⟨a, ha⟩
      have hmem : (Submodule.Quotient.mk x : E.degreeOne ⧸
          (LinearMap.range E.differential : Submodule R E.degreeOne)) = 0 :=
        h.bijective_cokernelMap.1 (hzero.trans (map_zero _).symm)
      exact Submodule.Quotient.mk_eq_zero _ |>.1 hmem
    · obtain ⟨w, hw⟩ := h.bijective_cokernelMap.2 (Submodule.Quotient.mk y)
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
      rw [Hom.cokernelMap, Submodule.mapQ_apply] at hw
      obtain ⟨a, ha⟩ := (Submodule.Quotient.eq _).1 hw
      exact ⟨x, -a, by rw [map_neg, ha]; abel⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨LinearMap.ker_eq_bot.1 (Submodule.eq_bot_iff _ |>.2 fun z hz => ?_), fun z => ?_⟩,
      fun a => ?_⟩
    · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      rw [LinearMap.mem_ker, Hom.cokernelMap, Submodule.mapQ_apply,
        Submodule.Quotient.mk_eq_zero] at hz
      obtain ⟨b, hb⟩ := h2 x hz
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨b, hb⟩
    · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      obtain ⟨x, c, hc⟩ := h3 y
      refine ⟨Submodule.Quotient.mk x, ?_⟩
      rw [Hom.cokernelMap, Submodule.mapQ_apply]
      refine (Submodule.Quotient.eq _).2 ?_
      exact ⟨-c, by rw [map_neg, ← hc]; abel⟩
    · obtain ⟨x, hx, hxa⟩ := h1 a.1 (LinearMap.mem_ker.1 a.2)
      exact ⟨⟨x, LinearMap.mem_ker.2 hx⟩, Subtype.ext hxa⟩

variable {S : Type u} [CommRing S] {E' F' : LinearTwoTermComplex S}

/-- **The obstruction-theory property transports along additive isomorphisms of two-term
complexes.**  Given a chain map `φ : E ⟶ F` over `R`, a chain map `ψ : E' ⟶ F'` over `S`, and
additive bijections in all four degrees which commute with the two differentials and with `φ`,
`ψ`, the map `ψ` is an obstruction theory as soon as `φ` is.  No compatibility of the base rings
is required: by `isObstructionTheory_iff_elementwise` the property only involves the additive
structure. -/
theorem isObstructionTheory_of_addEquiv {φ : Hom E F} {ψ : Hom E' F'}
    (a₀ : E.degreeZero ≃+ E'.degreeZero) (a₁ : E.degreeOne ≃+ E'.degreeOne)
    (b₀ : F.degreeZero ≃+ F'.degreeZero) (b₁ : F.degreeOne ≃+ F'.degreeOne)
    (ha : ∀ x, a₁ (E.differential x) = E'.differential (a₀ x))
    (hb : ∀ x, b₁ (F.differential x) = F'.differential (b₀ x))
    (h0 : ∀ x, b₀ (φ.degreeZero x) = ψ.degreeZero (a₀ x))
    (h1 : ∀ x, b₁ (φ.degreeOne x) = ψ.degreeOne (a₁ x))
    (h : IsObstructionTheory φ) : IsObstructionTheory ψ := by
  obtain ⟨H1, H2, H3⟩ := (isObstructionTheory_iff_elementwise φ).1 h
  refine (isObstructionTheory_iff_elementwise ψ).2
    ⟨fun a' ha' => ?_, fun x' hx' => ?_, fun y' => ?_⟩
  · have hz : F.differential (b₀.symm a') = 0 := by
      apply b₁.injective
      rw [hb, b₀.apply_symm_apply, ha', map_zero]
    obtain ⟨x, hx, hxa⟩ := H1 _ hz
    refine ⟨a₀ x, ?_, ?_⟩
    · rw [← ha, hx, map_zero]
    · rw [← h0, hxa, b₀.apply_symm_apply]
  · obtain ⟨a', ha'⟩ := hx'
    have hd : F.differential (b₀.symm a') = φ.degreeOne (a₁.symm x') := by
      apply b₁.injective
      rw [hb, b₀.apply_symm_apply, h1, a₁.apply_symm_apply, ha']
    obtain ⟨b, hb2⟩ := H2 _ ⟨_, hd⟩
    exact ⟨a₀ b, by rw [← ha, hb2, a₁.apply_symm_apply]⟩
  · obtain ⟨x, c, hc⟩ := H3 (b₁.symm y')
    refine ⟨a₁ x, b₀ c, ?_⟩
    rw [← h1, ← hb, ← hc, map_sub, b₁.apply_symm_apply]

/-- **Two chain maps related by additive isomorphisms of two-term complexes are obstruction
theories simultaneously**: `isObstructionTheory_of_addEquiv` applied in both directions. -/
theorem isObstructionTheory_addEquiv_iff {φ : Hom E F} {ψ : Hom E' F'}
    (a₀ : E.degreeZero ≃+ E'.degreeZero) (a₁ : E.degreeOne ≃+ E'.degreeOne)
    (b₀ : F.degreeZero ≃+ F'.degreeZero) (b₁ : F.degreeOne ≃+ F'.degreeOne)
    (ha : ∀ x, a₁ (E.differential x) = E'.differential (a₀ x))
    (hb : ∀ x, b₁ (F.differential x) = F'.differential (b₀ x))
    (h0 : ∀ x, b₀ (φ.degreeZero x) = ψ.degreeZero (a₀ x))
    (h1 : ∀ x, b₁ (φ.degreeOne x) = ψ.degreeOne (a₁ x)) :
    IsObstructionTheory φ ↔ IsObstructionTheory ψ := by
  refine ⟨isObstructionTheory_of_addEquiv a₀ a₁ b₀ b₁ ha hb h0 h1, ?_⟩
  refine isObstructionTheory_of_addEquiv a₀.symm a₁.symm b₀.symm b₁.symm
    (fun x => ?_) (fun x => ?_) (fun x => ?_) (fun x => ?_)
  · exact a₁.injective (by rw [a₁.apply_symm_apply, ha, a₀.apply_symm_apply])
  · exact b₁.injective (by rw [b₁.apply_symm_apply, hb, b₀.apply_symm_apply])
  · exact b₀.injective (by rw [b₀.apply_symm_apply, h0, a₀.apply_symm_apply])
  · exact b₁.injective (by rw [b₁.apply_symm_apply, h1, a₁.apply_symm_apply])

/-- **The obstruction-theory property transports along a semilinear isomorphism of two-term
complexes**: the packaged form of `isObstructionTheory_of_addEquiv`. -/
theorem isObstructionTheory_of_semilinearIso {e : R ≃+* S} {φ : Hom E F} {ψ : Hom E' F'}
    (α : SemilinearIso e E E') (β : SemilinearIso e F F')
    (h0 : ∀ x, β.degreeZero (φ.degreeZero x) = ψ.degreeZero (α.degreeZero x))
    (h1 : ∀ x, β.degreeOne (φ.degreeOne x) = ψ.degreeOne (α.degreeOne x))
    (h : IsObstructionTheory φ) : IsObstructionTheory ψ :=
  isObstructionTheory_of_addEquiv α.degreeZero α.degreeOne β.degreeZero β.degreeOne
    α.comm β.comm h0 h1 h

end Transfer

/-! ## The reindexing algebra map -/

section Reindex

open RelativeVirtualClassBaseChange
open GromovWitten.AlgebraicGeometry.NormalConeAction (Base)

variable {k : Type u} [CommRing k] {σ τ' : Type u}

/-- **The reindexing algebra map** `ρ : k[x_σ, y_{Option τ'}] →ₐ[k] k[x_σ, y_{τ'}]`: it renames
`x_i ↦ x_i` and `y_{some j} ↦ y_j` and kills the extra coordinate `y₀ = y_{none}`.  It is the
comorphism of the closed immersion of the coordinate hyperplane
`𝔸^σ × 𝔸^{τ'} ↪ 𝔸^σ × 𝔸^{Option τ'}`, `y₀ = 0`. -/
noncomputable def reindexAlgHom :
    MvPolynomial (σ ⊕ Option τ') k →ₐ[k] MvPolynomial (σ ⊕ τ') k :=
  MvPolynomial.aeval
    (Sum.elim (fun i => MvPolynomial.X (Sum.inl i))
      (Option.elim' 0 fun j => MvPolynomial.X (Sum.inr j)))

/-- **The canonical section of the reindexing map**: the renaming along `Sum.map id Option.some`,
which identifies `k[x_σ, y_{τ'}]` with the subalgebra of polynomials not involving `y₀`. -/
noncomputable def reindexSection :
    MvPolynomial (σ ⊕ τ') k →ₐ[k] MvPolynomial (σ ⊕ Option τ') k :=
  MvPolynomial.rename (Sum.map id Option.some)

@[simp]
theorem reindexAlgHom_X_inl (i : σ) :
    reindexAlgHom (MvPolynomial.X (Sum.inl i) : MvPolynomial (σ ⊕ Option τ') k) =
      MvPolynomial.X (Sum.inl i) := by
  simp [reindexAlgHom]

@[simp]
theorem reindexAlgHom_X_inr_some (j : τ') :
    reindexAlgHom (MvPolynomial.X (Sum.inr (some j)) : MvPolynomial (σ ⊕ Option τ') k) =
      MvPolynomial.X (Sum.inr j) := by
  simp [reindexAlgHom, Option.elim']

@[simp]
theorem reindexAlgHom_X_inr_none :
    reindexAlgHom (MvPolynomial.X (Sum.inr none) : MvPolynomial (σ ⊕ Option τ') k) = 0 := by
  simp [reindexAlgHom, Option.elim']

@[simp]
theorem reindexSection_X_inl (i : σ) :
    reindexSection (MvPolynomial.X (Sum.inl i) : MvPolynomial (σ ⊕ τ') k) =
      MvPolynomial.X (Sum.inl i) := by
  simp [reindexSection]

@[simp]
theorem reindexSection_X_inr (j : τ') :
    reindexSection (MvPolynomial.X (Sum.inr j) : MvPolynomial (σ ⊕ τ') k) =
      MvPolynomial.X (Sum.inr (some j)) := by
  simp [reindexSection]

/-- `ρ` is a retraction of its section. -/
theorem reindexAlgHom_comp_reindexSection :
    (reindexAlgHom (k := k) (σ := σ) (τ' := τ')).comp reindexSection = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  intro v
  cases v with
  | inl i => simp
  | inr j => simp

/-- `ρ (ι f) = f`. -/
theorem reindexAlgHom_reindexSection (f : MvPolynomial (σ ⊕ τ') k) :
    reindexAlgHom (reindexSection f) = f := by
  rw [← AlgHom.comp_apply, reindexAlgHom_comp_reindexSection, AlgHom.id_apply]

/-- **`ρ` is surjective**, with the explicit section `ι = reindexSection`. -/
theorem surjective_reindexAlgHom :
    Function.Surjective (reindexAlgHom (k := k) (σ := σ) (τ' := τ')) :=
  fun f => ⟨reindexSection f, reindexAlgHom_reindexSection f⟩

@[simp]
theorem reindexAlgHom_hyperplaneCoord :
    reindexAlgHom (hyperplaneCoord (k := k) (σ := σ) (τ' := τ')) = 0 :=
  reindexAlgHom_X_inr_none

/-- **Every polynomial agrees with its `y₀ = 0` specialisation modulo `y₀`.**  This is the
elementwise form of the statement that `ker ρ` is generated by `y₀`. -/
theorem sub_reindexSection_reindexAlgHom_mem (f : MvPolynomial (σ ⊕ Option τ') k) :
    f - reindexSection (reindexAlgHom f) ∈
      Ideal.span {hyperplaneCoord (k := k) (σ := σ) (τ' := τ')} := by
  have key : (Ideal.Quotient.mkₐ k
        (Ideal.span {hyperplaneCoord (k := k) (σ := σ) (τ' := τ')})).comp
        (reindexSection.comp reindexAlgHom) =
      Ideal.Quotient.mkₐ k (Ideal.span {hyperplaneCoord (k := k) (σ := σ) (τ' := τ')}) := by
    apply MvPolynomial.algHom_ext
    intro v
    cases v with
    | inl i => simp
    | inr o =>
      cases o with
      | none =>
        have hmem : hyperplaneCoord (k := k) (σ := σ) (τ' := τ') ∈
            Ideal.span {hyperplaneCoord (k := k) (σ := σ) (τ' := τ')} :=
          Ideal.mem_span_singleton_self _
        simp only [AlgHom.comp_apply, reindexAlgHom_X_inr_none, map_zero,
          Ideal.Quotient.mkₐ_eq_mk]
        exact (Ideal.Quotient.eq_zero_iff_mem.2 hmem).symm
      | some j => simp
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact (AlgHom.congr_fun key f).symm

/-- **The kernel of `ρ` is the ideal generated by `y₀`.** -/
theorem comap_bot_reindexAlgHom :
    Ideal.comap (reindexAlgHom (k := k) (σ := σ) (τ' := τ')) ⊥ =
      Ideal.span {hyperplaneCoord (k := k) (σ := σ) (τ' := τ')} := by
  apply le_antisymm
  · intro f hf
    have hf' : reindexAlgHom f = 0 := by
      simpa using hf
    have h := sub_reindexSection_reindexAlgHom_mem f
    rwa [hf', map_zero, sub_zero] at h
  · rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simp

/-- **The kernel of `ρ` is `(y₀)`**, in `RingHom.ker` form. -/
theorem ker_reindexAlgHom :
    RingHom.ker (reindexAlgHom (k := k) (σ := σ) (τ' := τ')) =
      Ideal.span {hyperplaneCoord (k := k) (σ := σ) (τ' := τ')} := by
  rw [RingHom.ker_eq_comap_bot]
  exact comap_bot_reindexAlgHom

variable (I : Ideal (MvPolynomial (σ ⊕ Option τ') k))

/-- **The reindexed ideal** `J = ρ(I) ⊆ k[x_σ, y_{τ'}]`: the ideal of `X' = X ×_Y Y'` inside the
*smaller* ambient space `𝔸^σ × Y'`, `Y' = 𝔸^{τ'}`. -/
noncomputable abbrev reindexIdeal : Ideal (MvPolynomial (σ ⊕ τ') k) :=
  I.map reindexAlgHom

/-- `ρ(I') = ρ(I) = J`: adjoining `y₀` to `I` does not change the image, since `ρ y₀ = 0`. -/
theorem map_hyperplaneIdeal :
    (hyperplaneIdeal I).map reindexAlgHom = reindexIdeal I := by
  rw [Ideal.map_sup, Ideal.map_span]
  simp

/-- **`ρ⁻¹(J) = I'`**: the preimage of the reindexed ideal is the hyperplane ideal, because
`ker ρ = (y₀) ⊆ I'`. -/
theorem comap_reindexIdeal :
    Ideal.comap reindexAlgHom (reindexIdeal I) = hyperplaneIdeal I := by
  rw [← map_hyperplaneIdeal I,
    Ideal.comap_map_of_surjective _ surjective_reindexAlgHom, comap_bot_reindexAlgHom,
    sup_assoc, sup_idem]

/-- `I' ≤ ρ⁻¹(J)`, the hypothesis needed by `Ideal.mapCotangent`. -/
theorem hyperplaneIdeal_le_comap :
    hyperplaneIdeal I ≤ Ideal.comap reindexAlgHom (reindexIdeal I) :=
  (comap_reindexIdeal I).ge

/-- The hypothesis of `Ideal.Quotient.liftₐ` for the forward reindexing map. -/
theorem forall_mem_hyperplaneIdeal_comp_eq_zero :
    ∀ a ∈ hyperplaneIdeal I,
      ((Ideal.Quotient.mkₐ k (reindexIdeal I)).comp reindexAlgHom) a = 0 := by
  intro a ha
  exact Ideal.Quotient.eq_zero_iff_mem.2 (hyperplaneIdeal_le_comap I ha)

/-- `ι (ρ a) ∈ I'` for `a ∈ I'`: the section of `ρ` does not leave the hyperplane ideal. -/
theorem reindexSection_reindexAlgHom_mem (a : MvPolynomial (σ ⊕ Option τ') k)
    (ha : a ∈ hyperplaneIdeal I) : reindexSection (reindexAlgHom a) ∈ hyperplaneIdeal I := by
  have h : a - reindexSection (reindexAlgHom a) ∈ hyperplaneIdeal I :=
    Ideal.mem_sup_right (sub_reindexSection_reindexAlgHom_mem a)
  have h2 : reindexSection (reindexAlgHom a) = a - (a - reindexSection (reindexAlgHom a)) := by
    abel
  rw [h2]
  exact sub_mem ha h

/-- The hypothesis of `Ideal.Quotient.liftₐ` for the backward reindexing map. -/
theorem forall_mem_reindexIdeal_comp_eq_zero :
    ∀ a ∈ reindexIdeal I,
      ((Ideal.Quotient.mkₐ k (hyperplaneIdeal I)).comp reindexSection) a = 0 := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ surjective_reindexAlgHom).1 ha
  exact Ideal.Quotient.eq_zero_iff_mem.2
    (reindexSection_reindexAlgHom_mem I b (le_hyperplaneIdeal I hb))

/-- The forward reindexing map `R ⧸ I' →ₐ[k] R' ⧸ J`, `[f] ↦ [ρ f]`. -/
noncomputable def reindexQuotientHom : Base (hyperplaneIdeal I) →ₐ[k] Base (reindexIdeal I) :=
  Ideal.Quotient.liftₐ (hyperplaneIdeal I)
    ((Ideal.Quotient.mkₐ k (reindexIdeal I)).comp reindexAlgHom)
    (forall_mem_hyperplaneIdeal_comp_eq_zero I)

/-- The backward reindexing map `R' ⧸ J →ₐ[k] R ⧸ I'`, `[f] ↦ [ι f]`. -/
noncomputable def reindexQuotientInv : Base (reindexIdeal I) →ₐ[k] Base (hyperplaneIdeal I) :=
  Ideal.Quotient.liftₐ (reindexIdeal I)
    ((Ideal.Quotient.mkₐ k (hyperplaneIdeal I)).comp reindexSection)
    (forall_mem_reindexIdeal_comp_eq_zero I)

@[simp]
theorem reindexQuotientHom_mk (f : MvPolynomial (σ ⊕ Option τ') k) :
    reindexQuotientHom I (Ideal.Quotient.mk (hyperplaneIdeal I) f) =
      Ideal.Quotient.mk (reindexIdeal I) (reindexAlgHom f) :=
  rfl

@[simp]
theorem reindexQuotientInv_mk (f : MvPolynomial (σ ⊕ τ') k) :
    reindexQuotientInv I (Ideal.Quotient.mk (reindexIdeal I) f) =
      Ideal.Quotient.mk (hyperplaneIdeal I) (reindexSection f) :=
  rfl

/-- The two reindexing maps compose to the identity of `R' ⧸ J`. -/
theorem reindexQuotientHom_comp_inv :
    (reindexQuotientHom I).comp (reindexQuotientInv I) =
      AlgHom.id k (Base (reindexIdeal I)) := by
  apply AlgHom.ext
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [AlgHom.comp_apply, reindexQuotientInv_mk, reindexQuotientHom_mk,
    reindexAlgHom_reindexSection, AlgHom.id_apply]

/-- The two reindexing maps compose to the identity of `R ⧸ I'`. -/
theorem reindexQuotientInv_comp_hom :
    (reindexQuotientInv I).comp (reindexQuotientHom I) =
      AlgHom.id k (Base (hyperplaneIdeal I)) := by
  apply AlgHom.ext
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [AlgHom.comp_apply, reindexQuotientHom_mk, reindexQuotientInv_mk, AlgHom.id_apply,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← neg_sub]
  exact neg_mem (Ideal.mem_sup_right (sub_reindexSection_reindexAlgHom_mem f))

/-- **The reindexing isomorphism of coordinate rings**
`R ⧸ (I + (y₀)) ≃ₐ[k] R' ⧸ J`, `R = k[x_σ, y_{Option τ'}]`, `R' = k[x_σ, y_{τ'}]`,
`J = ρ(I)`: the affine model of the identification of `X' = X ×_Y Y'` as a closed subscheme of
the *smaller* ambient space `𝔸^σ × Y'` rather than of `𝔸^σ × Y`. -/
noncomputable def quotientReindexEquiv :
    Base (hyperplaneIdeal I) ≃ₐ[k] Base (reindexIdeal I) :=
  AlgEquiv.ofAlgHom (reindexQuotientHom I) (reindexQuotientInv I)
    (reindexQuotientHom_comp_inv I) (reindexQuotientInv_comp_hom I)

@[simp]
theorem quotientReindexEquiv_mk (f : MvPolynomial (σ ⊕ Option τ') k) :
    quotientReindexEquiv I (Ideal.Quotient.mk (hyperplaneIdeal I) f) =
      Ideal.Quotient.mk (reindexIdeal I) (reindexAlgHom f) :=
  rfl

@[simp]
theorem quotientReindexEquiv_symm_mk (f : MvPolynomial (σ ⊕ τ') k) :
    (quotientReindexEquiv I).symm (Ideal.Quotient.mk (reindexIdeal I) f) =
      Ideal.Quotient.mk (hyperplaneIdeal I) (reindexSection f) :=
  rfl

/-! ### `ρ` commutes with the `σ`-partial derivatives -/

/-- `ρ` commutes with `∂/∂x_s` on the coordinate functions. -/
theorem reindexAlgHom_pderiv_X (s : σ) (v : σ ⊕ Option τ') :
    reindexAlgHom (MvPolynomial.pderiv (Sum.inl s)
        (MvPolynomial.X v : MvPolynomial (σ ⊕ Option τ') k)) =
      MvPolynomial.pderiv (Sum.inl s) (reindexAlgHom (MvPolynomial.X v)) := by
  cases v with
  | inl i =>
    rcases eq_or_ne i s with rfl | hne
    · simp
    · rw [MvPolynomial.pderiv_X_of_ne (by simpa using hne), map_zero, reindexAlgHom_X_inl,
        MvPolynomial.pderiv_X_of_ne (by simpa using hne)]
  | inr o =>
    rw [MvPolynomial.pderiv_X_of_ne (by simp), map_zero]
    cases o with
    | none => rw [reindexAlgHom_X_inr_none, map_zero]
    | some j => rw [reindexAlgHom_X_inr_some, MvPolynomial.pderiv_X_of_ne (by simp)]

/-- **`ρ` commutes with the `σ`-partial derivatives.**  Setting the extra coordinate `y₀` to zero
commutes with differentiating in the `𝔸^σ`-directions; this is what makes the relative (`σ`-only)
conormal differentials of `I'` and of `J` correspond under the reindexing. -/
theorem reindexAlgHom_pderiv (s : σ) (f : MvPolynomial (σ ⊕ Option τ') k) :
    reindexAlgHom (MvPolynomial.pderiv (Sum.inl s) f) =
      MvPolynomial.pderiv (Sum.inl s) (reindexAlgHom f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [reindexAlgHom]
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp =>
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, hp, reindexAlgHom_pderiv_X]

/-! ### The reindexed conormal module -/

/-- **The comparison map on conormal modules** `I'/I'² → J/J²` induced by `ρ`.  It is only
`k`-linear; its semilinearity over `Base (hyperplaneIdeal I) → Base (reindexIdeal I)` is
`reindexCotangentMap_smul_base`. -/
noncomputable def reindexCotangentMap :
    (hyperplaneIdeal I).Cotangent →ₗ[k] (reindexIdeal I).Cotangent :=
  Ideal.mapCotangent (hyperplaneIdeal I) (reindexIdeal I) reindexAlgHom
    (hyperplaneIdeal_le_comap I)

@[simp]
theorem reindexCotangentMap_toCotangent (x : hyperplaneIdeal I) :
    reindexCotangentMap I (Ideal.toCotangent (hyperplaneIdeal I) x) =
      Ideal.toCotangent (reindexIdeal I)
        ⟨reindexAlgHom (x : MvPolynomial (σ ⊕ Option τ') k), hyperplaneIdeal_le_comap I x.2⟩ :=
  rfl

/-- The ring homomorphism `Base (hyperplaneIdeal I) → Base (reindexIdeal I)` underlying
`quotientReindexEquiv`. -/
noncomputable def reindexBaseHom : Base (hyperplaneIdeal I) →+* Base (reindexIdeal I) :=
  (quotientReindexEquiv I).toAlgHom.toRingHom

@[simp]
theorem reindexBaseHom_mk (f : MvPolynomial (σ ⊕ Option τ') k) :
    reindexBaseHom I (Ideal.Quotient.mk (hyperplaneIdeal I) f) =
      Ideal.Quotient.mk (reindexIdeal I) (reindexAlgHom f) :=
  rfl

/-- `ρ`-semilinearity of the conormal comparison map over the ambient polynomial ring. -/
theorem reindexCotangentMap_smul (a : MvPolynomial (σ ⊕ Option τ') k)
    (x : (hyperplaneIdeal I).Cotangent) :
    reindexCotangentMap I (a • x) = reindexAlgHom a • reindexCotangentMap I x := by
  obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective (hyperplaneIdeal I) x
  rw [← map_smul (Ideal.toCotangent (hyperplaneIdeal I)) a y, reindexCotangentMap_toCotangent,
    reindexCotangentMap_toCotangent, ← map_smul (Ideal.toCotangent (reindexIdeal I))]
  exact congrArg _ (Subtype.ext (map_mul reindexAlgHom a (y : MvPolynomial (σ ⊕ Option τ') k)))

/-- **Semilinearity of the conormal comparison map** along the reindexing isomorphism of
coordinate rings. -/
theorem reindexCotangentMap_smul_base (b : Base (hyperplaneIdeal I))
    (x : (hyperplaneIdeal I).Cotangent) :
    reindexCotangentMap I (b • x) = reindexBaseHom I b • reindexCotangentMap I x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  have h1 : (Ideal.Quotient.mk (hyperplaneIdeal I) a) • x = a • x :=
    IsScalarTower.algebraMap_smul (Base (hyperplaneIdeal I)) a x
  have h2 : (Ideal.Quotient.mk (reindexIdeal I) (reindexAlgHom a)) • reindexCotangentMap I x =
      reindexAlgHom a • reindexCotangentMap I x :=
    IsScalarTower.algebraMap_smul (Base (reindexIdeal I)) (reindexAlgHom a) _
  rw [h1, reindexCotangentMap_smul, reindexBaseHom_mk, h2]

/-- The conormal comparison map as a semilinear map along `reindexBaseHom`. -/
noncomputable def reindexCotangentSemilinear :
    (hyperplaneIdeal I).Cotangent →ₛₗ[reindexBaseHom I] (reindexIdeal I).Cotangent where
  toFun := reindexCotangentMap I
  map_add' := (reindexCotangentMap I).map_add
  map_smul' := reindexCotangentMap_smul_base I

/-- The conormal class of `y₀` dies under the comparison map, because `ρ y₀ = 0`. -/
theorem reindexCotangentMap_hyperplaneCoord :
    reindexCotangentMap I (Ideal.toCotangent (hyperplaneIdeal I)
        ⟨hyperplaneCoord, hyperplaneCoord_mem I⟩) = 0 := by
  rw [reindexCotangentMap_toCotangent, Ideal.toCotangent_eq_zero]
  simp

/-- **The reindexed conormal module map** `hyperplaneCotangent I → J/J²`: the descent of
`reindexCotangentMap` to the quotient of `I'/I'²` by the conormal class of `y₀`. -/
noncomputable def hyperplaneCotangentReindex :
    hyperplaneCotangent I →ₛₗ[reindexBaseHom I] (reindexIdeal I).Cotangent :=
  Submodule.liftQSpanSingleton _ (reindexCotangentSemilinear I)
    (reindexCotangentMap_hyperplaneCoord I)

@[simp]
theorem hyperplaneCotangentReindex_mk (x : (hyperplaneIdeal I).Cotangent) :
    hyperplaneCotangentReindex I (Submodule.Quotient.mk x) = reindexCotangentMap I x :=
  rfl

/-- `J² = ρ(I'²)`. -/
theorem reindexIdeal_sq :
    reindexIdeal I ^ 2 = (hyperplaneIdeal I ^ 2).map reindexAlgHom := by
  rw [Ideal.map_pow, map_hyperplaneIdeal]

/-- **Surjectivity of the reindexed conormal map**: every conormal class of `J` comes from a
conormal class of `I'`, because `J = ρ(I')` and `ρ` is surjective. -/
theorem surjective_hyperplaneCotangentReindex :
    Function.Surjective (hyperplaneCotangentReindex I) := by
  intro z
  obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective (reindexIdeal I) z
  have hy : (y : MvPolynomial (σ ⊕ τ') k) ∈ (hyperplaneIdeal I).map reindexAlgHom := by
    rw [map_hyperplaneIdeal]
    exact y.2
  obtain ⟨a, ha, hav⟩ := (Ideal.mem_map_iff_of_surjective _ surjective_reindexAlgHom).1 hy
  refine ⟨Submodule.Quotient.mk (Ideal.toCotangent (hyperplaneIdeal I) ⟨a, ha⟩), ?_⟩
  rw [hyperplaneCotangentReindex_mk, reindexCotangentMap_toCotangent]
  exact congrArg _ (Subtype.ext hav)

/-- **The kernel of the reindexed conormal map is trivial.**  If the conormal class of `a ∈ I'`
dies in `J/J²` then `ρ a ∈ J² = ρ(I'²)`, so `a` differs from an element of `I'²` by an element of
`ker ρ = (y₀)`; hence the class of `a` in `I'/I'²` is a multiple of the class of `y₀`, i.e. zero in
`hyperplaneCotangent I`. -/
theorem mk_eq_zero_of_reindexCotangentMap_eq_zero (x : (hyperplaneIdeal I).Cotangent)
    (hx : reindexCotangentMap I x = 0) :
    (Submodule.Quotient.mk x : hyperplaneCotangent I) = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective (hyperplaneIdeal I) x
  rw [reindexCotangentMap_toCotangent, Ideal.toCotangent_eq_zero, reindexIdeal_sq] at hx
  obtain ⟨c, hc, hcv⟩ := (Ideal.mem_map_iff_of_surjective _ surjective_reindexAlgHom).1 hx
  have hcv' : reindexAlgHom c = reindexAlgHom (y : MvPolynomial (σ ⊕ Option τ') k) := hcv
  have hcI : c ∈ hyperplaneIdeal I := Ideal.pow_le_self (by norm_num) hc
  have hker : (y : MvPolynomial (σ ⊕ Option τ') k) - c ∈
      Ideal.span {hyperplaneCoord (k := k) (σ := σ) (τ' := τ')} := by
    rw [← comap_bot_reindexAlgHom]
    simp only [Ideal.mem_comap, Ideal.mem_bot, map_sub, hcv', sub_self]
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hker
  have hsplit : y = r • (⟨hyperplaneCoord, hyperplaneCoord_mem I⟩ : hyperplaneIdeal I) +
      ⟨c, hcI⟩ := by
    apply Subtype.ext
    change (y : MvPolynomial (σ ⊕ Option τ') k) =
      r * hyperplaneCoord (k := k) (σ := σ) (τ' := τ') + c
    rw [hr]
    ring
  have hy : Ideal.toCotangent (hyperplaneIdeal I) y =
      r • Ideal.toCotangent (hyperplaneIdeal I)
        (⟨hyperplaneCoord, hyperplaneCoord_mem I⟩ : hyperplaneIdeal I) := by
    rw [hsplit, map_add, map_smul, (Ideal.toCotangent_eq_zero _ ⟨c, hcI⟩).2 hc, add_zero]
  rw [hy, Submodule.Quotient.mk_eq_zero]
  refine Submodule.mem_span_singleton.2 ⟨Ideal.Quotient.mk (hyperplaneIdeal I) r, ?_⟩
  exact IsScalarTower.algebraMap_smul (Base (hyperplaneIdeal I)) r _

/-- **Injectivity of the reindexed conormal map.** -/
theorem injective_hyperplaneCotangentReindex :
    Function.Injective (hyperplaneCotangentReindex I) := by
  intro z w hzw
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [hyperplaneCotangentReindex_mk, hyperplaneCotangentReindex_mk, ← sub_eq_zero,
    ← map_sub] at hzw
  have h := mk_eq_zero_of_reindexCotangentMap_eq_zero I (x - y) hzw
  rw [Submodule.Quotient.mk_eq_zero] at h
  exact (Submodule.Quotient.eq _).2 h

/-- **The reindexed conormal module**: the relative conormal module `hyperplaneCotangent I` of
`X'/Y'` inside the ambient space `𝔸^σ × Y` is the honest conormal module `J/J²` of `X'` inside the
smaller ambient space `𝔸^σ × Y'`, semilinearly over the reindexing isomorphism
`Base (hyperplaneIdeal I) ≃ₐ[k] Base (reindexIdeal I)`. -/
noncomputable def hyperplaneCotangentReindexEquiv :
    hyperplaneCotangent I ≃+ (reindexIdeal I).Cotangent :=
  AddEquiv.ofBijective (hyperplaneCotangentReindex I).toAddMonoidHom
    ⟨injective_hyperplaneCotangentReindex I, surjective_hyperplaneCotangentReindex I⟩

@[simp]
theorem hyperplaneCotangentReindexEquiv_mk (x : (hyperplaneIdeal I).Cotangent) :
    hyperplaneCotangentReindexEquiv I (Submodule.Quotient.mk x) = reindexCotangentMap I x :=
  rfl

/-- Semilinearity of the reindexed conormal isomorphism, in the packaged form. -/
theorem hyperplaneCotangentReindexEquiv_smul (b : Base (hyperplaneIdeal I))
    (x : hyperplaneCotangent I) :
    hyperplaneCotangentReindexEquiv I (b • x) =
      reindexBaseHom I b • hyperplaneCotangentReindexEquiv I x :=
  (hyperplaneCotangentReindex I).map_smul' b x

/-! ### The degree-one terms -/

/-- **The comparison of the degree-one terms** `(σ → Base I') ≃+ (σ → Base J)`: the reindexing
isomorphism of coordinate rings applied coordinatewise.  This is the `σ`-part of the relative
conormal complex, i.e. the relative differentials `⊕_σ dx_s`, which is unaffected by the change of
the `τ`-coordinates. -/
noncomputable def sigmaReindexEquiv :
    (σ → Base (hyperplaneIdeal I)) ≃+ (σ → Base (reindexIdeal I)) :=
  AddEquiv.piCongrRight fun _ => (quotientReindexEquiv I).toRingEquiv.toAddEquiv

@[simp]
theorem sigmaReindexEquiv_apply (f : σ → Base (hyperplaneIdeal I)) (s : σ) :
    sigmaReindexEquiv I f s = quotientReindexEquiv I (f s) :=
  rfl

/-- Semilinearity of the degree-one comparison. -/
theorem sigmaReindexEquiv_smul (b : Base (hyperplaneIdeal I))
    (f : σ → Base (hyperplaneIdeal I)) :
    sigmaReindexEquiv I (b • f) = reindexBaseHom I b • sigmaReindexEquiv I f := by
  funext s
  exact map_mul (quotientReindexEquiv I) b (f s)

/-- **The two relative conormal differentials correspond under the reindexing.**  Both send the
conormal class of `a` to the `σ`-partial derivatives of `a`, and `ρ` commutes with those
(`reindexAlgHom_pderiv`). -/
theorem sigmaReindexEquiv_hyperplaneDifferential (z : hyperplaneCotangent I) :
    sigmaReindexEquiv I (hyperplaneDifferential I z) =
      (RelativeAbsolute.relConormalComplex (reindexIdeal I)).differential
        (hyperplaneCotangentReindexEquiv I z) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective (hyperplaneIdeal I) x
  funext s
  simp only [sigmaReindexEquiv_apply, hyperplaneDifferential_mk,
    hyperplaneCotangentReindexEquiv_mk, reindexCotangentMap_toCotangent,
    LinearMap.comp_apply,
    RelativeAbsolute.sigmaPart_conormalMap_toCotangent, quotientReindexEquiv_mk]
  exact congrArg _ (reindexAlgHom_pderiv s (a : MvPolynomial (σ ⊕ Option τ') k))

/-- **The reindexing isomorphism of two-term complexes**
`hyperplaneConormalComplex I ≅ relConormalComplex (reindexIdeal I)`, semilinear along the
reindexing isomorphism `quotientReindexEquiv I` of coordinate rings: the relative conormal complex
of `X'/Y'` computed inside the ambient space `𝔸^σ × Y` (where the conormal class of the equation
`y₀` has to be divided out) *is* the relative conormal complex of `X' = Spec (R' ⧸ J) ⊆ 𝔸^σ × Y'`
computed inside the smaller ambient space. -/
noncomputable def hyperplaneReindexIso :
    SemilinearIso (quotientReindexEquiv I).toRingEquiv (hyperplaneConormalComplex I)
      (RelativeAbsolute.relConormalComplex (reindexIdeal I)) where
  degreeZero := hyperplaneCotangentReindexEquiv I
  degreeOne := sigmaReindexEquiv I
  map_smul_degreeZero := hyperplaneCotangentReindexEquiv_smul I
  map_smul_degreeOne := sigmaReindexEquiv_smul I
  comm := sigmaReindexEquiv_hyperplaneDifferential I

/-! ### The `Base I`-algebra structure on the reindexed coordinate ring -/

/-- **`Base (reindexIdeal I)` is a `Base I`-algebra** through `Base I → Base I' ≃ Base J`: the
comorphism of the closed immersion `X' = X ×_Y Y' ↪ X`. -/
noncomputable instance algebraReindex : Algebra (Base I) (Base (reindexIdeal I)) :=
  RingHom.toAlgebra ((reindexBaseHom I).comp (algebraMap (Base I) (Base (hyperplaneIdeal I))))

@[simp]
theorem algebraMap_reindex_mk (r : MvPolynomial (σ ⊕ Option τ') k) :
    algebraMap (Base I) (Base (reindexIdeal I)) (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (reindexIdeal I) (reindexAlgHom r) :=
  rfl

@[simp]
theorem reindexBaseHom_symm_apply (b : Base (reindexIdeal I)) :
    reindexBaseHom I ((quotientReindexEquiv I).symm b) = b :=
  (quotientReindexEquiv I).apply_symm_apply b

/-- **The reindexing isomorphism of coordinate rings is `Base I`-linear**, because the
`Base I`-algebra structure of `Base (reindexIdeal I)` is defined through it. -/
noncomputable def baseReindexLinearEquiv :
    Base (hyperplaneIdeal I) ≃ₗ[Base I] Base (reindexIdeal I) where
  toFun := quotientReindexEquiv I
  map_add' := map_add _
  map_smul' b x := by
    rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
    rfl
  invFun := (quotientReindexEquiv I).symm
  left_inv := (quotientReindexEquiv I).left_inv
  right_inv := (quotientReindexEquiv I).right_inv

/-- **The reindexing isomorphism as an isomorphism of `Base I`-algebras**: `X' = X ×_Y Y'` has the
same coordinate ring whether computed inside `𝔸^σ × Y` (as `R ⧸ (I + (y₀))`) or inside `𝔸^σ × Y'`
(as `R' ⧸ J`), compatibly with the closed immersion `X' ↪ X`. -/
noncomputable def quotientReindexAlgEquiv :
    Base (hyperplaneIdeal I) ≃ₐ[Base I] Base (reindexIdeal I) where
  __ := (quotientReindexEquiv I).toRingEquiv
  commutes' _ := rfl

variable (M : Type u) [AddCommGroup M] [Module (Base I) M]

/-- **Comparison of the two base changes** `Base I' ⊗[Base I] M ≃ Base J ⊗[Base I] M` of a
`Base I`-module `M`, induced by the reindexing isomorphism of coordinate rings. -/
noncomputable def tensorReindexEquiv :
    Base (hyperplaneIdeal I) ⊗[Base I] M ≃ₗ[Base I] Base (reindexIdeal I) ⊗[Base I] M :=
  TensorProduct.congr (baseReindexLinearEquiv I) (LinearEquiv.refl (Base I) M)

@[simp]
theorem tensorReindexEquiv_tmul (b : Base (hyperplaneIdeal I)) (m : M) :
    tensorReindexEquiv I M (b ⊗ₜ[Base I] m) = quotientReindexEquiv I b ⊗ₜ[Base I] m :=
  rfl

/-- Semilinearity of the base-change comparison over `Base I'`. -/
theorem tensorReindexEquiv_smul (b : Base (hyperplaneIdeal I))
    (z : Base (hyperplaneIdeal I) ⊗[Base I] M) :
    tensorReindexEquiv I M (b • z) = reindexBaseHom I b • tensorReindexEquiv I M z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul c m =>
    rw [TensorProduct.smul_tmul', tensorReindexEquiv_tmul, tensorReindexEquiv_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
    rfl
  | add z w hz hw => rw [smul_add, map_add, map_add, hz, hw, smul_add]

/-- Semilinearity of the inverse base-change comparison. -/
theorem tensorReindexEquiv_symm_smul (b : Base (reindexIdeal I))
    (z : Base (reindexIdeal I) ⊗[Base I] M) :
    (tensorReindexEquiv I M).symm (b • z) =
      (quotientReindexEquiv I).symm b • (tensorReindexEquiv I M).symm z := by
  apply (tensorReindexEquiv I M).injective
  rw [LinearEquiv.apply_symm_apply, tensorReindexEquiv_smul, LinearEquiv.apply_symm_apply,
    reindexBaseHom_symm_apply]

variable {N : Type u} [AddCommGroup N] [Module (Base I) N]

/-- The base-change comparison is natural in the `Base I`-module. -/
theorem tensorReindexEquiv_baseChange (d : M →ₗ[Base I] N)
    (z : Base (hyperplaneIdeal I) ⊗[Base I] M) :
    tensorReindexEquiv I N (LinearMap.baseChange (Base (hyperplaneIdeal I)) d z) =
      LinearMap.baseChange (Base (reindexIdeal I)) d (tensorReindexEquiv I M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b m =>
    rw [LinearMap.baseChange_tmul, tensorReindexEquiv_tmul, tensorReindexEquiv_tmul,
      LinearMap.baseChange_tmul]
  | add z w hz hw => rw [map_add, map_add, map_add, map_add, hz, hw]

/-- Naturality of the inverse base-change comparison. -/
theorem tensorReindexEquiv_symm_baseChange (d : M →ₗ[Base I] N)
    (z : Base (reindexIdeal I) ⊗[Base I] M) :
    (tensorReindexEquiv I N).symm (LinearMap.baseChange (Base (reindexIdeal I)) d z) =
      LinearMap.baseChange (Base (hyperplaneIdeal I)) d ((tensorReindexEquiv I M).symm z) := by
  apply (tensorReindexEquiv I N).injective
  rw [LinearEquiv.apply_symm_apply, tensorReindexEquiv_baseChange, LinearEquiv.apply_symm_apply]

end Reindex

/-! ## The reindexed relative obstruction datum -/

section ReindexHom

open RelativeVirtualClassBaseChange
open GromovWitten.AlgebraicGeometry.NormalConeAction (Base)

variable {k : Type u} [CommRing k] {σ τ' : Type u} [Fintype σ]
variable (I : Ideal (MvPolynomial (σ ⊕ Option τ') k))
variable {E : LinearTwoTermComplex (Base I)}

/-- **The degree-zero component of the reindexed datum**: the degree-zero component of
`hyperplaneHom φ`, conjugated by the reindexing comparisons. -/
noncomputable def reindexBaseChangeZero
    (φ : Hom E (RelativeAbsolute.relConormalComplex I)) :
    Base (reindexIdeal I) ⊗[Base I] E.degreeZero →ₗ[Base (reindexIdeal I)]
      (reindexIdeal I).Cotangent where
  toFun z := hyperplaneCotangentReindexEquiv I
    ((hyperplaneHom I φ).degreeZero ((tensorReindexEquiv I E.degreeZero).symm z))
  map_add' z w := by rw [map_add, map_add, map_add]
  map_smul' b z := by
    rw [RingHom.id_apply, tensorReindexEquiv_symm_smul, map_smul,
      hyperplaneCotangentReindexEquiv_smul, reindexBaseHom_symm_apply]

/-- **The degree-one component of the reindexed datum**. -/
noncomputable def reindexBaseChangeOne
    (φ : Hom E (RelativeAbsolute.relConormalComplex I)) :
    Base (reindexIdeal I) ⊗[Base I] E.degreeOne →ₗ[Base (reindexIdeal I)]
      (σ → Base (reindexIdeal I)) where
  toFun z := sigmaReindexEquiv I
    ((hyperplaneHom I φ).degreeOne ((tensorReindexEquiv I E.degreeOne).symm z))
  map_add' z w := by rw [map_add, map_add, map_add]
  map_smul' b z := by
    rw [RingHom.id_apply, tensorReindexEquiv_symm_smul, map_smul,
      sigmaReindexEquiv_smul, reindexBaseHom_symm_apply]

/-- **The reindexed relative obstruction datum of `X'/Y'`**: the chain map
`E ⊗ Base J ⟶ relConormalComplex J` obtained from `hyperplaneHom φ` by transporting along the
reindexing isomorphism `hyperplaneReindexIso`.  Its target is now the relative conormal complex of
an honest ideal `J` of the polynomial ring `k[x_σ, y_{τ'}]` of `𝔸^σ × Y'`, so that all the
machinery of `RelativeAbsolute.lean` (`absHom`, `Gr`, `relProductMap`, `ideal'`,
`relativeVirtualClass`) applies to it verbatim. -/
noncomputable def reindexHom (φ : Hom E (RelativeAbsolute.relConormalComplex I)) :
    Hom (E.baseChange (Base (reindexIdeal I)))
      (RelativeAbsolute.relConormalComplex (reindexIdeal I)) where
  degreeZero := reindexBaseChangeZero I φ
  degreeOne := reindexBaseChangeOne I φ
  comm z := by
    have hcomm := (hyperplaneHom I φ).comm ((tensorReindexEquiv I E.degreeZero).symm z)
    rw [LinearTwoTermComplex.baseChange_differential] at hcomm
    change sigmaReindexEquiv I ((hyperplaneHom I φ).degreeOne
        ((tensorReindexEquiv I E.degreeOne).symm
          (LinearMap.baseChange (Base (reindexIdeal I)) E.differential z))) =
      (RelativeAbsolute.relConormalComplex (reindexIdeal I)).differential
        (hyperplaneCotangentReindexEquiv I ((hyperplaneHom I φ).degreeZero
          ((tensorReindexEquiv I E.degreeZero).symm z)))
    rw [tensorReindexEquiv_symm_baseChange, hcomm]
    exact sigmaReindexEquiv_hyperplaneDifferential I _

@[simp]
theorem reindexHom_degreeZero_apply (φ : Hom E (RelativeAbsolute.relConormalComplex I))
    (z : Base (reindexIdeal I) ⊗[Base I] E.degreeZero) :
    (reindexHom I φ).degreeZero z = hyperplaneCotangentReindexEquiv I
      ((hyperplaneHom I φ).degreeZero ((tensorReindexEquiv I E.degreeZero).symm z)) :=
  rfl

@[simp]
theorem reindexHom_degreeOne_apply (φ : Hom E (RelativeAbsolute.relConormalComplex I))
    (z : Base (reindexIdeal I) ⊗[Base I] E.degreeOne) :
    (reindexHom I φ).degreeOne z = sigmaReindexEquiv I
      ((hyperplaneHom I φ).degreeOne ((tensorReindexEquiv I E.degreeOne).symm z)) :=
  rfl

/-- The degree-zero comparison square of the reindexing. -/
theorem hyperplaneCotangentReindexEquiv_degreeZero
    (φ : Hom E (RelativeAbsolute.relConormalComplex I))
    (x : Base (hyperplaneIdeal I) ⊗[Base I] E.degreeZero) :
    hyperplaneCotangentReindexEquiv I ((hyperplaneHom I φ).degreeZero x) =
      (reindexHom I φ).degreeZero (tensorReindexEquiv I E.degreeZero x) := by
  rw [reindexHom_degreeZero_apply]
  exact congrArg _ (congrArg _ ((tensorReindexEquiv I E.degreeZero).symm_apply_apply x).symm)

/-- The degree-one comparison square of the reindexing. -/
theorem sigmaReindexEquiv_degreeOne
    (φ : Hom E (RelativeAbsolute.relConormalComplex I))
    (x : Base (hyperplaneIdeal I) ⊗[Base I] E.degreeOne) :
    sigmaReindexEquiv I ((hyperplaneHom I φ).degreeOne x) =
      (reindexHom I φ).degreeOne (tensorReindexEquiv I E.degreeOne x) := by
  rw [reindexHom_degreeOne_apply]
  exact congrArg _ (congrArg _ ((tensorReindexEquiv I E.degreeOne).symm_apply_apply x).symm)

/-- **The reindexed hyperplane datum is a relative obstruction theory.**  If `φ` is a relative
obstruction theory for `X = Spec (R ⧸ I) → Y = 𝔸^{Option τ'}`, then `reindexHom I φ` is a relative
obstruction theory for `X' = X ×_Y Y' = Spec (R' ⧸ J) → Y' = 𝔸^{τ'}`, where
`R' = k[x_σ, y_{τ'}]` and `J = reindexIdeal I = ρ(I)`.  No regularity hypothesis on the equation
`y₀` of the hyperplane is required: this is `RelativeHyperplaneObstruction`'s
`isObstructionTheory_hyperplaneHom` transported along `hyperplaneReindexIso`. -/
theorem isObstructionTheory_reindexed_hyperplaneHom
    {φ : Hom E (RelativeAbsolute.relConormalComplex I)} (hφ : IsObstructionTheory φ) :
    IsObstructionTheory (reindexHom I φ) := by
  exact isObstructionTheory_of_addEquiv (tensorReindexEquiv I E.degreeZero).toAddEquiv
    (tensorReindexEquiv I E.degreeOne).toAddEquiv (hyperplaneCotangentReindexEquiv I)
    (sigmaReindexEquiv I) (tensorReindexEquiv_baseChange I E.degreeZero E.differential)
    (sigmaReindexEquiv_hyperplaneDifferential I)
    (hyperplaneCotangentReindexEquiv_degreeZero I φ) (sigmaReindexEquiv_degreeOne I φ)
    (RelativeHyperplaneObstruction.isObstructionTheory_hyperplaneHom I hφ)

/-- **The reindexing does not change the obstruction-theory property**: `reindexHom I φ` is an
obstruction theory exactly when `hyperplaneHom I φ` is. -/
theorem isObstructionTheory_reindexHom_iff (φ : Hom E (RelativeAbsolute.relConormalComplex I)) :
    IsObstructionTheory (reindexHom I φ) ↔ IsObstructionTheory (hyperplaneHom I φ) :=
  (isObstructionTheory_addEquiv_iff (tensorReindexEquiv I E.degreeZero).toAddEquiv
    (tensorReindexEquiv I E.degreeOne).toAddEquiv (hyperplaneCotangentReindexEquiv I)
    (sigmaReindexEquiv I) (tensorReindexEquiv_baseChange I E.degreeZero E.differential)
    (sigmaReindexEquiv_hyperplaneDifferential I)
    (hyperplaneCotangentReindexEquiv_degreeZero I φ) (sigmaReindexEquiv_degreeOne I φ)).symm

/-- **Regularity makes the reindexed hyperplane base change reflect the obstruction-theory
property**: for `y₀` a non-zero-divisor on `Base I = R ⧸ I`, `reindexHom I φ` is an obstruction
theory for `X'/Y'` if and only if the plain degreewise base change of `φ` along
`Base I → Base I'` is one.  This combines `isObstructionTheory_reindexHom_iff` with
`RelativeHyperplaneObstruction.isObstructionTheory_hyperplaneHom_iff`. -/
theorem isObstructionTheory_reindexHom_iff_baseChange
    (hreg : IsSMulRegular (Base I)
      (Ideal.Quotient.mk I (hyperplaneCoord (k := k) (σ := σ) (τ' := τ'))))
    (φ : Hom E (RelativeAbsolute.relConormalComplex I)) :
    IsObstructionTheory (reindexHom I φ) ↔
      IsObstructionTheory (φ.baseChange (Base (hyperplaneIdeal I))) :=
  (isObstructionTheory_reindexHom_iff I φ).trans
    (RelativeHyperplaneObstruction.isObstructionTheory_hyperplaneHom_iff I hreg φ)

/-! ### The virtual dimension drops by exactly one -/

section Dimension

variable [Fintype τ'] [Nontrivial (Base I)] [Nontrivial (Base (reindexIdeal I))]
variable [Module.Free (Base I) E.degreeZero]
variable [Module.Free (Base I) E.degreeOne] [Module.Finite (Base I) E.degreeOne]

/-- **The virtual dimension of the hyperplane base change is one less than that of the original
datum**: `vdim [X'/Y'] + 1 = vdim [X/Y]`, read absolutely through `RelativeAbsolute.absHom`.  The
*relative* contributions agree, because the degreewise base change of a finite free module has the
same rank (`Module.finrank_baseChange`), and the base drops one dimension,
`#(Option τ') = #τ' + 1`.  This is the expected-dimension count for the Gysin pullback along the
regular embedding `Y' ↪ Y` of codimension one. -/
theorem virtualDimension_absHom_reindexHom
    (φ : Hom E (RelativeAbsolute.relConormalComplex I)) :
    VirtualClass.virtualDimension (RelativeAbsolute.absHom (reindexHom I φ)) + 1 =
      VirtualClass.virtualDimension (RelativeAbsolute.absHom φ) := by
  rw [RelativeAbsolute.virtualDimension_absHom, RelativeAbsolute.virtualDimension_absHom,
    Module.finrank_baseChange, Module.finrank_baseChange, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_option]
  push_cast
  ring

end Dimension

/-! ### The relative virtual class of the hyperplane base change -/

section VirtualClass

open IntersectionTheory

variable [Fintype τ'] [IsNoetherianRing k]
variable [Module.Free (Base (reindexIdeal I)) (Base (reindexIdeal I) ⊗[Base I] E.degreeZero)]
variable [Module.Finite (Base (reindexIdeal I)) (Base (reindexIdeal I) ⊗[Base I] E.degreeZero)]
variable (φ : Hom E (RelativeAbsolute.relConormalComplex I))
variable {ι : Type u} [Finite ι]
variable (bundleChart :
  ResolvedCone.bundleRing (RelativeAbsolute.absHom (reindexHom I φ)) ≃ₐ[Base (reindexIdeal I)]
    MvPolynomial ι (Base (reindexIdeal I)))
variable (dimX : DimensionFunction
  (_root_.AlgebraicGeometry.Spec (CommRingCat.of (Base (reindexIdeal I)))))
variable (dimE : DimensionFunction
  (ResolvedCone.bundleSpace (RelativeAbsolute.absHom (reindexHom I φ)))) (i : ℤ)
variable (RX : RationalEquivalenceSystem
  (_root_.AlgebraicGeometry.Spec (CommRingCat.of (Base (reindexIdeal I)))) dimX i)
variable (RE : RationalEquivalenceSystem
  (ResolvedCone.bundleSpace (RelativeAbsolute.absHom (reindexHom I φ))) dimE
  (i + (Nat.card ι : ℤ)))

/-- **`[X'/Y']^vir`, the relative virtual class of the hyperplane base change.**  By
`isObstructionTheory_reindexed_hyperplaneHom` the reindexed datum `reindexHom I φ` is a relative
obstruction theory for `X' = X ×_Y Y' → Y' = 𝔸^{τ'}` with target the relative conormal complex of
the ideal `J = reindexIdeal I` of the polynomial ring of `𝔸^σ × Y'`; this is therefore
`RelativeAbsolute.relativeVirtualClass` of that datum, i.e. the Gysin image of the class of its
resolved cone.  The identification of this class with the Gysin pullback `i^![X/Y]^vir` along the
regular embedding `i : Y' ↪ Y` is *not* proved here: it requires the identity of resolved-cone
ideals `ResolvedCone.ideal (reindexHom I φ) = (ResolvedCone.ideal φ).map …`, which is a separate
`BaseChangeConeIdeal`-style ring comparison. -/
noncomputable def relativeVirtualClass_hyperplane
    (hhom : PrincipalDivisorsHomogeneous
      (ResolvedCone.bundleSpace (RelativeAbsolute.absHom (reindexHom I φ))) dimE)
    (hinj : Function.Injective
      (VectorBundle.chowPullbackBundle bundleChart dimX dimE i RX RE)) :
    RX.ChowGroup :=
  RelativeAbsolute.relativeVirtualClass (reindexHom I φ) bundleChart dimX dimE i RX RE hhom hinj

/-- **The relative virtual class of the hyperplane base change is the virtual class of the
associated absolute obstruction theory**, by `RelativeAbsolute.virtualClassAt_absHom` applied to
the reindexed datum. -/
theorem virtualClassAt_absHom_reindexHom
    (hhom : PrincipalDivisorsHomogeneous
      (ResolvedCone.bundleSpace (RelativeAbsolute.absHom (reindexHom I φ))) dimE)
    (hinj : Function.Injective
      (VectorBundle.chowPullbackBundle bundleChart dimX dimE i RX RE)) :
    VirtualClass.virtualClassAt (RelativeAbsolute.absHom (reindexHom I φ)) bundleChart dimX dimE i
        RX RE hhom hinj =
      relativeVirtualClass_hyperplane I φ bundleChart dimX dimE i RX RE hhom hinj :=
  RelativeAbsolute.virtualClassAt_absHom (reindexHom I φ) bundleChart dimX dimE i RX RE hhom hinj

end VirtualClass

end ReindexHom

/-! ## The comparison of associated graded rings -/

section AssociatedGraded

open RelativeVirtualClassBaseChange AffineNormalCone
open GromovWitten.AlgebraicGeometry.NormalConeAction (Base)
open ConeTranslation (Gr)

variable {k : Type u} [CommRing k] {σ τ' : Type u}
variable (I : Ideal (MvPolynomial (σ ⊕ Option τ') k))

/-- `ρ` as a ring homomorphism, for `Polynomial.map`. -/
noncomputable abbrev reindexRingHom :
    MvPolynomial (σ ⊕ Option τ') k →+* MvPolynomial (σ ⊕ τ') k :=
  (reindexAlgHom : MvPolynomial (σ ⊕ Option τ') k →ₐ[k] MvPolynomial (σ ⊕ τ') k).toRingHom

/-- `ρ(Iⁿ) ⊆ Jⁿ`. -/
theorem reindexAlgHom_mem_pow {n : ℕ} {a : MvPolynomial (σ ⊕ Option τ') k} (ha : a ∈ I ^ n) :
    reindexAlgHom a ∈ reindexIdeal I ^ n := by
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ha

/-- `ρ` carries the Rees algebra of `I` into the Rees algebra of `J`. -/
theorem map_mem_reesAlgebra (x : reesAlgebra I) :
    Polynomial.map (reindexRingHom (k := k) (σ := σ) (τ' := τ'))
        (x : Polynomial (MvPolynomial (σ ⊕ Option τ') k)) ∈ reesAlgebra (reindexIdeal I) := by
  intro n
  rw [Polynomial.coeff_map]
  exact reindexAlgHom_mem_pow I (x.2 n)

/-- **The Rees-algebra comparison map** `R[It] → R'[Jt]` induced by `ρ`. -/
noncomputable def reesReindexHom : reesAlgebra I →+* reesAlgebra (reindexIdeal I) where
  toFun x := ⟨Polynomial.map reindexRingHom (x : Polynomial _), map_mem_reesAlgebra I x⟩
  map_one' := by
    apply Subtype.ext
    exact Polynomial.map_one _
  map_mul' x y := by
    apply Subtype.ext
    exact Polynomial.map_mul _
  map_zero' := by
    apply Subtype.ext
    exact Polynomial.map_zero _
  map_add' x y := by
    apply Subtype.ext
    exact Polynomial.map_add _

@[simp]
theorem coe_reesReindexHom (x : reesAlgebra I) :
    (reesReindexHom I x : Polynomial (MvPolynomial (σ ⊕ τ') k)) =
      Polynomial.map reindexRingHom (x : Polynomial (MvPolynomial (σ ⊕ Option τ') k)) :=
  rfl

/-- The Rees comparison map sends the structural image of `a` to the structural image of `ρ a`. -/
theorem reesReindexHom_algebraMap (a : MvPolynomial (σ ⊕ Option τ') k) :
    reesReindexHom I (algebraMap (MvPolynomial (σ ⊕ Option τ') k) (reesAlgebra I) a) =
      algebraMap (MvPolynomial (σ ⊕ τ') k) (reesAlgebra (reindexIdeal I)) (reindexAlgHom a) := by
  apply Subtype.ext
  rw [coe_reesReindexHom]
  change Polynomial.map reindexRingHom (Polynomial.C a) = Polynomial.C (reindexAlgHom a)
  rw [Polynomial.map_C]
  rfl

/-- The Rees comparison map carries the ideal defining `gr_I(R)` into the ideal defining
`gr_J(R')`. -/
theorem reesIdeal_le_comap :
    Ideal.map (algebraMap (MvPolynomial (σ ⊕ Option τ') k) (reesAlgebra I)) I ≤
      Ideal.comap (reesReindexHom I)
        (Ideal.map (algebraMap (MvPolynomial (σ ⊕ τ') k) (reesAlgebra (reindexIdeal I)))
          (reindexIdeal I)) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Ideal.mem_comap, reesReindexHom_algebraMap]
  exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)

/-- The hypothesis of `Ideal.Quotient.lift` for `grReindexHom`. -/
theorem forall_mem_reesIdeal_eq_zero :
    ∀ a ∈ Ideal.map (algebraMap (MvPolynomial (σ ⊕ Option τ') k) (reesAlgebra I)) I,
      ((Ideal.Quotient.mk
        (Ideal.map (algebraMap (MvPolynomial (σ ⊕ τ') k) (reesAlgebra (reindexIdeal I)))
          (reindexIdeal I))).comp (reesReindexHom I)) a = 0 := by
  intro a ha
  exact Ideal.Quotient.eq_zero_iff_mem.2 (reesIdeal_le_comap I ha)

/-- **The comparison of associated graded rings** `gr_I(R) → gr_J(R')` induced by `ρ`: the
coordinate-ring map of the closed immersion of the normal cone of `X' ⊆ 𝔸^σ × Y'` into the
base change along `X' ↪ X` of the normal cone of `X ⊆ 𝔸^σ × Y`. -/
noncomputable def grReindexHom : Gr I →+* Gr (reindexIdeal I) :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk
      (Ideal.map (algebraMap (MvPolynomial (σ ⊕ τ') k) (reesAlgebra (reindexIdeal I)))
        (reindexIdeal I))).comp (reesReindexHom I))
    (forall_mem_reesIdeal_eq_zero I)

@[simp]
theorem grReindexHom_mk (x : reesAlgebra I) :
    grReindexHom I (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (reesReindexHom I x) :=
  rfl

/-- `I ≤ ρ⁻¹(J)`, the hypothesis of `Ideal.mapCotangent` for `I` itself. -/
theorem le_comap_reindexIdeal : I ≤ Ideal.comap reindexAlgHom (reindexIdeal I) :=
  Ideal.le_comap_map

/-- **The conormal comparison map of `I` itself**, `I/I² → J/J²`, induced by `ρ`. -/
noncomputable def idealCotangentReindex :
    I.Cotangent →ₗ[k] (reindexIdeal I).Cotangent :=
  Ideal.mapCotangent I (reindexIdeal I) reindexAlgHom (le_comap_reindexIdeal I)

@[simp]
theorem idealCotangentReindex_toCotangent (x : I) :
    idealCotangentReindex I (Ideal.toCotangent I x) =
      Ideal.toCotangent (reindexIdeal I)
        ⟨reindexAlgHom (x : MvPolynomial (σ ⊕ Option τ') k), le_comap_reindexIdeal I x.2⟩ :=
  rfl

/-- **The graded comparison map is compatible with the degree-one inclusions of the conormal
modules**: `gr_I(R) → gr_J(R')` restricts to `I/I² → J/J²`. -/
theorem grReindexHom_conormalToAssociatedGraded (m : I.Cotangent) :
    grReindexHom I (conormalToAssociatedGraded (MvPolynomial (σ ⊕ Option τ') k) I m) =
      conormalToAssociatedGraded (MvPolynomial (σ ⊕ τ') k) (reindexIdeal I)
        (idealCotangentReindex I m) := by
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective I m
  rw [conormalToAssociatedGraded_toCotangent, grReindexHom_mk, idealCotangentReindex_toCotangent,
    conormalToAssociatedGraded_toCotangent]
  refine congrArg _ (Subtype.ext ?_)
  rw [coe_reesReindexHom, degreeOneRees_coe, degreeOneRees_coe, Polynomial.map_monomial]
  rfl

/-- **The graded comparison map is a map of algebras over the coordinate rings**: it is compatible
with the structural maps `Base I → gr_I(R)` and `Base J → gr_J(R')` through the reindexing
`Base I → Base J`. -/
theorem grReindexHom_algebraMap (b : Base I) :
    grReindexHom I (algebraMap (Base I) (Gr I) b) =
      algebraMap (Base (reindexIdeal I)) (Gr (reindexIdeal I))
        (algebraMap (Base I) (Base (reindexIdeal I)) b) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
  change grReindexHom I (Ideal.Quotient.mk _
      (algebraMap (MvPolynomial (σ ⊕ Option τ') k) (reesAlgebra I) r)) = _
  rw [grReindexHom_mk, reesReindexHom_algebraMap, algebraMap_reindex_mk]
  rfl

/-- **The Rees-algebra comparison map is surjective**: an element of `R'[Jt]` has all its
coefficients in `Jⁿ = ρ(Iⁿ)`, so it lifts coefficientwise. -/
theorem surjective_reesReindexHom : Function.Surjective (reesReindexHom I) := by
  classical
  intro q
  have hcoeff : ∀ n : ℕ, ∃ a : MvPolynomial (σ ⊕ Option τ') k,
      a ∈ I ^ n ∧ reindexAlgHom a = (q : Polynomial (MvPolynomial (σ ⊕ τ') k)).coeff n := by
    intro n
    have h : ((q : Polynomial (MvPolynomial (σ ⊕ τ') k)).coeff n) ∈ (I ^ n).map reindexAlgHom := by
      rw [Ideal.map_pow]
      exact q.2 n
    exact (Ideal.mem_map_iff_of_surjective _ surjective_reindexAlgHom).1 h
  choose a ha hav using hcoeff
  refine ⟨⟨∑ n ∈ (q : Polynomial (MvPolynomial (σ ⊕ τ') k)).support,
      Polynomial.monomial n (a n), Subalgebra.sum_mem _ fun n _ =>
        reesAlgebra.monomial_mem.2 (ha n)⟩, ?_⟩
  apply Subtype.ext
  rw [coe_reesReindexHom]
  change Polynomial.map reindexRingHom
    (∑ n ∈ (q : Polynomial (MvPolynomial (σ ⊕ τ') k)).support, Polynomial.monomial n (a n)) = _
  rw [← Polynomial.coe_mapRingHom, map_sum]
  have hval : ∀ n, reindexRingHom (a n) =
      (q : Polynomial (MvPolynomial (σ ⊕ τ') k)).coeff n := hav
  simp only [Polynomial.coe_mapRingHom, Polynomial.map_monomial, hval]
  exact ((q : Polynomial (MvPolynomial (σ ⊕ τ') k)).as_sum_support).symm

/-- **The comparison of associated graded rings is surjective.**  Geometrically: the normal cone
`C_{X'/𝔸^σ×Y'} = Spec gr_J(R')` is a *closed subcone* of the normal cone `C_{X/𝔸^σ×Y}`, and (since
`grReindexHom` is a `Base J`-algebra map by `grReindexHom_algebraMap`) of its base change along
`X' ↪ X`.  This is the Behrend–Fantechi closed immersion of normal cones; the remaining, harder
statement — that it is an *isomorphism* onto the base change, which is what the resolved-cone
ideal identity needs — is a Tor-independence statement in all degrees and is not proved here. -/
theorem surjective_grReindexHom : Function.Surjective (grReindexHom I) := by
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨x, rfl⟩ := surjective_reesReindexHom I y
  exact ⟨Ideal.Quotient.mk _ x, rfl⟩

end AssociatedGraded

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeHyperplaneReindex
