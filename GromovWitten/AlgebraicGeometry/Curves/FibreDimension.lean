/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.Algebra.FiniteTypeKrullDimension
import GromovWitten.AlgebraicGeometry.Curves.SmoothLocusDimension

/-!
# The fibre-dimension inequality and composition of relative dimensions

For a morphism `q : Z ⟶ W` of schemes locally of finite type over a field `K`, the dimension of
`Z` is at most the dimension of `W` plus the supremum of the dimensions of the fibres of `q`
(`topologicalKrullDim_le_of_fibers`).  The proof reduces, through affine charts, to the algebraic
fibre-dimension formula `coheight_eq_coheight_add_coheight_fiberPrime`: a chain of
specializations ending at a point `z` lies entirely in any affine open containing its most
special point, hence inside an affine chart `Spec T → Spec R` of `q`, where its length is bounded
by the coheight of the prime of `z`, which is the coheight of its contraction plus its coheight
in the fibre ring.

Applied to the geometric fibres of a composite `X ⟶ Y ⟶ S`, this proves that geometric relative
dimension bounds add under composition (`GeometricRelativeDimensionLE.comp`), which is roadmap
item L0.2.
-/

open CategoryTheory Limits Topology TopologicalSpace
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

/-! ### The fibre of an affine chart -/

/-- The fibre of an affine chart `(U, V)` of `q` over the point of `U` corresponding to a prime
`Q` of `Γ(W, U)` is the spectrum of the fibre ring `κ(Q) ⊗ Γ(Z, V)`. -/
def chartFiberHomeomorph {Z W : Scheme.{u}} (q : Z ⟶ W) {U : W.Opens} (hU : IsAffineOpen U)
    {V : Z.Opens} (hV : IsAffineOpen V) (e : V ≤ q ⁻¹ᵁ U) (Q : PrimeSpectrum Γ(W, U)) :
    letI := (q.appLE U V e).hom.toAlgebra
    (hV.fromSpec ≫ q).fiber (hU.fromSpec Q) ≃ₜ PrimeSpectrum (Q.asIdeal.Fiber Γ(Z, V)) := by
  letI := (q.appLE U V e).hom.toAlgebra
  have hcomm : Spec.map (q.appLE U V e) ≫ hU.fromSpec = hV.fromSpec ≫ q :=
    hU.SpecMap_appLE_fromSpec q hV e
  have hφ : CommRingCat.ofHom (algebraMap Γ(W, U) Γ(Z, V)) = q.appLE U V e := by
    change CommRingCat.ofHom (q.appLE U V e).hom = _
    exact CommRingCat.ofHom_hom _
  have hset : (hV.fromSpec ≫ q) ⁻¹' {hU.fromSpec Q} =
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(W, U) Γ(Z, V)))) ⁻¹' {Q} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    have hz : hU.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(W, U) Γ(Z, V))) z) =
        (hV.fromSpec ≫ q) z := by
      rw [hφ, ← Scheme.Hom.comp_apply, hcomm]
    rw [← hz]
    exact hU.fromSpec.isOpenEmbedding.injective.eq_iff
  exact ((hV.fromSpec ≫ q).fiberHomeo _).trans <| (Homeomorph.setCongr hset).trans <|
    ((Spec.map (CommRingCat.ofHom (algebraMap Γ(W, U) Γ(Z, V)))).fiberHomeo Q).symm.trans
      (specFiberHomeomorph Γ(W, U) Γ(Z, V) Q)

/-! ### Structure maps to `Spec K` as `K`-algebras on affine opens -/

section Field

variable {K : Type u} [Field K]

/-- The `K`-algebra structure on the sections of a `K`-scheme over an open. -/
abbrev sectionsAlgebra {Z : Scheme.{u}} (π : Z ⟶ Spec (.of K)) (V : Z.Opens) :
    Algebra K Γ(Z, V) :=
  ((π.appLE ⊤ V (by simp)).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra

theorem sectionsAlgebra_algebraMap {Z : Scheme.{u}} (π : Z ⟶ Spec (.of K)) (V : Z.Opens) :
    letI := sectionsAlgebra π V
    algebraMap K Γ(Z, V) =
      (π.appLE ⊤ V (by simp)).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom := rfl

/-- Sections of a `K`-scheme locally of finite type over an affine open form a finitely
generated `K`-algebra. -/
theorem sectionsAlgebra_finiteType {Z : Scheme.{u}} (π : Z ⟶ Spec (.of K))
    [LocallyOfFiniteType π] {V : Z.Opens} (hV : IsAffineOpen V) :
    letI := sectionsAlgebra π V
    Algebra.FiniteType K Γ(Z, V) := by
  let _ := sectionsAlgebra π V
  have h1 : (π.appLE ⊤ V (by simp)).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) π inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _
  have h2 : (Scheme.ΓSpecIso (.of K)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
  exact h1.comp h2

end Field

/-! ### Chains of specializations and affine charts -/

section Chains

variable {Z : Scheme.{u}}

/-- On `Spec R`, the height of a point in the specialization order is the coheight of the
corresponding prime ideal. -/
theorem height_spec_eq_coheight (R : CommRingCat.{u}) (x : PrimeSpectrum R) :
    @Order.height (Spec R) _ x = Order.coheight x :=
  (Order.height_orderIso (specOrderIsoPrimeSpectrum R) x).symm.trans
    (Order.coheight_ofDual (OrderDual.toDual x)).symm

/-- An open immersion is strictly monotone for the specialization orders. -/
theorem strictMono_of_isOpenImmersion {Y : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j] :
    StrictMono j := by
  intro a b hab
  rw [lt_iff_le_not_ge] at hab ⊢
  change (b ⤳ a) ∧ ¬ (a ⤳ b) at hab
  change (j b ⤳ j a) ∧ ¬ (j a ⤳ j b)
  rwa [j.isOpenEmbedding.isInducing.specializes_iff, j.isOpenEmbedding.isInducing.specializes_iff]

/-- A chain of specializations lies in every open set containing its most special point, and
inside an affine open of that kind its length is bounded by the coheight of the prime of its
last point.  The affine open may be chosen inside any open neighbourhood `O` of the most
special point. -/
theorem exists_affineOpen_length_le_coheight (p : LTSeries Z) (O : Z.Opens) (hO : p.head ∈ O) :
    ∃ (V : Z.Opens) (hV : IsAffineOpen V) (_ : V ≤ O) (hz : p.last ∈ V),
      (p.length : ℕ∞) ≤ Order.coheight (hV.primeIdealOf ⟨p.last, hz⟩) := by
  obtain ⟨_, ⟨V, hV', rfl⟩, hz₀V, hVO⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open hO O.2
  have hV : IsAffineOpen V := hV'
  have hmemV : ∀ i, p i ∈ Set.range hV.fromSpec := by
    intro i
    rw [hV.range_fromSpec]
    have hle : p.head ≤ p i := p.monotone (Fin.zero_le i)
    exact Specializes.mem_open hle V.2 hz₀V
  choose x hx using hmemV
  let p' : LTSeries (Spec Γ(Z, V)) :=
    { length := p.length
      toFun := x
      step := fun i ↦ by
        have hlt : p i.castSucc < p i.succ := p.step i
        change x i.castSucc < x i.succ
        rw [lt_iff_le_not_ge] at hlt ⊢
        change (p i.succ ⤳ p i.castSucc) ∧ ¬ (p i.castSucc ⤳ p i.succ) at hlt
        change (x i.succ ⤳ x i.castSucc) ∧ ¬ (x i.castSucc ⤳ x i.succ)
        rw [← hx, ← hx] at hlt
        rwa [hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff,
          hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff] at hlt }
  have hlast : p.last ∈ V := by
    have hmem : hV.fromSpec (x (Fin.last _)) ∈ (V : Set Z) :=
      hV.range_fromSpec ▸ Set.mem_range_self _
    rwa [hx] at hmem
  refine ⟨V, hV, hVO, hlast, ?_⟩
  have hP : hV.primeIdealOf ⟨p.last, hlast⟩ = p'.last := by
    apply hV.fromSpec.isOpenEmbedding.injective
    rw [hV.fromSpec_primeIdealOf]
    exact (hx _).symm
  calc (p.length : ℕ∞) ≤ Order.height p'.last := Order.length_le_height_last
    _ = @Order.coheight (PrimeSpectrum Γ(Z, V)) _ p'.last := height_spec_eq_coheight _ _
    _ = Order.coheight (hV.primeIdealOf ⟨p.last, hlast⟩) := by rw [hP]

/-- The coheight of the prime of a point in an affine chart is at most the height of the point:
chains of primes below the prime are chains of specializations of the point. -/
theorem coheight_primeIdealOf_le_height {V : Z.Opens} (hV : IsAffineOpen V) {z : Z}
    (hz : z ∈ V) : Order.coheight (hV.primeIdealOf ⟨z, hz⟩) ≤ Order.height z := by
  have h := Order.height_le_height_apply_of_strictMono hV.fromSpec
    (strictMono_of_isOpenImmersion hV.fromSpec) (hV.primeIdealOf ⟨z, hz⟩)
  rw [hV.fromSpec_primeIdealOf, height_spec_eq_coheight] at h
  exact h

end Chains

/-! ### Chart independence of the coheight of a point over a field -/

section PointDimension

variable {K : Type u} [Field K] {Z : Scheme.{u}} (π : Z ⟶ Spec (.of K))

/-- The `K`-algebra structure on the residue field of the stalk at a point of a `K`-scheme. -/
abbrev stalkResidueFieldAlgebra (z : Z) :
    Algebra K (IsLocalRing.ResidueField (Z.presheaf.stalk z)) :=
  ((IsLocalRing.residue _).comp ((Z.presheaf.germ (π ⁻¹ᵁ ⊤) z (by simp)).hom.comp
    ((π.app ⊤).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom))).toAlgebra

/-- The residue field of the prime of a point in an affine chart is the residue field of the
stalk at the point, compatibly with the `K`-algebra structures. -/
def chartResidueFieldAlgEquiv {V : Z.Opens} (hV : IsAffineOpen V) {z : Z} (hz : z ∈ V) :
    letI := sectionsAlgebra π V
    letI := stalkResidueFieldAlgebra π z
    (hV.primeIdealOf ⟨z, hz⟩).asIdeal.ResidueField ≃ₐ[K]
      IsLocalRing.ResidueField (Z.presheaf.stalk z) := by
  letI := sectionsAlgebra π V
  letI := stalkResidueFieldAlgebra π z
  letI : Algebra Γ(Z, V) (Z.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk Z.presheaf ⟨z, hz⟩
  have hloc : IsLocalization.AtPrime (Z.presheaf.stalk z) (hV.primeIdealOf ⟨z, hz⟩).asIdeal :=
    hV.isLocalization_stalk ⟨z, hz⟩
  let e : Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal ≃ₐ[Γ(Z, V)]
      Z.presheaf.stalk z :=
    IsLocalization.algEquiv (hV.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl _ _
  refine AlgEquiv.ofRingEquiv (f := IsLocalRing.ResidueField.mapEquiv e.toRingEquiv) ?_
  intro c
  rw [IsLocalRing.ResidueField.mapEquiv_apply,
    IsScalarTower.algebraMap_apply K (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal),
    IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ResidueField.map_residue,
    IsScalarTower.algebraMap_apply K Γ(Z, V)
      (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal)]
  change IsLocalRing.residue _ (e (algebraMap Γ(Z, V) _ (algebraMap K Γ(Z, V) c))) = _
  rw [e.commutes]
  change IsLocalRing.residue _ ((Z.presheaf.germ V z hz).hom
    ((π.appLE ⊤ V (by simp)).hom ((Scheme.ΓSpecIso (.of K)).inv.hom c))) =
    IsLocalRing.residue _ ((Z.presheaf.germ (π ⁻¹ᵁ ⊤) z (by simp)).hom
      ((π.app ⊤).hom ((Scheme.ΓSpecIso (.of K)).inv.hom c)))
  congr 1
  change (Z.presheaf.germ V z hz).hom ((Z.presheaf.map (homOfLE _).op).hom
    ((π.app ⊤).hom ((Scheme.ΓSpecIso (.of K)).inv.hom c))) = _
  rw [TopCat.Presheaf.germ_res_apply]

/-- Over a field, the coheight of the prime of a point does not depend on the affine chart. -/
theorem coheight_primeIdealOf_eq [LocallyOfFiniteType π] {V V' : Z.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') {z : Z} (hz : z ∈ V) (hz' : z ∈ V') :
    Order.coheight (hV.primeIdealOf ⟨z, hz⟩) = Order.coheight (hV'.primeIdealOf ⟨z, hz'⟩) := by
  let _ := sectionsAlgebra π V
  let _ := sectionsAlgebra π V'
  let _ := stalkResidueFieldAlgebra π z
  have h1 : Algebra.FiniteType K Γ(Z, V) := sectionsAlgebra_finiteType π hV
  have h2 : Algebra.FiniteType K Γ(Z, V') := sectionsAlgebra_finiteType π hV'
  have e1 := GromovWitten.Algebra.PrimeSpectrum.coheight_eq_toENat_trdeg_residueField (k := K)
    (hV.primeIdealOf ⟨z, hz⟩)
  have e2 := GromovWitten.Algebra.PrimeSpectrum.coheight_eq_toENat_trdeg_residueField (k := K)
    (hV'.primeIdealOf ⟨z, hz'⟩)
  have e3 : Cardinal.toENat (Algebra.trdeg K (hV.primeIdealOf ⟨z, hz⟩).asIdeal.ResidueField) =
      Cardinal.toENat (Algebra.trdeg K (hV'.primeIdealOf ⟨z, hz'⟩).asIdeal.ResidueField) := by
    rw [(chartResidueFieldAlgEquiv π hV hz).trdeg_eq,
      (chartResidueFieldAlgEquiv π hV' hz').trdeg_eq]
  exact e1.trans (e3.trans e2.symm)

/-- Over a field, the height of a point (the dimension of its closure) is the coheight of its
prime in any affine chart containing it. -/
theorem height_eq_coheight_primeIdealOf [LocallyOfFiniteType π] {V : Z.Opens}
    (hV : IsAffineOpen V) {z : Z} (hz : z ∈ V) :
    Order.height z = Order.coheight (hV.primeIdealOf ⟨z, hz⟩) := by
  refine le_antisymm ?_ (coheight_primeIdealOf_le_height hV hz)
  rw [Order.height_le_iff']
  intro p hp
  subst hp
  obtain ⟨V', hV', -, hz', hlen⟩ := exists_affineOpen_length_le_coheight p ⊤ trivial
  rw [coheight_primeIdealOf_eq π hV hV' hz hz']
  exact hlen

end PointDimension

/-! ### The fibre-dimension inequality -/

section FibreDimension

variable {K : Type u} [Field K] {Z W : Scheme.{u}}

/-- A chain of specializations ending at `z` lies in every open neighbourhood of its most
special point; inside an affine chart of `q` its length is bounded by the coheight of the prime
of `z`, computed by the algebraic fibre-dimension formula. -/
theorem height_le_of_fibers (q : Z ⟶ W) (πW : W ⟶ Spec (.of K)) [LocallyOfFiniteType πW]
    [LocallyOfFiniteType (q ≫ πW)] {d e : ℕ} (hW : topologicalKrullDim W ≤ e)
    (hfib : ∀ η : W, topologicalKrullDim (q.fiber η) ≤ d) (z : Z) :
    Order.height z ≤ (d + e : ℕ) := by
  rw [Order.height_le_iff']
  intro p hp
  -- The most special point of the chain and an affine chart around it.
  obtain ⟨_, ⟨U, hU', rfl⟩, hz₀U, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (q p.head)) isOpen_univ
  have hU : IsAffineOpen U := hU'
  obtain ⟨V, hV, hVle, hzV, hlen⟩ :=
    exists_affineOpen_length_le_coheight p (q ⁻¹ᵁ U) (show p.head ∈ q ⁻¹ᵁ U from hz₀U)
  -- The algebraic fibre-dimension formula.
  let P : PrimeSpectrum Γ(Z, V) := hV.primeIdealOf ⟨p.last, hzV⟩
  let _ := (q.appLE U V hVle).hom.toAlgebra
  let _ := sectionsAlgebra (q ≫ πW) V
  let _ := sectionsAlgebra πW U
  have hft₁ : Algebra.FiniteType K Γ(W, U) := sectionsAlgebra_finiteType πW hU
  have hft₂ : Algebra.FiniteType K Γ(Z, V) := sectionsAlgebra_finiteType (q ≫ πW) hV
  have htower : IsScalarTower K Γ(W, U) Γ(Z, V) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have hcomp : (q ≫ πW).appLE ⊤ V (by simp) = πW.appLE ⊤ U (by simp) ≫ q.appLE U V hVle :=
      (Scheme.Hom.appLE_comp_appLE q πW ⊤ U V (by simp) hVle).symm
    change ((q ≫ πW).appLE ⊤ V (by simp)).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom =
      (q.appLE U V hVle).hom.comp
        ((πW.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)
    rw [hcomp, CommRingCat.hom_comp, RingHom.comp_assoc]
  have hformula := GromovWitten.Algebra.coheight_eq_coheight_add_coheight_fiberPrime K Γ(W, U) P
  -- Bound the two terms.
  let Q : PrimeSpectrum Γ(W, U) := PrimeSpectrum.comap (algebraMap Γ(W, U) Γ(Z, V)) P
  have hQle : Order.coheight Q ≤ (e : ℕ∞) := by
    have h1 : ((Order.coheight Q : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim W := by
      refine (Order.coheight_le_krullDim Q).trans ?_
      change ringKrullDim Γ(W, U) ≤ _
      rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
      exact hU.fromSpec.isOpenEmbedding.isInducing.topologicalKrullDim_le
    have h2 := h1.trans hW
    exact_mod_cast h2
  have hP'le : Order.coheight (GromovWitten.Algebra.fiberPrime Γ(W, U) P) ≤ (d : ℕ∞) := by
    have h1 : ((Order.coheight (GromovWitten.Algebra.fiberPrime Γ(W, U) P) : ℕ∞) : WithBot ℕ∞) ≤
        topologicalKrullDim (q.fiber (hU.fromSpec Q)) := by
      refine (Order.coheight_le_krullDim _).trans ?_
      change ringKrullDim (Q.asIdeal.Fiber Γ(Z, V)) ≤ _
      rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
        ← IsHomeomorph.topologicalKrullDim_eq _ (chartFiberHomeomorph q hU hV hVle Q).isHomeomorph]
      exact (fiberMapPrecomp hV.fromSpec q (hU.fromSpec Q)).isOpenEmbedding.isInducing
        |>.topologicalKrullDim_le
    have h2 := h1.trans (hfib _)
    exact_mod_cast h2
  -- Assemble.
  calc (p.length : ℕ∞) ≤ Order.coheight P := hlen
    _ = Order.coheight Q + Order.coheight (GromovWitten.Algebra.fiberPrime Γ(W, U) P) := hformula
    _ ≤ (e : ℕ∞) + (d : ℕ∞) := add_le_add hQle hP'le
    _ = ((d + e : ℕ) : ℕ∞) := by push_cast; ring

/-- The fibre-dimension inequality for schemes locally of finite type over a field: the
dimension of the source is at most the dimension of the target plus the maximal fibre
dimension. -/
theorem topologicalKrullDim_le_of_fibers (q : Z ⟶ W) (πW : W ⟶ Spec (.of K))
    [LocallyOfFiniteType πW] [LocallyOfFiniteType (q ≫ πW)] {d e : ℕ}
    (hW : topologicalKrullDim W ≤ e) (hfib : ∀ η : W, topologicalKrullDim (q.fiber η) ≤ d) :
    topologicalKrullDim Z ≤ (d + e : ℕ) := by
  have hZ : topologicalKrullDim Z = Order.krullDim Z := by
    change Order.krullDim (IrreducibleCloseds Z) = Order.krullDim Z
    exact Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Z))
  rw [hZ, Order.krullDim_eq_iSup_height]
  refine iSup_le fun z ↦ ?_
  have := height_le_of_fibers q πW hW hfib z
  exact_mod_cast this

end FibreDimension

/-! ### Composition of geometric relative dimension bounds -/

namespace GeometricRelativeDimensionLE

/-- Geometric relative dimension bounds add under composition: if `g : X ⟶ Y` has geometric
relative dimension at most `d` and `f : Y ⟶ S` at most `e`, then `g ≫ f` has geometric relative
dimension at most `d + e`.  Every geometric fibre of `g ≫ f` maps to the corresponding geometric
fibre of `f`, and its fibres are geometric fibres of `g`, so the fibre-dimension inequality
applies. -/
theorem comp {X Y S : Scheme.{u}} {d e : ℕ} {g : X ⟶ Y} {f : Y ⟶ S}
    (hg : GeometricRelativeDimensionLE d g) (hf : GeometricRelativeDimensionLE e f) :
    GeometricRelativeDimensionLE (d + e) (g ≫ f) := by
  have := hg.1
  have := hf.1
  refine ⟨inferInstance, ?_⟩
  intro K _ y Z fst snd hsq
  have hWsq : IsPullback (pullback.fst f y) (pullback.snd f y) f y := IsPullback.of_hasPullback f y
  have hW : topologicalKrullDim (pullback f y : Scheme.{u}) ≤ e := hf.2 y _ _ hWsq
  let q : Z ⟶ pullback f y := pullback.lift (fst ≫ g) snd (by rw [Category.assoc, hsq.w])
  have hqπ : q ≫ pullback.snd f y = snd := pullback.lift_snd ..
  have hqfst : q ≫ pullback.fst f y = fst ≫ g := pullback.lift_fst ..
  have hsq' : IsPullback fst (q ≫ pullback.snd f y) (g ≫ f) y := by
    rw [hqπ]
    exact hsq
  have hq : IsPullback fst q g (pullback.fst f y) := IsPullback.of_bot hsq' hqfst.symm hWsq
  have hfib : ∀ η : (pullback f y : Scheme.{u}), topologicalKrullDim (q.fiber η) ≤ d := by
    intro η
    have hsq'' : IsPullback (q.fiberι η ≫ fst) (q.fiberToSpecResidueField η) g
        ((pullback f y : Scheme.{u}).fromSpecResidueField η ≫ pullback.fst f y) :=
      (IsPullback.of_hasPullback q ((pullback f y : Scheme.{u}).fromSpecResidueField η)).paste_horiz
        hq
    exact hg.2 ((pullback f y : Scheme.{u}).fromSpecResidueField η ≫ pullback.fst f y) _ _ hsq''
  have : LocallyOfFiniteType (q ≫ pullback.snd f y) := by
    rw [hqπ]
    exact MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hsq inferInstance
  exact topologicalKrullDim_le_of_fibers q (pullback.snd f y) hW hfib

end GeometricRelativeDimensionLE

end

end GromovWitten.AlgebraicGeometry.Curves
