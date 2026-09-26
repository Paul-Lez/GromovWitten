/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import GromovWitten.AlgebraicGeometry.Stacks.EtaleSlice
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Affine slices of a smooth morphism are étale

`Stacks.EtaleSlice` proves the commutative-algebra core of the Deligne--Mumford slicing
construction (Stacks 06N3): if `B` is standard smooth over `A` of relative dimension `n` and
`b : Fin n → B` cuts out `C`, and the `1 ⊗ d bᵢ` generate `C ⊗[B] Ω[B⁄A]`, then `C` is étale
over `A`.  This file turns that into the shape in which the converse Deligne--Mumford criterion
consumes it, namely étaleness of the *slice morphism*
`pullback.snd g s ≫ t : W ×_U R ⟶ U` of a pair of morphisms `t s : R ⟶ U` along a closed
immersion `g : W ⟶ U`.

## Main results

* `span_tmul_eq_top_of_span_eq_top`: the hypothesis of `EtaleSlice.etale_of_span_eq_top` may be
  checked before passing to the quotient: if the `d bᵢ` generate `Ω[B⁄A]` over `B`, then the
  `1 ⊗ d bᵢ` generate `C ⊗[B] Ω[B⁄A]` over `C`.
* `etale_quotient_of_span_eq_top`: consequently `B ⧸ (b₁, …, bₙ)` is étale over `A` as soon as
  the `d bᵢ` generate `Ω[B⁄A]`; all presentation hypotheses are discharged automatically.
* `exists_notMem_smul_mem_span`: Nakayama's lemma in spreading-out form, `h • M ⊆ span (range y)`
  for some `h ∉ q` whenever the `y i` generate the finitely generated module `M` modulo the
  proper ideal `q`.  This is the step turning generation of `Ω[B⁄A]` at a point into generation
  on a neighbourhood.
* `exists_subfamily_span_sup_smul_eq_top` and `exists_subfamily_notMem_smul_mem_span`: **the
  choice of the slicing functions.**  A spanning set of a free module of rank `n` contains `n`
  elements generating it modulo a maximal ideal `q`, hence (with the previous item) generating it
  after inverting a single element outside `q`.
* `isPullback_specMap_quotient`: the affine base change of a closed immersion.  For a ring map
  `σ : A →+* B` and `I : Ideal A`, the square
  `Spec (B ⧸ I·B) → Spec B`, `Spec (B ⧸ I·B) → Spec (A ⧸ I)`, `Spec B → Spec A`,
  `Spec (A ⧸ I) → Spec A` is cartesian.
* `etale_slice_specMap`: **the affine slice is étale.**  For `t := Spec.map τ` smooth (standard
  smooth of relative dimension `n` in the algebra sense) and `s := Spec.map σ`, and
  `f : Fin n → A` whose `σ`-pullbacks have differentials generating `Ω[B⁄A]`, the slice morphism
  `pullback.snd g s ≫ t` of the closed immersion `g : Spec (A ⧸ (f)) ⟶ Spec A` is étale.

## What is still missing for `EtaleSliceExists`

`etale_slice_specMap` produces one member of the family required by
`GromovWitten.AlgebraicGeometry.EtaleSliceExists`
(`Stacks.DeligneMumfordCriterionFinal`), on an affine chart of `U` over which `R` is affine and
`t` is standard smooth.  Two inputs are not supplied here.

1. *Choosing `f`.*  Unramifiedness of `(t, s) : R ⟶ U ⨯ U` makes
   `EtaleSlice.surjective_mapBaseChange_of_formallyUnramified` apply, so the differentials
   `d (σ a)`, `a : A`, generate `Ω[B⁄A]` over `B`; `exists_subfamily_notMem_smul_mem_span` then
   picks `n` of them generating `Ω[B⁄A]` after inverting one element `h` outside a chosen maximal
   ideal of `B`.  What is *not* formalised here is the bookkeeping that transports this to the
   hypothesis `hspan` of `etale_slice_specMap` over `Localization.Away h`.  Both ingredients are
   available in Mathlib: `Algebra.IsStandardSmoothOfRelativeDimension.localization_away` together
   with `Algebra.IsStandardSmoothOfRelativeDimension.trans` gives
   `IsStandardSmoothOfRelativeDimension n A (Localization.Away h)`, and
   `IsLocalizedModule (Submonoid.powers h) (KaehlerDifferential.map A A B (Localization.Away h))`
   is an instance (used in `Mathlib/RingTheory/Smooth/Locus.lean`), so `Ω[B_h⁄A]` is the
   localisation of `Ω[B⁄A]`; only the routine `span` argument is missing.
2. *Covering `U`.*  Shrinking `Spec B` (i.e. `R`) is harmless for the ring statement but changes
   nothing about the slice, which is determined by `f` alone: the generation condition has to
   hold at *every* point of `s⁻¹(W)`, not only near the chosen point.  Deducing the global
   condition from the pointwise one is where the groupoid structure of `R = U ×_X U` (the
   composition law, which translates the condition at a point of `s⁻¹(W)` to a condition at the
   corresponding point of the unit section) is used in Stacks 06N3, and that translation is not
   formalised in this repository.
-/

open TensorProduct CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace GromovWitten.EtaleSliceLocal

universe u

/-! ## Generation of differentials before and after passing to the quotient -/

section Span

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

omit [Algebra A C] [IsScalarTower A B C] in
/-- **Generation of `Ω[B⁄A]` over `B` implies generation of `C ⊗[B] Ω[B⁄A]` over `C`.**  The
right-hand module is generated by the elements `1 ⊗ m`, and `m ↦ 1 ⊗ m` is `B`-linear, so a
`B`-generating family of `Ω[B⁄A]` gives a `C`-generating family of the base change. -/
theorem span_tmul_eq_top_of_span_eq_top {ι : Type*} (b : ι → B)
    (hspan : Submodule.span B (Set.range fun i ↦ KaehlerDifferential.D A B (b i)) = ⊤) :
    Submodule.span C
      (Set.range fun i ↦ (1 : C) ⊗ₜ[B] KaehlerDifferential.D A B (b i)) = ⊤ := by
  set P : Submodule C (C ⊗[B] Ω[B⁄A]) :=
    Submodule.span C (Set.range fun i ↦ (1 : C) ⊗ₜ[B] KaehlerDifferential.D A B (b i))
  have hmem : ∀ m : Ω[B⁄A], (1 : C) ⊗ₜ[B] m ∈ P := by
    have hle : (⊤ : Submodule B Ω[B⁄A]) ≤
        Submodule.comap (TensorProduct.mk B C Ω[B⁄A] 1) (P.restrictScalars B) := by
      rw [← hspan, Submodule.span_le]
      rintro x ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    intro m
    exact hle (Submodule.mem_top (x := m))
  have hall : ∀ x : C ⊗[B] Ω[B⁄A], x ∈ P := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul c m =>
        have hc : c ⊗ₜ[B] m = c • ((1 : C) ⊗ₜ[B] m) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hc]
        exact Submodule.smul_mem _ _ (hmem m)
    | add x y hx hy => exact add_mem hx hy
  exact top_unique fun x _ ↦ hall x

/-- **Étale slicing with the generation condition checked upstairs.**  The version of
`EtaleSlice.etale_of_span_eq_top_of_isStandardSmooth` whose generation hypothesis is stated in
`Ω[B⁄A]` rather than in `C ⊗[B] Ω[B⁄A]`. -/
theorem etale_of_span_eq_top_of_isStandardSmooth' (n : ℕ) [Nontrivial B]
    [Algebra.IsStandardSmoothOfRelativeDimension n A B] [Algebra.FinitePresentation A C]
    (b : Fin n → B) (hsurj : Function.Surjective (algebraMap B C))
    (hker : Ideal.span (Set.range b) = RingHom.ker (algebraMap B C))
    (hspan : Submodule.span B (Set.range fun i ↦ KaehlerDifferential.D A B (b i)) = ⊤) :
    Algebra.Etale A C :=
  EtaleSlice.etale_of_span_eq_top_of_isStandardSmooth n b hsurj hker
    (span_tmul_eq_top_of_span_eq_top b hspan)

end Span

section Quotient

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The quotient of a finitely presented algebra by a finitely generated ideal is finitely
presented. -/
theorem finitePresentation_quotient_span [Algebra.FinitePresentation A B] {n : ℕ}
    (b : Fin n → B) :
    Algebra.FinitePresentation A (B ⧸ Ideal.span (Set.range b)) :=
  Algebra.FinitePresentation.quotient
    (Submodule.fg_span (Set.finite_range b))

/-- **Étale slicing, quotient form.**  If `B` is standard smooth over `A` of relative
dimension `n` and the differentials of `b : Fin n → B` generate `Ω[B⁄A]`, then the quotient of
`B` by the ideal generated by the `b i` is étale over `A`. -/
theorem etale_quotient_of_span_eq_top (n : ℕ) [Nontrivial B]
    [Algebra.IsStandardSmoothOfRelativeDimension n A B] (b : Fin n → B)
    (hspan : Submodule.span B (Set.range fun i ↦ KaehlerDifferential.D A B (b i)) = ⊤) :
    Algebra.Etale A (B ⧸ Ideal.span (Set.range b)) := by
  have _ : Algebra.IsStandardSmooth A B :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have hfp : Algebra.FinitePresentation A B :=
    Algebra.IsStandardSmooth.finitePresentation
  have _ : Algebra.FinitePresentation A (B ⧸ Ideal.span (Set.range b)) :=
    finitePresentation_quotient_span b
  refine etale_of_span_eq_top_of_isStandardSmooth' n b Ideal.Quotient.mk_surjective ?_ hspan
  exact (Ideal.mk_ker (I := Ideal.span (Set.range b))).symm

end Quotient

/-! ## Nakayama: from generation modulo a prime to generation after inverting one element -/

section Nakayama

variable {B : Type u} [CommRing B]

/-- **Nakayama's lemma, in spreading-out form.**  Let `M` be a finitely generated `B`-module
generated by a family `y` *modulo* a proper ideal `q`.  Then there is an element `h ∉ q` with
`h • M ⊆ span (range y)`, i.e. the `y i` generate `M` after inverting `h`.

This is the step of Stacks 06N3 which turns a choice of `n` slicing functions whose differentials
generate the relative cotangent module at one point into a choice generating it on a
neighbourhood; combined with `etale_slice_specMap` it is what makes the slice étale near the
chosen point. -/
theorem exists_notMem_smul_mem_span {M : Type u} [AddCommGroup M] [Module B M]
    [Module.Finite B M] {ι : Type*} (y : ι → M) (q : Ideal B) (hq : q ≠ ⊤)
    (hgen : Submodule.span B (Set.range y) ⊔ q • (⊤ : Submodule B M) = ⊤) :
    ∃ h : B, h ∉ q ∧ ∀ m : M, h • m ∈ Submodule.span B (Set.range y) := by
  set N := Submodule.span B (Set.range y) with hN
  have htop : (⊤ : Submodule B (M ⧸ N)) ≤ q • (⊤ : Submodule B (M ⧸ N)) := by
    have h1 : Submodule.map N.mkQ (q • (⊤ : Submodule B M)) = ⊤ :=
      (Submodule.map_mkQ_eq_top N _).2 hgen
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h1
    exact h1.ge
  obtain ⟨r, hr, hr'⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul q
    (⊤ : Submodule B (M ⧸ N)) Module.Finite.fg_top htop
  refine ⟨r, fun hrq ↦ hq ((Ideal.eq_top_iff_one q).2 ?_), fun m ↦ ?_⟩
  · simpa using q.sub_mem hrq hr
  · have hz := hr' (N.mkQ m) Submodule.mem_top
    rw [← map_smul] at hz
    exact (Submodule.Quotient.mk_eq_zero N).1 hz

/-- **Extracting `rank`-many elements from a spanning set, modulo a maximal ideal.**  Let `M` be
free of rank `n` over `B` with basis `bas`, let `S` be a `B`-spanning subset of `M` and let `q` be
a maximal ideal of `B`.  Then `n` elements of `S` already generate `M` modulo `q`: their images
form a basis of the `n`-dimensional `B ⧸ q`-vector space `M ⧸ q·M`.

Together with `exists_notMem_smul_mem_span` this is the choice of the `n` slicing functions of
Stacks 06N3: apply it to `M := Ω[B⁄A]` (free of rank `n` because `B` is standard smooth over `A`
of relative dimension `n`) and to the spanning set `S = {d (σ a) | a : A}` produced from the
unramified diagonal by `EtaleSlice.surjective_mapBaseChange_of_formallyUnramified`. -/
theorem exists_subfamily_span_sup_smul_eq_top {M : Type u} [AddCommGroup M] [Module B M]
    {n : ℕ} (bas : Module.Basis (Fin n) B M) (S : Set M) (hS : Submodule.span B S = ⊤)
    (q : Ideal B) [q.IsMaximal] :
    ∃ y : Fin n → M, (∀ i, y i ∈ S) ∧
      Submodule.span B (Set.range y) ⊔ q • (⊤ : Submodule B M) = ⊤ := by
  classical
  let _ : Field (B ⧸ q) := Ideal.Quotient.field q
  have hsur : Function.Surjective (algebraMap B (B ⧸ q)) := Ideal.Quotient.mk_surjective
  have _ : Module.Finite B M := Module.Finite.of_basis bas
  have e : (B ⧸ q) ⊗[B] M ≃ₗ[B ⧸ q] M ⧸ q • (⊤ : Submodule B M) :=
    (TensorProduct.quotTensorEquivQuotSMul M q).extendScalarsOfSurjective hsur
  have basQ : Module.Basis (Fin n) (B ⧸ q) (M ⧸ q • (⊤ : Submodule B M)) :=
    (Algebra.TensorProduct.basis (B ⧸ q) bas).map e
  have hrank : Module.finrank (B ⧸ q) (M ⧸ q • (⊤ : Submodule B M)) = n := by
    rw [Module.finrank_eq_card_basis basQ, Fintype.card_fin]
  have _ : Module.Finite (B ⧸ q) (M ⧸ q • (⊤ : Submodule B M)) := Module.Finite.of_basis basQ
  have hiff : ∀ X : Set (M ⧸ q • (⊤ : Submodule B M)),
      Submodule.span B X = ⊤ ↔ Submodule.span (B ⧸ q) X = ⊤ := by
    intro X
    rw [← Submodule.restrictScalars_span B (B ⧸ q) hsur X,
      Submodule.restrictScalars_eq_top_iff]
  have hSB : Submodule.span B ((q • (⊤ : Submodule B M)).mkQ '' S) = ⊤ := by
    rw [← Submodule.map_span, hS, Submodule.map_top, Submodule.range_mkQ]
  obtain ⟨t, hts, hspant, hindep⟩ :=
    exists_linearIndependent (B ⧸ q) ((q • (⊤ : Submodule B M)).mkQ '' S)
  have htop : Submodule.span (B ⧸ q) t = ⊤ := hspant.trans ((hiff _).1 hSB)
  have _ : Fintype t := hindep.setFinite.fintype
  have hcard : Fintype.card t = n := by
    have hb : Module.Basis t (B ⧸ q) (M ⧸ q • (⊤ : Submodule B M)) :=
      Module.Basis.mk hindep (le_of_eq (by rw [Subtype.range_coe]; exact htop.symm))
    rw [← hrank, Module.finrank_eq_card_basis hb]
  have hsel : ∀ i : Fin n, ∃ m : M, m ∈ S ∧ (q • (⊤ : Submodule B M)).mkQ m =
      (((Fintype.equivFinOfCardEq hcard).symm i : t) : M ⧸ q • (⊤ : Submodule B M)) :=
    fun i ↦ hts ((Fintype.equivFinOfCardEq hcard).symm i).2
  choose y hyS hy using hsel
  refine ⟨y, hyS, ?_⟩
  have hrange : (Set.range fun i ↦ (q • (⊤ : Submodule B M)).mkQ (y i)) = t := by
    rw [show (fun i ↦ (q • (⊤ : Submodule B M)).mkQ (y i)) =
      (Subtype.val ∘ fun i ↦ (Fintype.equivFinOfCardEq hcard).symm i) from funext hy,
      Set.range_comp, Equiv.range_eq_univ, Set.image_univ, Subtype.range_coe]
  have h2 : Submodule.span B (Set.range fun i ↦ (q • (⊤ : Submodule B M)).mkQ (y i)) = ⊤ :=
    (hiff _).2 (by rw [hrange]; exact htop)
  have h3 : Submodule.map (q • (⊤ : Submodule B M)).mkQ (Submodule.span B (Set.range y)) = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact h2
  rw [sup_comm]
  exact (Submodule.map_mkQ_eq_top _ _).1 h3

/-- **The choice of the slicing functions of Stacks 06N3.**  Let `M` be free of rank `n` over `B`
with basis `bas`, let `S` be a `B`-spanning subset of `M` and let `q` be a maximal ideal of `B`.
Then there are `n` elements of `S` and an element `h ∉ q` with `h • M ⊆ span (range y)`, i.e. the
`y i` generate `M` after inverting `h`.

Applied to `M := Ω[B⁄A]` (free of rank `n` since `B` is standard smooth over `A` of relative
dimension `n`) and to `S := {d (σ a) | a : A}` (which spans by
`EtaleSlice.surjective_mapBaseChange_of_formallyUnramified`, the unramified-diagonal input), this
chooses the `n` functions on `U` whose slice is étale near the chosen point of `R`. -/
theorem exists_subfamily_notMem_smul_mem_span {M : Type u} [AddCommGroup M] [Module B M]
    {n : ℕ} (bas : Module.Basis (Fin n) B M) (S : Set M) (hS : Submodule.span B S = ⊤)
    (q : Ideal B) [hq : q.IsMaximal] :
    ∃ (y : Fin n → M) (h : B), (∀ i, y i ∈ S) ∧ h ∉ q ∧
      ∀ m : M, h • m ∈ Submodule.span B (Set.range y) := by
  obtain ⟨y, hyS, hgen⟩ := exists_subfamily_span_sup_smul_eq_top bas S hS q
  have _ : Module.Finite B M := Module.Finite.of_basis bas
  obtain ⟨h, hh, hh'⟩ := exists_notMem_smul_mem_span y q hq.ne_top hgen
  exact ⟨y, h, hyS, hh, hh'⟩

end Nakayama

/-! ## The affine slice morphism -/

section Affine

variable {A B : Type u} [CommRing A] [CommRing B]

open Algebra.TensorProduct in
/-- **Affine base change of a closed immersion** (algebra-instance form; use
`isPullback_specMap_quotient`). -/
theorem isPullback_specMap_quotient' [Algebra A B] (I : Ideal A) :
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap A B)))))
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map (algebraMap A B))
        (algebraMap A B) Ideal.le_comap_map)))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  have hleft : (quotIdealMapEquivTensorQuot B I).symm.toRingHom.comp includeLeftRingHom =
      Ideal.Quotient.mk (I.map (algebraMap A B)) := by
    refine RingHom.ext fun b ↦ ?_
    change (quotIdealMapEquivTensorQuot B I).symm (b ⊗ₜ[A] (1 : A ⧸ I)) = _
    refine (AlgEquiv.symm_apply_eq _).2 ?_
    exact (quotIdealMapEquivTensorQuot_mk B I b).symm
  have hright : (quotIdealMapEquivTensorQuot B I).symm.toRingHom.comp
      (RingHomClass.toRingHom (includeRight : (A ⧸ I) →ₐ[A] B ⊗[A] (A ⧸ I))) =
      Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ ?_)
    change (quotIdealMapEquivTensorQuot B I).symm
      ((1 : B) ⊗ₜ[A] (Ideal.Quotient.mk I a)) = _
    refine (AlgEquiv.symm_apply_eq _).2 ?_
    change (1 : B) ⊗ₜ[A] (Ideal.Quotient.mk I a) =
      (quotIdealMapEquivTensorQuot B I) (Ideal.Quotient.mk (I.map (algebraMap A B))
        (algebraMap A B a))
    rw [quotIdealMapEquivTensorQuot_mk B I (algebraMap A B a)]
    change (1 : B) ⊗ₜ[A] (algebraMap A (A ⧸ I) a) = (algebraMap A B a) ⊗ₜ[A] (1 : A ⧸ I)
    rw [Algebra.algebraMap_eq_smul_one (R := A) (A := A ⧸ I) a,
      Algebra.algebraMap_eq_smul_one (R := A) (A := B) a, TensorProduct.smul_tmul]
  have hiso : IsIso (Spec.map (CommRingCat.ofHom
      (quotIdealMapEquivTensorQuot B I).symm.toRingHom)) := by
    rw [isIso_SpecMap_iff]
    exact (quotIdealMapEquivTensorQuot B I).symm.bijective
  have hcomm : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap A B)))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map (algebraMap A B))
        (algebraMap A B) Ideal.le_comap_map)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
  refine IsPullback.of_iso_pullback ⟨hcomm⟩
    (asIso (Spec.map (CommRingCat.ofHom
        (quotIdealMapEquivTensorQuot B I).symm.toRingHom)) ≪≫
      (pullbackSpecIso A B (A ⧸ I)).symm) ?_ ?_
  · rw [Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc, pullbackSpecIso_inv_fst,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, hleft]
  · rw [Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc, pullbackSpecIso_inv_snd,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, hright]

/-- **Affine base change of a closed immersion.**  For a ring map `σ : A →+* B` and an ideal
`I : Ideal A`, the closed subscheme `Spec (A ⧸ I)` of `Spec A` pulls back along
`Spec σ : Spec B ⟶ Spec A` to the closed subscheme `Spec (B ⧸ I·B)` of `Spec B`.  This is the
affine case of "the slice `s⁻¹(W)` of a closed subscheme `W ⊆ U` is cut out by the pullbacks of
the equations of `W`". -/
theorem isPullback_specMap_quotient (σ : A →+* B) (I : Ideal A) :
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map σ))))
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map σ) σ Ideal.le_comap_map)))
      (Spec.map (CommRingCat.ofHom σ))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  @isPullback_specMap_quotient' A B _ _ σ.toAlgebra I

/-- A morphism of affine schemes coming from an étale algebra is étale. -/
theorem etale_specMap_of_etale {C : Type u} [CommRing C] [Algebra A C]
    (h : Algebra.Etale A C) :
    _root_.AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom (algebraMap A C))) := by
  rw [HasRingHomProperty.Spec_iff (P := @_root_.AlgebraicGeometry.Etale)]
  exact RingHom.etale_algebraMap.mpr h

/-- **The affine slice of a smooth morphism is étale.**  Let `t := Spec (algebraMap A B)` be
standard smooth of relative dimension `n`, let `s := Spec σ` be a second morphism
`Spec B ⟶ Spec A`, and let `W = Spec (A ⧸ I)` be a closed subscheme of `Spec A` whose ideal
pulls back under `σ` to an ideal generated by `n` elements `b` whose differentials generate
`Ω[B⁄A]`.  Then the slice morphism `pullback.snd g s ≫ t : W ×_{Spec A} Spec B ⟶ Spec A` is
étale.  This is one member of the family required by
`GromovWitten.AlgebraicGeometry.EtaleSliceExists`. -/
theorem etale_slice_specMap [Algebra A B] (n : ℕ) [Nontrivial B]
    [Algebra.IsStandardSmoothOfRelativeDimension n A B] (σ : A →+* B) (I : Ideal A)
    (b : Fin n → B) (hI : I.map σ = Ideal.span (Set.range b))
    (hspan : Submodule.span B
      (Set.range fun i ↦ KaehlerDifferential.D A B (b i)) = ⊤) :
    _root_.AlgebraicGeometry.Etale
      (pullback.snd (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
        (Spec.map (CommRingCat.ofHom σ)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  have hsq := (isPullback_specMap_quotient σ I).flip
  have hEt : _root_.AlgebraicGeometry.Etale
      (Spec.map (CommRingCat.ofHom (algebraMap A (B ⧸ I.map σ)))) := by
    rw [hI]
    exact etale_specMap_of_etale (etale_quotient_of_span_eq_top n b hspan)
  have hkey : _root_.AlgebraicGeometry.Etale
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map σ))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact hEt
  have _hres : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [← MorphismProperty.cancel_left_of_respectsIso
    (@_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) hsq.isoPullback.hom _,
    ← Category.assoc, hsq.isoPullback_hom_snd]
  exact hkey

end Affine

end GromovWitten.EtaleSliceLocal
