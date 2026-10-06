/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ClassifyingStackChow
import GromovWitten.AlgebraicGeometry.IntersectionTheory.AtlasIndependence
import GromovWitten.AlgebraicGeometry.IntersectionTheory.CycleGluing
import GromovWitten.AlgebraicGeometry.Stacks.ConstantGroup
import GromovWitten.AlgebraicGeometry.Sites.StackSiteContinuity
import Mathlib.RingTheory.TensorProduct.Pi

/-!
# The self-overlap of the atlas `Spec k → [Spec k / Γ]`

Let `k` be a field and `Γ` a finite group, viewed as the constant finite group scheme
`constantGroup Γ = Spec (Γ → ℤ)`.  The quotient stack `[Spec k / Γ]` of the trivial action of
`Γ` on `Spec k` (the classifying stack `BΓ_k`) has the atlas chart `Spec k → [Spec k / Γ]`
(`constantAtlasChart`, étale and surjective).  This file identifies the self-overlap
`Spec k ×_{[Spec k/Γ]} Spec k` of that chart with `Spec (Γ → k) = Γ × Spec k`, both legs being
the structure map, and deduces that the Vistoli Chow groups of the chart groupoid are those of
the standalone groupoid `ClassifyingStackChow.constantGroupoid k Γ` of
`IntersectionTheory/ClassifyingStackChow.lean`, and that the chart groupoid has degree `|Γ|`.

The route: the tautological object of the atlas chart is the trivial torsor
`Γ × Spec k → Spec k`; `Spec (Γ → k)` is the scheme product `Spec (Γ → ℤ) × Spec k`
(`k ⊗_ℤ (Γ → ℤ) ≅ (Γ → k)`), so it represents the trivial torsor
(`constantTautRepresentation`), and `ActionTorsor.atlasPullbackPresentation` turns this
representation into a pullback presentation of the chart (`constantSelfOverlap`).  Its second
leg is computed by the general lemma `atlasPullbackPresentation_snd_of_smul_eq_snd`, valid for
any action whose action map is the second projection.  Uniqueness of pullback presentations
(`Sites.SiteChart.presentationIso`, already in the repository) compares the explicit
presentation with the internally chosen self-overlap `StackChart.selfOverlapScheme`.

## Main results

* `constantAtlasChart k Γ`: the atlas chart `Spec k → [Spec k / Γ]` (its scheme is reducibly
  `Spec k`; it equals `ActionTorsor.atlasChart _ _ (Spec k) rfl` by `rfl`), with
  `constantAtlasChart_isEtaleSurjective`.
* `isPullback_constantArrows`, `constantArrowsIsProduct`: `Spec (Γ → k)` with the two
  projections `constantArrowsToGroup`, `constantProjection` is the product `Spec (Γ → ℤ) × Spec k`.
* `constantTrivialTorsorIso`, `constantTautRepresentation`: `Spec (Γ → k)` represents the
  trivial torsor `Γ × Spec k`, i.e. the tautological object of the atlas chart.
* `atlasPullbackPresentation_snd_of_smul_eq_snd`: for an action with action map the second
  projection, the second leg of the atlas-chart pullback presentation attached to a
  representation `R` of the tautological torsor is `R.toBase`.
* `constantSelfOverlap`: the explicit pullback presentation of the self-overlap of the atlas
  chart with space `Spec (Γ → k)` and both legs `constantProjection k Γ`
  (`constantSelfOverlap_space`, `constantSelfOverlap_fst`, `constantSelfOverlap_snd`).
* `Sites.SiteChart.presentationIso_hom_snd`: the canonical isomorphism of two pullback
  presentations is compatible with the chart legs (the first-leg version already existed).
* `selfOverlapIso`: the chosen self-overlap scheme `(constantAtlasChart k Γ).selfOverlapScheme _`
  is isomorphic to `Spec (Γ → k)`, compatibly with both legs (`selfOverlapIso_hom_fst`,
  `selfOverlapIso_hom_snd`).
* `constantChartGroupoid k Γ`: the chart groupoid `StackChart.etaleGroupoid` of the atlas (with
  structure map `𝟙 (Spec k)`), with `constantChartGroupoid_good`.
* `constantMoritaMap`: the isomorphism of groupoids `constantGroupoid k Γ ≅ constantChartGroupoid
  k Γ` as a `MoritaMap`, and `vistoliChowEquivConstant`: the induced isomorphism
  `(constantAtlasChart k Γ).vistoliChow _ (𝟙 _) i ≃ₗ[ℚ] (constantGroupoid k Γ).vistoliChow i`.
* `IntersectionTheory.map_fundamentalCycle_of_iso`,
  `IntersectionTheory.map_fundamentalCycle_eq_of_iso_comp`: pushforward of fundamental cycles
  along isomorphisms; `constantChartGroupoid_isOfDegree`: the chart groupoid has degree `|Γ|`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CartesianMonoidalCategory
open scoped MonoidalCategory

namespace GromovWitten.AlgebraicGeometry

/-! ## Pushforward of fundamental cycles along isomorphisms -/

namespace IntersectionTheory

/-- Pushforward along an isomorphism of locally Noetherian schemes carries the fundamental cycle
to the fundamental cycle, for weight functions compatible with the isomorphism. -/
theorem map_fundamentalCycle_of_iso {W W' : Scheme.{u}} [IsLocallyNoetherian W]
    [IsLocallyNoetherian W'] (θ : W' ≅ W) (wW : W → ℤ) (wW' : W' → ℤ)
    (hw : ∀ x, wW' x = wW (θ.hom.base x)) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map θ.hom wW' wW W'.fundamentalCycle =
      W.fundamentalCycle := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext y
  change ∑ᶠ x ∈ θ.hom.base ⁻¹' {y}, W'.fundamentalCycle x *
    ((_root_.AlgebraicGeometry.AlgebraicCycle.mapCoeff θ.hom wW' wW x : ℕ) : ℚ) = _
  have hpre : θ.hom.base ⁻¹' {y} = {θ.inv.base y} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro rfl
      change x = (θ.hom ≫ θ.inv).base x
      rw [θ.hom_inv_id]
      rfl
    · rintro rfl
      change (θ.inv ≫ θ.hom).base y = y
      rw [θ.inv_hom_id]
      rfl
  rw [hpre, finsum_mem_singleton]
  have hfun : W'.fundamentalCycle (θ.inv.base y) = W.fundamentalCycle y := by
    have h := AlgebraicCycle.pullbackOpen_fundamentalCycle θ.inv
    have h' := congrArg (fun c : AlgebraicCycle W ℚ ↦ c y) h
    simpa [AlgebraicCycle.pullbackOpen_apply] using h'
  rw [hfun]
  have hcoeff :
      _root_.AlgebraicGeometry.AlgebraicCycle.mapCoeff θ.hom wW' wW (θ.inv.base y) = 1 := by
    simp [_root_.AlgebraicGeometry.AlgebraicCycle.mapCoeff, hw,
      ProperPushforwardDivisor.residueDegree_eq_one_of_isOpenImmersion]
  rw [hcoeff]
  simp

/-- The pushforward of the fundamental cycle along a quasi-compact map is invariant under
precomposition with an isomorphism of the source (for compatible weights). -/
theorem map_fundamentalCycle_eq_of_iso_comp {B W W' : Scheme.{u}} [IsLocallyNoetherian W]
    [IsLocallyNoetherian W'] (s : W ⟶ B) (s' : W' ⟶ B) [QuasiCompact s] [QuasiCompact s']
    (θ : W' ≅ W) (hθ : θ.hom ≫ s = s') (wB : B → ℤ) (wW : W → ℤ) (wW' : W' → ℤ)
    (hw : ∀ x, wW' x = wW (θ.hom.base x)) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map s' wW' wB W'.fundamentalCycle =
      _root_.AlgebraicGeometry.AlgebraicCycle.map s wW wB W.fundamentalCycle := by
  subst hθ
  rw [← AlgebraicCycle.map_comp_of_between θ.hom s wW' wW wB (fun x _ ↦ hw x),
    map_fundamentalCycle_of_iso θ wW wW' hw]

end IntersectionTheory

/-! ## Uniqueness of pullback presentations: the second leg -/

namespace Sites.SiteChart

variable {X : FppfStack.{u}} (A : StackChart X)

/-- The canonical isomorphism of two pullback presentations of the same base change is
compatible with the chart legs (companion of `presentationIso_hom_fst`). -/
theorem presentationIso_hom_snd {T : Scheme.{u}} {x : StackFiber X T}
    (p q : A.PullbackPresentation T x) :
    (presentationIso A p q).hom ≫ p.snd = q.snd :=
  p.lift_snd _ _ _

end Sites.SiteChart

/-! ## The second leg of the atlas-chart presentation for a trivial action -/

section TrivialSnd

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G} (X₀ : Scheme.{u})

/-- For an action of `G` on the algebraic space of a scheme `X₀` whose action map is the second
projection `G × X₀ → X₀` (a trivial action), the second leg of the pullback presentation
`ActionTorsor.atlasPullbackPresentation` of the atlas chart attached to a representation `R` of
the tautological torsor `G × X₀ → X₀` is the structure map `R.toBase` of the representation. -/
theorem atlasPullbackPresentation_snd_of_smul_eq_snd
    (h : U.space = AlgebraicSpace.ofScheme.obj X₀)
    (hsmul : ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf) = snd _ _)
    (R : TorsorRepresentation (ActionTorsor.atlasChart G U X₀ h).tautObj.toFppfTorsor) :
    (ActionTorsor.atlasPullbackPresentation X₀ h _ R).snd = R.toBase := by
  have := ActionTorsor.isIso_atlasChart_eqToHom h
  apply fppfYoneda.map_injective
  refine (fppfYoneda.map_preimage _).trans ?_
  change R.iso.hom ≫ (ConeQuotient.trivialWithPoint (fppfJ.yonedaEquiv.symm
    ((eqToHom (congrArg (fun Y : AlgebraicSpace.{u} => Y.toSheaf) h).symm).hom.app
      (Opposite.op X₀) (𝟙 X₀)))).target ≫
    inv (eqToHom (congrArg (fun Y : AlgebraicSpace.{u} => Y.toSheaf) h).symm) = _
  have ht : fppfJ.yonedaEquiv.symm
      ((eqToHom (congrArg (fun Y : AlgebraicSpace.{u} => Y.toSheaf) h).symm).hom.app
        (Opposite.op X₀) (𝟙 X₀)) =
      eqToHom (congrArg (fun Y : AlgebraicSpace.{u} => Y.toSheaf) h).symm :=
    (fppfYonedaEquiv_symm_app_eq_map_comp _ (𝟙 X₀)).trans
      (by erw [CategoryTheory.Functor.map_id, Category.id_comp])
  rw [ConeQuotient.trivialWithPoint_target, hsmul, whiskerLeft_snd]
  erw [ht, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  exact R.iso_hom_projection

/-- For the trivial action of `G` on the algebraic space of a scheme `X₀`, the second leg of
the pullback presentation of the atlas chart attached to a representation `R` of the
tautological torsor is `R.toBase`. -/
theorem atlasPullbackPresentation_trivial_snd
    (R : TorsorRepresentation (ActionTorsor.atlasChart G
      (AlgebraicSpaceAction.trivial G (AlgebraicSpace.ofScheme.obj X₀)) X₀
        rfl).tautObj.toFppfTorsor) :
    (ActionTorsor.atlasPullbackPresentation X₀ rfl _ R).snd = R.toBase :=
  atlasPullbackPresentation_snd_of_smul_eq_snd X₀ rfl rfl R

end TrivialSnd

open IntersectionTheory IntersectionTheory.ClassifyingStackChow
  IntersectionTheory.ProperPushforwardDivisor

attribute [local instance] torsorZuAlgebra Fintype.ofFinite

/-! ## `Spec (Γ → k)` as the product `Γ × Spec k` -/

section Product

variable (k : Type u) [Field k] (Γ : Type u) [Finite Γ] [DecidableEq Γ]

/-- The ring map `(Γ → TorsorZu) →+* (Γ → k)`, componentwise the structure map of `k`. -/
noncomputable def constantRingToArrows : ConstantRing Γ →+* (Γ → k) :=
  RingHom.pi fun γ => (algebraMap TorsorZu.{u} k).comp (Pi.evalRingHom _ γ)

/-- The projection `Spec (Γ → k) ⟶ Spec (Γ → TorsorZu) = Γ` to the constant group scheme. -/
noncomputable def constantArrowsToGroup :
    constantArrows k Γ ⟶ Spec (CommRingCat.of (ConstantRing Γ)) :=
  Spec.map (CommRingCat.ofHom (constantRingToArrows k Γ))

/-- The `TorsorZu`-algebra isomorphism `k ⊗ (Γ → TorsorZu) ≃ (Γ → k)`. -/
noncomputable def constantTensorEquiv :
    TensorProduct TorsorZu.{u} k (ConstantRing Γ) ≃ₐ[TorsorZu.{u}] (Γ → k) :=
  Algebra.TensorProduct.piScalarRight TorsorZu.{u} TorsorZu.{u} k Γ

/-- `constantTensorEquiv` on pure tensors: `x ⊗ y ↦ (γ ↦ y γ • x)`. -/
theorem constantTensorEquiv_tmul (x : k) (y : ConstantRing Γ) :
    constantTensorEquiv k Γ (TensorProduct.tmul _ x y) = fun γ => y γ • x :=
  rfl

/-- `Spec (Γ → k) ≅ Spec (k ⊗ (Γ → TorsorZu))`, the `Spec` of `constantTensorEquiv`. -/
noncomputable def constantArrowsIsoSpecTensor :
    constantArrows k Γ ≅ Spec (CommRingCat.of (TensorProduct TorsorZu.{u} k (ConstantRing Γ))) :=
  Scheme.Spec.mapIso (constantTensorEquiv k Γ).toRingEquiv.toCommRingCatIso.op

/-- The forward map of `constantArrowsIsoSpecTensor` is `Spec.map` of `constantTensorEquiv`. -/
theorem constantArrowsIsoSpecTensor_hom :
    (constantArrowsIsoSpecTensor k Γ).hom =
      Spec.map (CommRingCat.ofHom (constantTensorEquiv k Γ).toRingEquiv.toRingHom) := rfl

omit [DecidableEq Γ] in
/-- **`Spec (Γ → k)` is the fibre product `Spec k ×_{Spec ℤ} Spec (Γ → ℤ)`**, with projections
`constantProjection k Γ` and `constantArrowsToGroup k Γ`. -/
theorem isPullback_constantArrows :
    IsPullback (constantProjection k Γ) (constantArrowsToGroup k Γ)
      (Spec.map (CommRingCat.ofHom (algebraMap TorsorZu.{u} k)))
      (Spec.map (CommRingCat.ofHom (algebraMap TorsorZu.{u} (ConstantRing Γ)))) := by
  classical
  refine IsPullback.of_iso_pullback ⟨?_⟩
    (constantArrowsIsoSpecTensor k Γ ≪≫ (pullbackSpecIso TorsorZu.{u} k (ConstantRing Γ)).symm)
    ?_ ?_
  · rw [constantProjection, constantArrowsToGroup, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
  · rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, pullbackSpecIso_inv_fst,
      constantArrowsIsoSpecTensor_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    change _ = Spec.map (CommRingCat.ofHom (algebraMap k (Γ → k)))
    congr 2
    refine RingHom.ext fun c => ?_
    change constantTensorEquiv k Γ (TensorProduct.tmul _ c 1) = _
    rw [constantTensorEquiv_tmul]
    funext γ
    simp
  · rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, pullbackSpecIso_inv_snd,
      constantArrowsIsoSpecTensor_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    change _ = Spec.map (CommRingCat.ofHom (constantRingToArrows k Γ))
    congr 2
    refine RingHom.ext fun y => ?_
    change constantTensorEquiv k Γ (TensorProduct.tmul _ 1 y) = _
    rw [constantTensorEquiv_tmul]
    funext γ
    simp [constantRingToArrows, Algebra.smul_def]

/-- `Spec (Γ → k)` with the projections `constantArrowsToGroup`, `constantProjection` is the
scheme product `Spec (Γ → TorsorZu) × Spec k` (`Spec TorsorZu` being terminal). -/
noncomputable def constantArrowsIsProduct :
    IsLimit (BinaryFan.mk (constantArrowsToGroup k Γ) (constantProjection k Γ)) :=
  isProductOfIsTerminalIsPullback _ _ _ _ specULiftZIsTerminal
    (isPullback_constantArrows k Γ).flip.isLimit

/-- The fppf sheaf of `Spec (Γ → k)` is the product of the fppf sheaves of
`Spec (Γ → TorsorZu)` and `Spec k`. -/
noncomputable def constantArrowsSheafIsProduct :
    IsLimit (BinaryFan.mk (fppfYoneda.map (constantArrowsToGroup k Γ))
      (fppfYoneda.map (constantProjection k Γ))) :=
  isLimitMapConeBinaryFanEquiv fppfYoneda _ _
    (isLimitOfPreserves fppfYoneda (constantArrowsIsProduct k Γ))

end Product

/-! ## The atlas chart and the representation of its tautological torsor -/

variable (k : Type u) [Field k] (Γ : Type u) [Group Γ] [Finite Γ] [DecidableEq Γ]

/-- The trivial action of the constant finite group scheme `Γ` on `Spec k`; its quotient stack
`ActionTorsor.quotientStack (constantGroup Γ) (constantTrivialAction k Γ)` is `[Spec k / Γ]`. -/
noncomputable abbrev constantTrivialAction : AlgebraicSpaceAction (constantGroup Γ) :=
  AlgebraicSpaceAction.trivial (constantGroup Γ)
    (AlgebraicSpace.ofScheme.obj (Spec (CommRingCat.of k)))

/-- **The atlas chart `Spec k → [Spec k / Γ]`**: the atlas chart `ActionTorsor.atlasChart` of
the quotient stack of the trivial action, repackaged so that its scheme is reducibly `Spec k`
(it is equal to `ActionTorsor.atlasChart _ _ (Spec k) rfl` by `rfl`,
`constantAtlasChart_eq_atlasChart`). -/
noncomputable abbrev constantAtlasChart :
    StackChart (ActionTorsor.quotientStack (constantGroup Γ) (constantTrivialAction k Γ)) where
  scheme := Spec (CommRingCat.of k)
  map := (ActionTorsor.atlasChart (constantGroup Γ) (constantTrivialAction k Γ)
    (Spec (CommRingCat.of k)) rfl).map

/-- The atlas chart is `ActionTorsor.atlasChart` of the trivial action (by `rfl`). -/
theorem constantAtlasChart_eq_atlasChart :
    constantAtlasChart k Γ = ActionTorsor.atlasChart (constantGroup Γ) (constantTrivialAction k Γ)
      (Spec (CommRingCat.of k)) rfl :=
  rfl

/-- The atlas chart `Spec k → [Spec k / Γ]` is étale and surjective. -/
theorem constantAtlasChart_isEtaleSurjective : (constantAtlasChart k Γ).IsEtaleSurjective :=
  ActionTorsor.atlasChart_affineGroup_isEtaleSurjective_of_int (surjective_constant Γ) _ _ rfl

/-- **`Spec (Γ → k)` represents the trivial torsor `Γ × Spec k`**: the isomorphism of fppf
sheaves `fppfYoneda (Spec (Γ → k)) ≅ Γ ⊗ fppfYoneda (Spec k)` induced by the product structure
`constantArrowsSheafIsProduct`. -/
noncomputable def constantTrivialTorsorIso :
    fppfYoneda.obj (constantArrows k Γ) ≅
      (constantGroup Γ).space.toSheaf ⊗ fppfYoneda.obj (Spec (CommRingCat.of k)) :=
  (constantArrowsSheafIsProduct k Γ).conePointUniqueUpToIso
    (tensorProductIsBinaryProduct _ _)

/-- `constantTrivialTorsorIso` lies over `Spec k`. -/
theorem constantTrivialTorsorIso_hom_snd :
    (constantTrivialTorsorIso k Γ).hom ≫ snd _ _ = fppfYoneda.map (constantProjection k Γ) :=
  (constantArrowsSheafIsProduct k Γ).conePointUniqueUpToIso_hom_comp
    (tensorProductIsBinaryProduct _ _) ⟨WalkingPair.right⟩

/-- `constantTrivialTorsorIso` followed by the first projection is the map to `Γ`. -/
theorem constantTrivialTorsorIso_hom_fst :
    (constantTrivialTorsorIso k Γ).hom ≫ fst _ _ =
      fppfYoneda.map (constantArrowsToGroup k Γ) :=
  (constantArrowsSheafIsProduct k Γ).conePointUniqueUpToIso_hom_comp
    (tensorProductIsBinaryProduct _ _) ⟨WalkingPair.left⟩

/-- **The representation of the tautological torsor of the atlas chart** (the trivial torsor
`Γ × Spec k → Spec k`) by the scheme `Spec (Γ → k)` over `Spec k`. -/
noncomputable def constantTautRepresentation :
    TorsorRepresentation (constantAtlasChart k Γ).tautObj.toFppfTorsor where
  space := constantArrows k Γ
  toBase := constantProjection k Γ
  iso := constantTrivialTorsorIso k Γ
  iso_hom_projection := constantTrivialTorsorIso_hom_snd k Γ

/-! ## The explicit self-overlap presentation -/

/-- **The explicit self-overlap of the atlas `Spec k → [Spec k / Γ]`**: the pullback
presentation of the tautological object of `constantAtlasChart k Γ` with space `Spec (Γ → k)`
and both legs the structure map `constantProjection k Γ` (`constantSelfOverlap_fst`,
`constantSelfOverlap_snd`), obtained from the representation `constantTautRepresentation`. -/
noncomputable def constantSelfOverlap :
    (constantAtlasChart k Γ).PullbackPresentation (Spec (CommRingCat.of k))
      (constantAtlasChart k Γ).tautObj :=
  ActionTorsor.atlasPullbackPresentation (Spec (CommRingCat.of k)) rfl _
    (constantTautRepresentation k Γ)

/-- The space of the explicit self-overlap presentation is `Spec (Γ → k)`. -/
@[simp] theorem constantSelfOverlap_space :
    (constantSelfOverlap k Γ).space = constantArrows k Γ := rfl

/-- The first leg of the explicit self-overlap presentation is the structure map. -/
@[simp] theorem constantSelfOverlap_fst :
    (constantSelfOverlap k Γ).fst = constantProjection k Γ := rfl

/-- The second leg of the explicit self-overlap presentation is the structure map. -/
@[simp] theorem constantSelfOverlap_snd :
    (constantSelfOverlap k Γ).snd = constantProjection k Γ :=
  atlasPullbackPresentation_trivial_snd _ _

/-! ## Comparison with the chosen self-overlap -/

/-- The atlas chart `Spec k → [Spec k / Γ]` is representable. -/
theorem constantAtlasChart_isRepresentable : (constantAtlasChart k Γ).IsRepresentable :=
  (constantAtlasChart k Γ).isRepresentable_of_isEtaleSurjective
    (constantAtlasChart_isEtaleSurjective k Γ)

/-- The internally chosen self-overlap presentation `StackChart.selfOverlapScheme` of the atlas
chart (an arbitrary choice; compare `constantSelfOverlap`). -/
noncomputable abbrev constantChosenSelfOverlap :
    (constantAtlasChart k Γ).PullbackPresentation (Spec (CommRingCat.of k))
      (constantAtlasChart k Γ).tautObj :=
  (constantAtlasChart k Γ).selfOverlapScheme (constantAtlasChart_isRepresentable k Γ)

/-- **The chosen self-overlap scheme of the atlas `Spec k → [Spec k / Γ]` is `Spec (Γ → k)`**:
the canonical isomorphism of the two pullback presentations. -/
noncomputable def selfOverlapIso :
    (constantChosenSelfOverlap k Γ).space ≅ constantArrows k Γ :=
  Sites.SiteChart.presentationIso (constantAtlasChart k Γ) (constantSelfOverlap k Γ)
    (constantChosenSelfOverlap k Γ)

/-- `selfOverlapIso` carries the first leg of the chosen self-overlap to the structure map. -/
theorem selfOverlapIso_hom_fst :
    (selfOverlapIso k Γ).hom ≫ constantProjection k Γ = (constantChosenSelfOverlap k Γ).fst :=
  Sites.SiteChart.presentationIso_hom_fst _ _ _

/-- `selfOverlapIso` carries the second leg of the chosen self-overlap to the structure map. -/
theorem selfOverlapIso_hom_snd :
    (selfOverlapIso k Γ).hom ≫ constantProjection k Γ = (constantChosenSelfOverlap k Γ).snd := by
  have h := Sites.SiteChart.presentationIso_hom_snd (constantAtlasChart k Γ)
    (constantSelfOverlap k Γ) (constantChosenSelfOverlap k Γ)
  rwa [constantSelfOverlap_snd] at h

/-- The inverse of `selfOverlapIso` followed by the first leg is the structure map. -/
theorem selfOverlapIso_inv_comp_fst :
    (selfOverlapIso k Γ).inv ≫ (constantChosenSelfOverlap k Γ).fst = constantProjection k Γ :=
  (Iso.inv_comp_eq _).2 (selfOverlapIso_hom_fst k Γ).symm

/-- The inverse of `selfOverlapIso` followed by the second leg is the structure map. -/
theorem selfOverlapIso_inv_comp_snd :
    (selfOverlapIso k Γ).inv ≫ (constantChosenSelfOverlap k Γ).snd = constantProjection k Γ :=
  (Iso.inv_comp_eq _).2 (selfOverlapIso_hom_snd k Γ).symm

/-! ## The chart groupoid and its Vistoli Chow groups -/

/-- **The chart groupoid of the atlas `Spec k → [Spec k / Γ]`**: the étale presentation groupoid
`StackChart.etaleGroupoid` of `constantAtlasChart k Γ`, with structure map `𝟙 (Spec k)`. -/
noncomputable abbrev constantChartGroupoid : EtalePresentationGroupoid.{u} :=
  (constantAtlasChart k Γ).etaleGroupoid (constantAtlasChart_isEtaleSurjective k Γ)
    (𝟙 (Spec (CommRingCat.of k)))

/-- The chosen self-overlap scheme is compact (it is isomorphic to `Spec (Γ → k)`). -/
instance constantChosenSelfOverlap_compactSpace :
    CompactSpace (constantChosenSelfOverlap k Γ).space :=
  (selfOverlapIso k Γ).hom.homeomorph.symm.compactSpace

/-- The chosen self-overlap scheme is locally Noetherian. -/
instance constantChosenSelfOverlap_isLocallyNoetherian :
    IsLocallyNoetherian (constantChosenSelfOverlap k Γ).space :=
  have := (constantAtlasChart k Γ).selfOverlapScheme_fst_etale _
    (constantAtlasChart_isEtaleSurjective k Γ)
  LocallyOfFiniteType.isLocallyNoetherian (constantChosenSelfOverlap k Γ).fst

/-- The first leg of the chosen self-overlap is quasi-compact. -/
instance constantChosenSelfOverlap_fst_quasiCompact :
    QuasiCompact (constantChosenSelfOverlap k Γ).fst := by
  have h : (constantChosenSelfOverlap k Γ).fst =
      (selfOverlapIso k Γ).hom ≫ constantProjection k Γ := (selfOverlapIso_hom_fst k Γ).symm
  rw [h]
  infer_instance

/-- The chart groupoid of `Spec k → [Spec k / Γ]` satisfies the standing hypotheses `Good`. -/
theorem constantChartGroupoid_good : (constantChartGroupoid k Γ).Good :=
  have := (constantAtlasChart k Γ).selfOverlapScheme_fst_etale _
    (constantAtlasChart_isEtaleSurjective k Γ)
  EtalePresentationGroupoid.good_of_locallyOfFiniteType (𝟙 (Spec (CommRingCat.of k)))
    ((constantChosenSelfOverlap k Γ).fst ≫ 𝟙 (Spec (CommRingCat.of k)))

/-- **The groupoid `Γ_k ⇉ Spec k` is the chart groupoid of `Spec k → [Spec k / Γ]`**: the
isomorphism of groupoids (identity on the base `Spec k`, `selfOverlapIso` on arrows, compatible
with both legs) packaged as a `MoritaMap` via `MoritaMap.ofArrowIso`. -/
noncomputable def constantMoritaMap :
    MoritaMap (constantGroupoid k Γ) (constantChartGroupoid k Γ) :=
  MoritaMap.ofArrowIso (Iso.refl _) (selfOverlapIso k Γ).symm
    (by
      change (selfOverlapIso k Γ).inv ≫ (constantChosenSelfOverlap k Γ).fst =
        constantProjection k Γ ≫ 𝟙 _
      rw [selfOverlapIso_inv_comp_fst, Category.comp_id])
    (by
      change (selfOverlapIso k Γ).inv ≫ (constantChosenSelfOverlap k Γ).snd =
        constantProjection k Γ ≫ 𝟙 _
      rw [selfOverlapIso_inv_comp_snd, Category.comp_id])
    (fun u => by
      change DimensionFunction.specField k u =
        FiniteTypeDimension.dimensionFunction (𝟙 (Spec (CommRingCat.of k))) u
      rw [dimensionFunction_eq (DimensionFunction.specField k)
        (FiniteTypeDimension.dimensionFunction (𝟙 (Spec (CommRingCat.of k))))])
    (fun u => by
      obtain ⟨r⟩ : Nonempty (constantArrows k Γ) := inferInstance
      refine ⟨r, Subsingleton.elim _ _, Subsingleton.elim _ _, ?_⟩
      simp)

/-- **The Vistoli Chow groups of the atlas `Spec k → [Spec k / Γ]` are those of
`constantGroupoid k Γ`**: the linear isomorphism induced by the groupoid isomorphism
`constantMoritaMap` (`MoritaMap.vistoliChowEquiv`). -/
noncomputable def vistoliChowEquivConstant (i : ℤ) :
    (constantAtlasChart k Γ).vistoliChow (constantAtlasChart_isEtaleSurjective k Γ)
        (𝟙 (Spec (CommRingCat.of k))) i ≃ₗ[ℚ] (constantGroupoid k Γ).vistoliChow i :=
  (constantMoritaMap k Γ).vistoliChowEquiv i (constantGroupoid_good k Γ)
    (constantChartGroupoid_good k Γ)

/-! ## The degree of the chart groupoid -/

/-- The dimension function of the self-overlap scheme of the chart groupoid vanishes. -/
theorem constantChartGroupoid_arrowsDim_apply (r : (constantChartGroupoid k Γ).arrows) :
    (constantChartGroupoid k Γ).arrowsDim r = 0 := by
  rw [(constantChartGroupoid k Γ).src_dim r]
  change FiniteTypeDimension.dimensionFunction (𝟙 (Spec (CommRingCat.of k))) _ = 0
  rw [dimensionFunction_eq (FiniteTypeDimension.dimensionFunction (𝟙 (Spec (CommRingCat.of k))))
    (DimensionFunction.specField k)]
  rfl

/-- **The chart groupoid of `Spec k → [Spec k / Γ]` has degree `|Γ|`**: the first leg of the
self-overlap pushes its fundamental cycle to `|Γ| [Spec k]`, transported from
`constantGroupoid_isOfDegree` along `selfOverlapIso`. -/
theorem constantChartGroupoid_isOfDegree :
    (constantChartGroupoid k Γ).IsOfDegree (Nat.card Γ) := by
  have h := constantGroupoid_isOfDegree k Γ
  change _root_.AlgebraicGeometry.AlgebraicCycle.map (constantProjection k Γ)
    ⇑(constantArrowsDim k Γ) ⇑(DimensionFunction.specField k) _ = _ at h
  rw [dimensionFunction_eq (DimensionFunction.specField k)
    (FiniteTypeDimension.dimensionFunction (𝟙 (Spec (CommRingCat.of k))))] at h
  change _root_.AlgebraicGeometry.AlgebraicCycle.map (constantChosenSelfOverlap k Γ).fst
    ⇑(constantChartGroupoid k Γ).arrowsDim
    ⇑(FiniteTypeDimension.dimensionFunction (𝟙 (Spec (CommRingCat.of k)))) _ = _
  rw [← map_fundamentalCycle_eq_of_iso_comp (constantChosenSelfOverlap k Γ).fst
    (constantProjection k Γ) (selfOverlapIso k Γ).symm (selfOverlapIso_inv_comp_fst k Γ) _ _
    ⇑(constantArrowsDim k Γ) (fun x ↦ (constantChartGroupoid_arrowsDim_apply k Γ _).symm)]
  exact h

end GromovWitten.AlgebraicGeometry
