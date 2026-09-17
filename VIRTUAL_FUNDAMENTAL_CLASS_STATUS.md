# Behrend--Fantechi virtual fundamental class

Specification: [Tau Ceti roadmap comparison](https://github.com/TauCetiProject/TauCetiRoadmap/compare/main...Paul-Lez:TauCetiRoadmap:agent/behrend-fantechi-roadmap).

> **Implementation status: incomplete.**  The former conditional absolute and relative APIs have
> been retired because they accepted intrinsic-cone geometry, Chow/Gysin operations, resolved
> cones, and resolution independence as fields.  The public module now exports only completed
> constructions, currently the proper-point comparison.  General Behrend--Fantechi construction,
> independence, functoriality, and relative theory remain absent rather than assumed.

## Layer map

| Layer | Principal modules | Current artifact (not a completion claim) |
| --- | --- | --- |
| 0: spaces and stacks | `Spaces/*`, `Stacks/*` | fppf sheaves, fully faithful schemes and algebraic spaces as discrete stacks, representable properties, constructed binary categorical products and arbitrary categorical pullbacks of algebraic spaces, a constructed algebraic/Deligne--Mumford stack structure on every algebraic space, groupoid fibres, strong-morphism scheme charts, action-torsor groupoids together with their constructed base change along an arbitrary scheme morphism (the underlying fppf sheaf is the actual fibre product, and the group action, the equivariant map to `U`, the principal map, and the fppf-local section — whose cover is the base change of the original cover — are all constructed rather than assumed), which is proved functorial and equipped with identity and composition comparison isomorphisms, the unit and associativity coherence laws, and hence an assembled contravariant pseudofunctor `ActionTorsor.pullbackPseudofunctor` from the locally discrete bicategory of schemes into `Cat` whose fibres are exactly the torsor groupoids, now exported as the quotient prestack `quotientPrestack G U = [U/G]` and the classifying prestack `classifyingPrestack G = BG` (the trivial action on the one-point algebraic space), together with the constructed trivial torsor `G × T` over every scheme, whose left-multiplication action, principal isomorphism and global section are all built so that every fibre of `BG` is nonempty, the proved equivalence of each `BG` fibre with the groupoid `FppfTorsor G T` of fppf `G`-torsors, which commutes strictly with base change, and a genuine strong transformation `ActionTorsor.mapTargetStrongTrans` induced by every equivariant map of `G`-spaces, with all three strong-transformation coherence laws proved, in particular the structure morphism `[U/G] ⟶ BG`; the fppf descent condition of these prestacks, namely descent of arrows and effectivity of descent, remains open, so they are not bundled as `FppfStack`, algebraic/DM stack data, functorial transport of descent data along arbitrary strong transformations (including explicit vertical-composition coherence), a concrete groupoid-valued fibrewise two-pullback pseudofunctor with constructed strong projections and invertible comparison, a proved equivalence between its descent-data category and the genuine two-pullback of the projected descent-data categories, a proved comparison of the canonical global-to-descent functor with the induced pullback of the three component equivalences, and therefore a constructed general fibrewise two-pullback `FppfStack`; the canonical presentation is now equipped with a constructed full bicategorical bilimit proof, including explicit cone lifts, comparison-face coherence, uniqueness isomorphisms, and reconstruction of modifications from compatible projected pairs. Complete scheme presentations now transport across invertible stack 2-cells, stack equivalences are presented by identity scheme maps, representable properties are proved invariant under compatible equivalences of both source and target, any two genuine two-pullback presentations are proved equivalent from their bilimit properties, and multiplicative representable properties are stable under every genuine two-pullback projection with both universal-property uniqueness laws retained. Representable properties now also satisfy honest descent (`Stacks/PropertiesDescent.lean`): any two actual scheme presentations of the same base change are proved to sit in a genuine cartesian square of schemes (`StackMorphismPresentation.isPullback_baseChangeHom`, derived only from the two universal properties together with newly proved composition and target-change coherence for induced comparisons), so a Mathlib scheme-morphism property is independent of the chosen presentation, descends along every class of covers for which Mathlib supplies `MorphismProperty.DescendsAlong`, is local on the test schemes for every `IsZariskiLocalAtTarget` property, and remains compatible with composition, base change, arbitrary genuine two-pullbacks, and equivalences of source and target. fppf, hence also smooth and etale, descent is available for smooth, etale, unramified, locally-of-finite-type, locally-of-finite-presentation, quasi-compact, finite-type, finite-presentation, surjective, open-immersion and isomorphism morphisms; fpqc descent for quasi-compactness is absent from the pinned Mathlib and is proved here (`quasiCompact_descendsAlong_fpqcCover`), which is what makes the finite-type and finite-presentation cases available. Flat, separated, proper, and the immersion properties currently descend only along open covers of the test schemes, because Mathlib supplies no faithfully flat descent for `IsAffineHom`, `IsClosedImmersion`, or `Flat`. Constructed symmetry and left/right identity two-pullbacks remain available, and common atlas refinements together with their presentation groupoids are now constructed (`Stacks/AtlasRefinement.lean`): for any two stack morphisms `U → X`, `V → X` the genuine two-pullback supplies a refining morphism `U ×_X V → X` with both comparison projections and both comparison 2-cells, and it is a theorem, not input data, that the refinement inherits every multiplicative representable property of the two given morphisms, in particular smooth-surjectivity, so a common refinement of two atlases is again an atlas (`Genuine.refinementHom_hasRepresentableProperty`, `Genuine.refinementHom_smoothSurjective`, `StackTwoPullback.exists_commonRefinement`); the multiplicativity of `Smooth` and of `Smooth ⊓ Surjective`, absent from the pinned Mathlib, is proved here. From a genuine self two-pullback the groupoid `U ×_X U ⇉ U` is constructed with source, target, unit (the relative diagonal), inversion and composition over the constructed stack of composable pairs, each with its projection 2-cells obtained from the bicategorical universal property and with the full comparison-face coherence (`ConeLiftClassifies`) proved for inversion and composition; source and target are proved to inherit the representable properties of the atlas. Over every test scheme the same groupoid is completely explicit: objects are the objects of `U(T)`, arrows are the actual isomorphisms in `X(T)` between their images, all `Groupoid` axioms are proved, the arrows are in bijection with the objects of the fibre of `U ×_X U` and the automorphism group at a point is exactly the automorphism group of its image in `X`, so every stabilizer arrow is retained. Refinement compatibility holds in both registers: a refinement 2-cell induces a morphism of presentation groupoids with its source and target 2-cells and its comparison face (`refinementGroupoidMap`, `refinementGroupoidMap_classifies`), and fibrewise the induced functor is proved full and faithful, conjugation by the refinement 2-cell being a bijection on arrows; both comparison functors out of a common refinement of two atlases are therefore fully faithful. On the topological side the point relation of a chart is proved independent of the chosen self-overlap presentation (`StackChart.pointRelation_eq`), and for the quotient topology built in `Stacks/Geometry.lean` the atlas point relation is proved to be an equivalence relation, reflexivity, symmetry and transitivity being the constructed unit, inversion and composition of the chosen self-overlap, so the generated closure adds nothing and the underlying point space is the honest orbit set, `atlasPointMap x = atlasPointMap y ↔ atlasPointRelation x y`, with the quotient-topology characterisation `IsOpen S ↔ IsOpen (atlasPointMap ⁻¹' S)`. Independence of that space from the chart itself remains open, as do the chart-level `AtlasCommonRefinement`/`AtlasTripleRefinement` witness records (which would need a constructor assembling a strong-transformation modification out of fibrewise chart comparisons), the uniqueness-driven groupoid identities `inverse ∘ inverse ≅ 𝟙` and associativity of composition, and the former quotient-stack and algebraic-stack-product presentation records; the terminal fppf stack is now constructed from the terminal sheaf of types and proved bicategorically terminal (a structural morphism `FppfStack.toTerminal` out of every stack, with its hom-category proved contractible: any two such morphisms are canonically 2-isomorphic and modifications between them are unique), which yields the absolute product `X × X` as a genuine two-pullback over it and hence a constructed diagonal `stackDiagonal : X ⟶ X × X` obtained as the bilimit lift of the identity cone. `Stacks/Inertia.lean` then constructs the inertia stack `inertiaStack X = X ×_{X × X} X` as the canonical genuine self two-pullback of that diagonal, together with its projection `inertiaProjection X : I_X ⟶ X`, and proves, from the two-pullback itself and not by assumption, that over every test scheme `T` the inertia fibre is equivalent to the category `AutObj (StackFiber X T)` of objects of `X(T)` equipped with an automorphism (`inertiaFiberEquivalence`), with the projection identified with the functor forgetting the automorphism. This description is proved invariant under equivalence of stacks (`inertiaFiberEquivalenceOfStackEquivalence`, via the fibre equivalence induced by `StackEquivalenceData` and functoriality of `AutObj`), is proved to collapse for stacks with thin fibres, in particular schemes (`representedStack_inertiaFiberEquivalence`: inertia of a scheme is the scheme), and transports along any identification of the fibre with another category (`inertiaFiberEquivalenceOfFiberEquivalence`), which is the form needed for `[U/G]` once the quotient prestack is proved to be a stack. Because inertia is a genuine base change of the diagonal, the inertia projection inherits every multiplicative representable scheme-morphism property of the diagonal (`inertiaProjection_hasRepresentableProperty`); in particular a Deligne--Mumford, i.e. unramified, diagonal forces `I_X ⟶ X` to be unramified (`inertiaProjection_unramified`), and an étale diagonal forces it to be étale. `DeligneMumfordStack` stores only an étale surjective atlas and therefore has no redundant diagonal field. The Deligne--Mumford diagonal criterion itself is still open in both directions: `DiagonalHasProperty` (isomorphism sheaves) and `StackHom.HasRepresentableProperty` applied to `stackDiagonal` (base changes of a stack morphism) are two unrelated encodings of the same diagonal, and all descent results in `Stacks/PropertiesDescent.lean` are stated for the second, so no comparison exists yet; moreover deducing an unramified diagonal from an étale atlas needs the base change of the diagonal along `U × U ⟶ X × X`, i.e. products of stack morphisms and a pasting calculus for genuine two-pullbacks, neither of which is available, even though the scheme-level inputs are (`StackChart.unramified_of_isEtaleSurjective`, Mathlib's étale cancellation and fppf descent for unramifiedness). The converse direction needs étale slices through a smooth atlas, for which Mathlib v4.33.1 supplies nothing Stack dimension is now public and atlas-free (`Stacks/Dimension.lean`): `AlgebraicStack.dim X` is the supremum in `WithBot (WithTop ℤ)` of the corrected dimensions `dim U − r` of all atlas dimension presentations, so no chart occurs in the value, and `AlgebraicStack.dim_eq_of_independent`, `dim_eq_of_pureStackDimension`, `pureStackDimension_iff_dim_eq` and `dim_eq_bot_iff` compute it from any single presentation once atlas independence is known. Atlas independence is reduced to two named, isolated inputs rather than assumed: `StackDimensionPresentation.CommonRefinement` is the honest witness record for the overlap `U ×_X V` (only scheme-level geometric data; no field records a dimension of `X`), and `correctedDimension_eq_of_commonRefinement` proves `dim U − r_U = dim V − r_V` by computing the pure dimension of the overlap through each of its two smooth projections, whence `stackDimensionIndependent_of_commonRefinement`. Half of the overlap is constructed outright: `StackDimensionPresentation.overlap` is the actual chart pullback presentation chosen from representability of the first atlas, and `overlap_fst_smooth`, `overlap_fst_surjective`, `overlap_fst_relativeDimension` prove that `U ×_X V ⟶ V` is a smooth surjection of pure relative dimension `r_U`. The 2-categorical form of the other half is also proved: because pure relative dimension is not multiplicative (relative dimensions add), the existing base-change theorem does not apply, so composition of representable properties is reproved for three separate `MorphismProperty`s (`StackHom.comp_hasRepresentableProperty_of_comp`), giving `StackHom.twoPullbackSnd_hasPureRelativeDimension` and, via `StackTwoPullback.swap`, `StackHom.twoPullbackFst_hasPureRelativeDimension`: both projections of a genuine two-pullback carry the pure relative dimension of the opposite morphism. Two gaps remain and are named rather than hidden. First, the scheme-level formula `dim(source) = dim(target) + r` for a smooth surjection of pure relative dimension `r` is stated as the proposition `SmoothPureDimensionFormula` and is unproved: the pinned Mathlib has `topologicalKrullDim` and `SmoothOfRelativeDimension` but no dimension formula for flat or smooth morphisms, the missing input being `dim 𝒪_{W,w} = dim 𝒪_{U,q w} + dim 𝒪_{W_{q w},w}` for a flat local homomorphism (Stacks 02JS); only the degenerate cases `schemePureDimension_of_isIso` and `schemePureDimension_of_surjective_etale` are available, the latter proved here from the topological étale descent of `Curves/RelativeDimension.lean`. Second, the scheme-level second projection `U ×_X V ⟶ U` still needs a leg-exchanging comparison of chart pullback presentations for two distinct charts (only `PullbackPresentation.selfSwap` exists), equivalently a bridge between `StackChart.PullbackPresentation` and `StackMorphismPresentation` of the chart morphism; `CommonRefinement.ofOverlap` takes exactly those three missing facts as arguments. Conditional on the smooth formula, the derived identities are proved with a single sign convention: `correctedDimension_of_smoothCover` (`dim X = dim Y + r` for a smooth atlas cover of relative dimension `r`), `correctedDimension_add` (`dim(X × Y) = dim X + dim Y` in the form available before products of algebraic stacks are constructed), and `correctedDimension_quotient`/`AlgebraicStack.dim_quotient` (`dim [U/G] = dim U − dim G`); unconditionally, `FppfStack.pureStackDimension_ofSchemeAlgebraicStack` proves that a scheme pure of dimension `d`, viewed as a stack, has pure stack dimension `d`, generalizing the former `Spec k` computation. The quotient formula is stated for an abstract atlas of relative dimension `dim G` because `[U/G]` is not yet an algebraic stack here, the `AlgebraicQuotientPresentation.algebraicStack` block remaining retired, and applies verbatim once it is |
| 1: modules and cones | `Sites/*`, `Modules/Stack.lean`, `Cones/Affine.lean`, `Cones/Stack.lean` | distinct stack sites, canonical regular-function sheaves, constructed ringed-site identity/composition and module pullback adjunctions, actual module sheaves, direct sums and canonical finite-free sheaves, symmetric affine cones, Rees normal cones, the proved canonical closed immersion `Spec(gr_I R) → Spec Sym(I/I²)`, the proof that this canonical map is an isomorphism when the affine ideal comes with a chosen finite regular generating sequence (`Cones/RegularSequence.lean`, on top of the neutral commutative-algebra file `Algebra/QuasiRegular.lean`), concrete quotient groupoids, and a constructed rank-zero vector-bundle stack; the former relative-Spec/Proj and derived-Picard theorem packages are inactive; `Cones/DeformationSpace.lean` now constructs the affine deformation to the normal cone: the extended Rees algebra `R[It, t⁻¹]` is built as the subalgebra of Laurent polynomials whose degree-`n` coefficient lies in `Iⁿ` for `n ≥ 0`, with the deformation parameter `u = t⁻¹` proved a nonzerodivisor, the special fibre `R[It, t⁻¹]/(u)` proved isomorphic to the associated graded ring `gr_I(R)` (the coordinate ring of the affine normal cone), so that the normal cone is a closed subscheme of the deformation space `M° = Spec R[It, t⁻¹]` lying over the origin of the affine line, the localization at `u` proved to be the full Laurent polynomial ring, so that the generic fibre over `𝔾_m` is the trivial family `Spec R × 𝔾_m` embedded as the open subscheme `D(u)`, the fibre over `u = 1` proved isomorphic to `Spec R` itself (evaluation at `t = 1` is surjective with kernel `(u − 1)`, by an explicit geometric-series division inside the extended Rees algebra), and, over a base field `k`, the deformation space proved torsion-free hence flat over `k[u]`, so the structure morphism `M° → 𝔸¹_k` is a flat morphism of schemes; the cartesian-square packaging of these fibre identifications, the closed immersion `Spec(R/I) × 𝔸¹ → M°`, base change of the deformation space, and the tangent-bundle action on the normal cone remain to be constructed |
| 2: rational intersection theory | `IntersectionTheory/*` | scheme cycles graded by actual closure dimension, functorial proper pushforward on those cycle groups, constructed orders of vanishing, canonical rational equivalence, closed-immersion Chow pushforward, the proper-point Chow computation, and a constructed flat pullback along arbitrary open immersions which is proved rational-linear and contravariantly functorial, proved to descend to the rational Chow quotient, and assembled into the right-exact part of the localization sequence: restriction to an open subscheme of a Noetherian scheme is proved surjective through an actual extension-by-zero section, and it is proved to annihilate every class pushed forward from a closed subscheme of the complement; the principal divisor of a rational function is proved to have zero Chow class. `IntersectionTheory/StackChowVistoli.lean` now adds the Vistoli descent construction on top of this: for a scheme-level presentation groupoid `R ⇉ U` whose source and target are open immersions of relative dimension zero (`OpenPresentationGroupoid`, a data-only record with no conclusion stored in a field), the Vistoli cycles are constructed as the equalizer `{α ∈ Z_i(U) : s^*α = t^*α}` of the two genuine flat pullbacks, proved equal to the pointwise descent condition `α(s(r)) = α(t(r))` (`mem_cycles_iff`), and the Vistoli rational Chow group `chow` is their quotient by rational equivalence on the atlas. A refinement of presentations (an open immersion of atlases intertwined with a map of arrow schemes, the scheme shadow of `refinementGroupoidMap`) is proved, not assumed, to carry Vistoli cycles to Vistoli cycles and to preserve rational equivalence, hence to induce a map of Vistoli Chow groups which is proved functorial (`chowMap_id`, `chowMap_trans`); two presentations with a common refinement are therefore canonically comparable (`commonRefinementComparison`), and an invertible refinement induces an isomorphism (`Refinement.chowEquiv`, `commonRefinementEquiv`). For a presentation whose two legs agree, in particular the identity atlas of a scheme, every cycle is proved to descend and the Vistoli Chow group is proved canonically isomorphic to the scheme rational Chow group, compatibly with both quotient maps (`chowEquivSchemeChow`, `identityPresentationChowEquiv`), so the construction genuinely extends the scheme theory. On the stabilizer side the rational weight `1/n` is constructed with its normalization `n · (1/n) = 1` and the weight-one criterion for trivial stabilizers; for an object of a presentation groupoid the weight is proved to be `1/|Aut|` of its image in the base stack (`autWeight_presentationGroupoid`, via `PresentationGroupoid.autEquiv`) and is proved invariant under refinement of atlases (`autWeight_refinementFunctor`, via the fully faithful refinement functor). The stabilizer-weighted degree of a zero-cycle is constructed and proved independent of the finite set used to compute it, and on the one-point presentation over `Spec k` it is assembled into an actual homomorphism `chow 0 →ₗ[ℚ] ℚ` on the Vistoli Chow group, for which the fundamental class of a point with stabilizer group `Γ` is proved to have degree `1/|Γ|`, with `|Γ| · deg = 1` (`pointDegree_pointFundamentalClass`, `card_mul_pointDegree_pointFundamentalClass`, and `weightedDegree_fundamentalCycle_of_autEquiv` with the stabilizer read off from a genuine presentation-groupoid object). What is still missing is precisely one geometric input: flat pullback of algebraic cycles along a flat morphism of positive relative dimension. Mathlib v4.33.1 supplies only `AlgebraicCycle.map` (proper pushforward) and no `AlgebraicCycle.pullback`, so the source and target of the presentation groupoid of a genuine smooth or étale atlas, smooth surjective and not open immersions, are outside the construction, and `OpenPresentationGroupoid` cannot yet be instantiated on `AlgebraicStack.chosenAtlasSelfOverlap`. Consequently atlas independence is proved only in the refinement form above: that the comparison map of an arbitrary smooth refinement is an isomorphism is exactly exactness of `0 → A(X) → A(U) ⇉ A(R)` for a smooth cover and needs both that flat pullback and its surjectivity (Fulton, Intersection Theory, Prop. 1.9 with descent), neither of which exists. `BΓ` is likewise unavailable as a Deligne--Mumford stack, since `classifyingPrestack` is only a prestack until fppf descent for action torsors is proved, so the degree theorem is stated for the one-point atlas with stabilizer group `Γ` that such a presentation would supply; and the weighted degree descends to Chow classes only where rational equivalence is trivial, general descent being the degree theorem `deg div(f) = 0`, which rests on the same missing norm/`Ring.ord`-additivity input already recorded for general proper pushforward. Stack cycle generators, rational functions, and atlas divisor calculations in `StackChow.lean` remain experimental and their uncertified quotient and all stack pullback, positive-rank Gysin, and Chern operations are inactive |
| 3: cotangent complexes | `CotangentComplex/*` | Mathlib derived categories, homology-defined amplitude, affine presentation/conormal comparison, flat base change in the affine model, and a constructor sending an actual affine presentation to its derived object; `CotangentComplex/PerfectComplex.lean` now adds the affine (module) model of perfectness as fixed definitions rather than fields: `IsFiniteFree` (Mathlib freeness plus finiteness), `IsStrictlyPerfect` (a bounded complex all of whose terms are finite free), `IsPerfect E` (existence of a strictly perfect complex together with an actual isomorphism `Q(K) ≅ E` in `DerivedCategory (ModuleCat R)`), and `HasTorAmplitudeIn` (vanishing cohomology of the termwise tensor with an arbitrary module). Proved: a finite free module in one degree is strictly perfect and perfect; shifts, finite direct sums and mapping cones of strictly perfect complexes are strictly perfect (two-out-of-three for the strict notion); base change along an arbitrary ring homomorphism preserves strict perfectness (with the missing `ModuleCat.extendScalars` additivity instance supplied here); shifts and biproducts of perfect derived objects are perfect; a complex supported in `[a,b]` has Tor amplitude in `[a,b]`. The rank is the honest alternating `finsum` of `Module.finrank`, proved invariant under isomorphism, additive on direct sums and on cones (`rank(cone φ) = rank G − rank F`), multiplied by `Int.negOnePow n` under shift, and equal to `rank(K⁰) − rank(K⁻¹)` in the two-term range. `GlobalTwoTermResolution E` stores an actual `[-1,0]` complex of finite free modules plus an actual derived isomorphism onto `E`, with transport along derived isomorphisms proved functorial (`replace_refl`, `replace_trans`), rank-invariant, and implying perfectness and Tor amplitude in `[-1,0]`; an affine presentation whose conormal and ambient differential modules are finite free supplies such a resolution of its own derived object, with virtual rank `finrank(CotangentSpace) − finrank(Cotangent)`. Still absent: a geometric cotangent complex and its Jacobi--Zariski transitivity triangle, perfectness local on an atlas (no derived category of module sheaves on a stack site), derived tensor/dual operations and hence tensor-closure, `rank_dual` and two-out-of-three for perfectness in a distinguished triangle, and derived base change of resolutions; the arbitrary-predicate global-resolution constructor stays inactive |
| 4: cone stacks | `Cones/TwoTermQuotient.lean`, `Cones/Picard.lean`, `Cones/DerivedPicard.lean`, `Cones/Stack.lean` | actual Picard groupoids, fixed-base groupoid fibres, pullback-natural addition/actions, contraction and stabilizers, chain-homotopy 2-isomorphisms, quasi-isomorphism equivalences, an explicit `[K ≃ K]` acyclic-summand homotopy equivalence, vector-bundle-stack ranks derived from an actual local finite-free matrix quotient presentation, and a constructed rank-zero bundle stack whose fibres are explicitly equivalent to `[0/0]`. `Cones/DerivedPicard.lean` now makes `h¹/h⁰` functorial and derived: two-term complexes of `R`-modules are given a `Category` instance and `h¹/h⁰` is an honest functor `picardFunctor : LinearTwoTermComplex R ⥤ Cat`, with specified pseudofunctor comparison 2-cells (`picardCompIso`, `picardIdIso`) whose associativity and both unit coherence laws are proved; they are identities, and strictness is proved from the chain-level formulas rather than assumed. Chain homotopies are the invertible 2-cells: identity, vertical composition, inverse, both whiskerings and horizontal composition are constructed (`ChainHomotopy.refl/vcomp/symm/postcomp/precomp/hcomp`) and `ChainHomotopy.natTrans` is proved to take each of them to the corresponding operation on natural transformations (`natTrans_refl`, `natTrans_vcomp`, `natTrans_symm`, `natTrans_postcomp`, `natTrans_precomp`, `natTrans_hcomp`). A cochain complex of modules has a functorial underlying two-term complex in degrees `-1,0` (`cochainFunctor`, `cochainPicardFunctor`), and Mathlib homotopies and homotopy equivalences of such complexes restrict to the repo's chain-level notions (`ofHomotopy`, `ofHomotopyEquiv`). For a derived object `E` with a `GlobalTwoTermResolution F`, `h¹/h⁰(E)` is defined as `F.picard`, with vertex automorphisms proved to be `h⁰` (the kernel of the differential) and isomorphism classes proved to be `h¹` (its cokernel). Resolution independence is proved unconditionally: the resolving complex is proved K-projective (bounded above, free hence projective terms), so Mathlib's `CochainComplex.IsKProjective.Qh_map_bijective` lifts the derived comparison isomorphism of any two global two-term resolutions of the same `E` to an actual chain map realizing it (`exists_chain_realization`), that chain map is a quasi-isomorphism and therefore a homotopy equivalence of cochain complexes (`exists_homotopyEquiv`), and hence the two Picard groupoids are equivalent (`hasChainComparison`, `nonempty_picardEquivalence`), with the explicit hypothesis form `Comparison`/`HasChainComparison` retained for the future sheaf-level statement and proved stable under identity, composition and transport along `E ≅ E'`. Functoriality in composites is proved on the nose in the forward direction and up to a canonical natural isomorphism on inverses (`quotientEquivalence_comp_functor`, `quotientEquivalenceCompInverseIso`, `transPicardEquivalenceInverseIso`, all from uniqueness of right adjoints), and the inverse of the equivalence attached to a quasi-isomorphism is proved to agree with the chain-level inverse (`HomotopyEquivalence.quasiIsoInverseIso`), in particular with the projection off the acyclic summand `[K ≃ K]`, which is also proved to be a strict retraction (`AcyclicSummand.inverseIsoProjection`, `inclusion_quotientFunctor_comp_projection`). Still absent: canonicity of the comparison equivalence (the realizing chain map is unique only up to homotopy, so the equivalence is canonical only up to the `ChainHomotopy.natIso` 2-cells, and no uniqueness statement is proved); a comparison of the elementwise kernel/cokernel quasi-isomorphism predicate with Mathlib's `QuasiIso`, which would need the homology of a `[-1,0]`-complex of `ModuleCat R` identified elementwise with the kernel and cokernel of its differential; and any sheaf-level version, since there is no derived category of module sheaves on a stack site |
| 5: intrinsic cones | `IntrinsicNormalCone/*` | the honest local-embedding type remains; the former records supplying local cones, descent, purity, abelian hulls, and relative comparisons are inactive; the proper point has a separately constructed global zero intrinsic cone |
| 6: obstruction theories | `ObstructionTheory/*` | the cohomological definition remains; the point POT is proved perfect from its concrete, field-specific finite-free resolution and zero amplitude; the former arbitrary-predicate resolution, geometric-realization, and deformation packages are inactive |
| 7: virtual class | `VirtualFundamentalClass/Basic.lean`, `Examples.lean`, `Public.lean` | the proper point has a constructed Rees cone, perfect identity POT, rank-zero target, direct rank-zero resolved formula, virtual/fundamental equality, and degree one; the former general scheme/stack resolved-cone and independence packages are inactive |
| 8: functoriality | `VirtualFundamentalClass/Functoriality.lean` | genuine cartesian-square shapes remain active; the chosen equivalence in a cartesian square is required to classify its displayed cone, and isomorphisms of squares satisfy the comparison-face pasting equation; cotangent-triangle compatibility is absent, and records carrying virtual-pullback, product, and graph formulas as fields are inactive, so the theorems remain to be constructed |
| 9: relative theory | `IntrinsicNormalCone/Relative.lean`, `VirtualFundamentalClass/Relative*.lean` | the relative diagonal used in the relative-DM predicate is constructed as the bilimit lift of the identity cone, but the former relative cone, resolved class, base-change, independence, and formula packages are inactive; genuine relative VFC theory remains to be built |

## Structural guarantees already established

- Stack fibres and quotient fibres are categories with `IsGroupoid`; automorphisms are retained.
- Equivariant fppf torsors over a scheme base change along every scheme morphism: the pulled-back
  sheaf, action, target map, principal isomorphism, and local triviality are constructed, and the
  resulting functors form a genuine pseudofunctor on the locally discrete bicategory of schemes
  with proved unit and associativity coherence.  That pseudofunctor is exported as `[U/G]` and,
  for the one-point algebraic space with its trivial action, as `BG`.  The fibre over each scheme
  is literally the torsor groupoid and base change is literally the constructed pullback functor,
  so no caller supplies stackification or a fibre equivalence.  The trivial torsor `G × T` is
  constructed with its left-multiplication action, its principal isomorphism, inverted using the
  inverse of the group object, and its global section, so every fibre of `BG` is nonempty, and the
  forgetful functor from each `BG` fibre to the groupoid of fppf `G`-torsors is proved to be an
  equivalence that commutes strictly with base change.  Every equivariant map of `G`-spaces
  induces an honest strong transformation of these pseudofunctors, with identity naturality cells
  and all three coherence laws proved.  No stackification of `[U/G]` is claimed: effective fppf
  descent for action torsors, and already the descent of their arrows, remain open and are nowhere
  assumed.
- Schemes embed bicategorically fully faithfully into groupoid-valued fppf stacks through a
  bundled Yoneda pseudofunctor.  Its unitor, compositor, and coherence laws are constructed,
  and on each pair of schemes the discrete category of scheme morphisms is proved equivalent to
  the full hom-category of strong transformations and modifications.
- Composition of representable stack morphisms is derived from the displayed universal
  properties rather than postulated.  The composite universal comparison, nested classifying
  map, projection equation, source-object pullback isomorphism, pseudofunctorial pasting theorem,
  full classification law, and both map and object-isomorphism uniqueness laws are constructed
  and packaged as an actual `StackMorphismPresentation`.  Hence every scheme-morphism property
  stable under composition is proved stable under composition for both the raw presentations
  and their explicit 2-isomorphism-invariant closure.  Complete presentations are now
  transported across an invertible stack 2-cell by conjugating every comparison and deriving
  both uniqueness fields; hence the raw and public predicates are proved equivalent rather
  than merely related by a closure.  The canonical genuine two-pullback projection has a
  constructed presentation over every scheme object: its representing map is reused from the
  original morphism, while its pullback object, face equation, map uniqueness, and
  stabilizer-sensitive object-isomorphism uniqueness are proved.  Thus representable
  properties are stable under this canonical two-categorical base change.  Any two `Genuine`
  bilimit presentations are now compared by universal lifts in both directions; the comparison
  face for each round trip is proved by pasting the two bilimit face equations, and both inverse
  2-cells are derived from bilimit uniqueness.  Composing this constructed equivalence with the
  canonical projection proves arbitrary genuine base-change stability for multiplicative
  representable scheme-morphism properties.  Pre- and postcomposition by a stack equivalence are
  separately proved iff-invariant, so a compatible equivalence of both source and target also
  preserves every multiplicative representable property.
- Binary products of algebraic spaces are constructed internally: the underlying fppf sheaf is
  the categorical product, its diagonal is proved representable by factoring maps from schemes
  through the represented scheme diagonal, and the product of two chosen scheme atlases is
  proved representable, etale, and surjective by two explicit cartesian base changes.  The
  induced cone satisfies the categorical product universal property in algebraic spaces.
- Arbitrary pullbacks of algebraic spaces are likewise constructed as sheaf pullbacks.  The
  canonical map `X ×_Z Y → X × Y` is proved to be the base change of the actual diagonal
  of `Z`; a general constructor proves that the source of any representable morphism to an
  algebraic space is algebraic by deriving both its diagonal and its pulled-back atlas.  The two
  sheaf projections then satisfy the pullback universal property in the induced category.
- Algebraic spaces embed bicategorically fully faithfully into groupoid-valued fppf stacks:
  the embedding is a bundled pseudofunctor with constructed unitor and compositor and proved
  coherence laws.  On every pair of objects, its local hom functor from the discrete category of
  algebraic-space morphisms to the full category of strong transformations and modifications is
  a constructed equivalence.  In particular, every strong transformation is reconstructed from
  a unique sheaf morphism, with an explicit invertible counit modification.  The defining scheme
  atlas of an algebraic space is converted
  into a stack chart by using the actual sheaf pullback square; every alternative chart
  presentation is proved isomorphic to that pullback before geometric properties are
  transferred.  The isomorphism scheme of two objects is similarly constructed as the actual
  base change of the sheaf diagonal.  Hence the algebraic-stack and Deligne--Mumford-stack
  structures on a discrete algebraic space are derived rather than supplied.
- Scheme charts are strong transformations from represented discrete stacks, so arrow maps and
  pullback coherence are inherited from pseudonaturality rather than weakened to inhabited
  objectwise comparisons.
- The point set and topology of an algebraic stack are no longer caller-selected fields: they
  are constructed as the quotient topology of the internally chosen smooth atlas by the
  equivalence relation generated by the two projections from its represented self-overlap.
  Atlas-independence and the local-ring package needed for divisors remain open.
- A `StackTwoPullback.Genuine` contains both the category-equivalent fibre description and its
  full bicategorical universal property.  Its chosen lift is proved compatible with the cone's
  comparison face, and projection induces a bijection from arbitrary modifications to compatible
  pairs of projected modifications.  Thus both essential surjectivity and hom-category full
  faithfulness are present.  `StackTwoPullback.canonicalGenuine` constructs these witnesses for
  every cospan directly from the fibrewise categorical pullback: its lift retains both legs and
  the cone comparison isomorphism, while uniqueness and the hom-set inverse use
  `CategoricalPullback.mkIso` and `CategoricalPullback.hom_ext`.  The right-identity pullback also
  constructs these witnesses explicitly.
  Interchanging the two legs is now an actual involutive equivalence on the categorical fibres;
  at stack level the swapped presentation, comparison-face equation, lift uniqueness, and
  projected-modification bijection are all derived from the original bilimit witnesses.  The
  left-identity pullback is consequently constructed by symmetry rather than supplied anew.
  VFC and deformation records require this bundled type.
- For an arbitrary cospan, the objectwise categorical pullbacks now form an actual
  groupoid-valued pseudofunctor.  Its two projection strong transformations, their canonical
  comparison modification, the inverse modification, and both cancellation laws are
  constructed from the stored objectwise comparison isomorphisms.  Strong transformations now
  induce actual functors between descent-data categories: their cocycles explicitly conjugate
  by the pseudonaturality cells.  Transport along a vertical composite is related to successive
  transport by a proved natural isomorphism, rather than silently identified.  The projected
  descent data and the comparison induced by the stored fibrewise isomorphisms therefore form
  an actual functor to the categorical two-pullback of descent-data categories.  A componentwise
  inverse functor and explicit unit and counit prove that this functor is an equivalence.  A
  general cospan-induced functor on genuine categorical pullbacks is proved to be an equivalence
  when its three component functors are equivalences.  Strong-transformation pseudonaturality
  then supplies an explicit natural isomorphism identifying the canonical global-to-descent
  functor with that induced pullback functor.  Consequently the fibrewise two-pullback
  pseudofunctor is now exported as an `FppfStack`, with a canonical `StackTwoPullback`
  presentation whose fibre equivalence and compatibility are definitionally identities.
- A cartesian-stack-square witness can no longer pair an unrelated equivalence of underlying
  stacks with the displayed square.  It includes projection 2-cells from that equivalence and a
  proof that they classify the full displayed cone; an isomorphism of such squares also obeys
  the pointwise pasting equation between the four side cells and the comparison faces.
- The relative diagonal in `RelativeDeligneMumfordMorphism` is not caller-selected.  It is the
  bilimit lift of the canonical cone with two identity legs, and its two projection comparisons
  and comparison-face classification are derived from the bilimit property before
  representable unramifiedness is imposed.
- `DeligneMumfordStack` asks only for the defining etale-surjective atlas on an algebraic stack.
  Unramifiedness of its diagonal is no longer a redundant constructor field: the general
  etale-atlas/unramified-diagonal criterion remains open until it is proved.  The represented
  scheme case has a separate constructed proof of diagonal unramifiedness.
- Cone-stack equivalences use invertible modifications of strong transformations and therefore
  commute with pullback in the test scheme.  The former intrinsic-cone refinement and cocycle
  packages are inactive; their construction remains open.
- Cone addition, negation, and vector-bundle-stack actions are functors on the actual groupoid
  fibre over a fixed base object and carry natural comparison isomorphisms under reindexing.
- The action-arrow relation for an abelian cone acting on a cone stack is constructed.  The former
  `ConeQuotientPresentation`, however, supplied the quotient cone and the hard essential
  surjectivity/orbit-hom bijectivity results as fields, so it is inactive.  The former
  `ConeStackBaseChange` and non-universal `AbelianHull` records are inactive for the same reason.
- The three stack sites are different Lean types.  Their structure sheaves are induced from
  the represented regular-function functor, whose fppf sheaf condition is proved.  The
  structure sheaves retain their commutative-ring values; their underlying ring sheaves are
  derived functorially for Mathlib's module API rather than forgetting commutativity in the
  ringed-site data.
- Ringed-site morphisms cannot accept unrelated sheaf/module functors: continuity determines
  sheaf restriction, and the structure-sheaf isomorphism determines module restriction.
- Identity and composition of ringed-site morphisms are constructed from the underlying
  continuous functors and the canonical comparison for iterated sheaf pushforward.  Module
  inverse image is that determined restriction functor, while module pullback is Mathlib's
  actual left adjoint to it.  Inverse-image identity/composition comparisons come from the
  corresponding pushforward comparisons; pullback identity/composition comparisons come from
  uniqueness of left adjoints.  None is accepted as a field.  This does not assume the
  still-missing small-etale/lisse-etale continuity and quasi-coherent comparison theorem.
- The tensor product is constructed by taking the pointwise tensor product of the underlying
  presheaves over that commutative structure presheaf and applying Mathlib's actual module
  sheafification.  The structure sheaf is constructed as its unit, with left/right unit
  comparisons obtained from the pointwise unitors and the sheafification counit; symmetry is
  sheafified from the pointwise tensor symmetry.  The full associativity/coherence package and
  preservation of quasi-coherence and finite-local-free rank remain open.
- Binary direct sums and zero module sheaves are inherited from the actual abelian category of
  sheaves of modules.  Canonical finite-free sheaves of every natural rank are built from
  Mathlib's free sheaf, with explicit local generators, finite-presentation witnesses, and
  bases; finite local freeness transports across actual sheaf isomorphisms and adds under the
  constructed direct sum.  Duals, symmetric/exterior powers, and atlas descent remain open.
- Scheme rational equivalence has no caller-selected generator or divisor map: generators are
  actual integral locally Noetherian closed immersions with nonzero function-field elements.
  Divisor cycles are the unmodified order-of-vanishing cycles pushed forward to the ambient
  scheme.  The scheme fundamental cycle uses the local-ring length at each generic point, so
  nilpotent thickness is retained; coefficient one is recovered for reduced schemes.  The total
  relation space is the span of all such principal divisors, and each graded relation space is
  obtained from the canonical dimension grading.  Mathlib's residue-degree map has been proved
  rational-linear here.  Residue degrees are proved multiplicative under composition.  A proper
  map's specializing property is used to lift strict specialization chains, proving directly
  that closure dimension cannot increase; consequently the actual fibre-sum pushforward is
  functorial on dimension-graded cycles for arbitrary proper scheme morphisms.  For closed
  immersions, residue degree one and exact preservation of closure dimension are derived from the
  stalk map and closed topology; pushforward is proved to carry every principal divisor to its
  composite closed subscheme and hence descends functorially to the rational Chow quotient.
  Flat pullback along an open immersion is now constructed rather than assumed: an open immersion
  is flat of relative dimension zero and its scheme-theoretic fibres are single reduced points, so
  every pullback multiplicity is one and the pullback of a cycle is restriction of coefficients.
  Local finiteness of the restricted support is proved from injectivity of the open embedding, and
  the pullback is proved rational-linear and contravariantly functorial for arbitrary composites
  of open immersions. That it descends through rational equivalence is a theorem, not a field: the
  trace of an integral locally Noetherian closed subscheme on an open subscheme is constructed as
  the actual scheme-theoretic restriction of its closed immersion, integrality and local
  Noetherianity are inherited from a nonempty open of an irreducible scheme, the induced map of
  function fields is the canonical dominant-morphism map, and the order of vanishing is proved
  unchanged because an open immersion preserves the codimension of every point and is etale. Hence
  the restriction of a principal divisor is the principal divisor of the restricted function, or
  zero when the trace is empty, and the canonical span of principal divisors is carried into the
  canonical span. The same statement for an arbitrary open immersion is derived by factoring it
  through its open range, using that flat pullback along an isomorphism is the residue-degree
  pushforward along the inverse. On dimension-graded cycles the pullback requires exactly the
  geometric hypothesis that the two certified gradings agree along the immersion, and it is proved
  functorial both on cycles and on the rational Chow quotient. Extension by zero from an open
  subscheme of a Noetherian scheme is constructed and proved to be an actual section of that
  pullback, so restriction of rational Chow classes to an open subscheme is proved surjective;
  composing the closed-immersion Chow pushforward of a closed subscheme of the complement with
  that restriction is proved to be zero. This is the right-exact part of the localization
  sequence; exactness in the middle is not claimed. The principal divisor of a rational function
  on an integral locally Noetherian scheme is proved to lie in the canonical relation space, so
  its rational Chow class is zero, which is the codimension-one comparison in the form the Chow
  definition uses. The norm/divisor theorem needed to descend an arbitrary proper pushforward to
  Chow groups remains open, and the exact missing input is recorded in the module documentation:
  for a proper surjective morphism of integral locally Noetherian schemes the pushforward of a
  principal divisor must vanish when the image drops dimension and otherwise be the divisor of the
  field norm; Mathlib v4.33.1 supplies neither the norm along a finite extension of function
  fields nor the additivity of `Ring.ord` along a finite local extension on which that theorem
  rests. All
  cycle and Chow quotients used by the virtual-class API have coefficient field `ℚ`.  The active
  stack groundwork stops at fixed geometric cycle carriers and stack rational-function
  generators can no longer be replaced by a caller-selected type: they are actual nonzero
  rational maps to the affine line whose two pullbacks agree on the actual represented
  self-overlap of the internally chosen etale atlas.  The overlap and both etale-surjective
  projections are constructed from the atlas representability clause, with the second obtained
  from a proved involution of the represented self-pullback.  The presentation-free
  statement for every pair of dominant atlas maps defining isomorphic stack objects is now
  derived from the overlap universal property rather than stored in the function.  The conversion
  between function-field values and rational maps uses Mathlib's spreading-out theorem, and the
  constant-one function is constructed and proved to descend.  Pullback of a rational map is
  proved to agree with the canonical dominant-morphism map of function fields by unfolding its
  actual dense-open composition domain.  That canonical map is proved to agree with the
  fraction-field extension from every etale local stalk, and the length-defined order is proved
  etale invariant.  This groundwork is not yet promoted to a Chow quotient: the former
  certificate-based relation space could omit rational functions lacking a supplied dense-image
  certificate and is now inactive.  The integral atlas of a closed DM substack is an existential
  property and is chosen
  internally when a calculation needs it, so changing the witness atlas or its proofs no longer
  changes the raw presentation.  The actual cycle-generator type is the quotient of those raw
  presentations by the equivalence relation generated by stack equivalences compatible with
  the closed immersions into the ambient stack (and their certified dimensions).  Thus replacing
  a closed substack by an equivalent stack model cannot create a second cycle-basis vector.
- A `VectorBundleStack` no longer carries an independent integer rank.  It contains a genuine
  smooth-surjective scheme chart, an actual matrix between finite free modules, and fibre
  equivalences with the associated translation quotient; `stackRank` is defined as the
  difference of those two displayed free ranks.
- Those local fibre equivalences are now required to commute with pullback along every scheme
  map.  The comparison uses a constructed scalar-extension functor that maps both vectors and
  translation arrows entrywise, together with chart pseudonaturality to align the displayed base
  objects.  They also preserve zero, addition, and negation on both objects and arrows.  The
  explicit rank-zero bundle satisfies these laws by construction.
- Every algebraic stack has a constructed zero vector-bundle stack: total space, projection,
  vertex, and contractions are identities; each fixed-base fibre is proved contractible; its
  abelian coherences follow from singleton hom-sets; and its chosen smooth atlas presents it by
  the actual zero matrix `0 → 0`, with an explicit equivalence to the quotient groupoid `[0/0]`.
- Invertible 2-cells now transport actual stack-morphism scheme presentations without changing
  their representing scheme map.  Consequently representable properties and pure relative
  dimension are proved invariant under 2-isomorphism rather than re-supplied as fields.
- The former general scheme and stack homotopy-invariance records are inactive because they
  accepted the central Chow equivalence or its bijectivity as a field.  The proper point instead
  defines its rank-zero zero-section Gysin map directly as transport along the proved equality
  `i + rank(F₁) = i`.  General positive-rank homotopy invariance, projective-bundle Chern theory,
  self-intersection, and refined Gysin remain open.
- The former normal-cone and deformation base-change packages are inactive; they supplied the
  base-changed cones, deformation spaces, and equivalences as fields.
- The affine deformation to the normal cone is now constructed rather than supplied: the extended
  Rees algebra `R[It, t⁻¹]` inside the Laurent polynomials, its parameter `u = t⁻¹` proved a
  nonzerodivisor, the special fibre `R[It, t⁻¹]/(u)` proved isomorphic to `gr_I(R)` through the
  Rees algebra (surjectivity by splitting off the negative-degree part, and the kernel computed
  coefficientwise as `I · Rees_I(R)` in both directions), the localization at `u` proved to be the
  Laurent polynomial ring, the fibre over `u = 1` proved to be `R` by an explicit division by `u −
  1` inside the extended Rees algebra, and flatness over `k[u]` for a base field `k` proved from
  torsion-freeness through the leading-coefficient argument on polynomials. The scheme `M° = Spec
  R[It, t⁻¹]` therefore carries the affine normal cone as a closed subscheme over the origin, the
  trivial family as the open subscheme over `𝔾_m`, and the original scheme as the fibre over `u =
  1`.
- For every affine ideal, the coordinate map from the normal sheaf to the normal cone is now
  constructed by sending `I/I²` to the degree-one Rees classes and extending through the
  symmetric-algebra universal property.  Its surjectivity is proved from Mathlib's theorem that
  the Rees algebra is generated by the monomials `x t`.  The former
  `AffineNormalConeComparison` record—which allowed a caller to provide both this map and its
  surjectivity, as well as the hard regular-sequence isomorphism—has been removed.
- **The regular-sequence comparison is now proved, in the affine case.**  `Algebra/QuasiRegular.lean`
  proves the classical commutative-algebra theorem that a finite weakly regular sequence in
  Mathlib's sense (`RingTheory.Sequence.IsWeaklyRegular`) is quasi-regular: if `x : Fin n → R`
  is such a sequence, `I = span (range x)`, and `F` is a homogeneous polynomial of degree `d`
  with `F(x) ∈ I^(d+1)`, then every coefficient of `F` lies in `I`.  The proof is the classical
  induction on the length of the sequence: the last element is a non-zerodivisor modulo the ideal
  generated by the previous ones, this is bootstrapped to every power of that ideal, the colon
  computation `I^(d+1) : f = I^d` is derived from it, and the degree induction splits off the
  last variable using `MvPolynomial.optionEquivLeft`.  Nothing about associated graded rings is
  assumed anywhere in that file.
  `Cones/RegularSequence.lean` feeds this into the *existing* canonical map.  Given a
  `RegularGenerators R I` — a wrapper carrying only input data: a length, a family
  `Fin length → R`, a proof that it is a weakly regular sequence, and a proof that it spans `I` —
  it proves `normalSheafCoordinateMap_injective`, that the existing
  `AffineNormalCone.normalSheafCoordinateMap R I : Sym_{R/I}(I/I²) →+* gr_I(R)` is injective.
  Combined with the existing surjectivity theorem this gives a genuine `RingEquiv`
  `normalSheafCoordinateEquiv` (packaged also as an `R/I`-algebra isomorphism
  `normalSheafCoordinateAlgEquiv`), whose forward ring homomorphism is proved (by `rfl`) to be
  that very canonical map, and hence `schemeIsoNormalSheaf`, an isomorphism of schemes whose forward
  morphism is proved to be the existing canonical closed immersion `coneToNormalSheaf R I`; in
  particular `IsIso (coneToNormalSheaf R I)`.  The comparison is proved compatible with the
  degree-one conormal generators, the degree-zero `R/I`-structure maps, the vertex augmentations,
  the projections to `Spec(R/I)`, and the `A^1`-scaling actions (the scaling action on `gr_I(R)`
  is constructed here as the descent of the substitution `t ↦ r t` on the Rees algebra).
  **Scope.**  The theorem proved is affine and takes a chosen finite regular generating sequence
  as input; the sequence must be weakly regular in the given order.  It is *not* a statement
  about arbitrary regular immersions of schemes or stacks, and no Zariski/etale-local or
  stack-level version has been constructed.  The length-one acceptance case (a principal ideal
  generated by a non-zerodivisor) and its instantiation at `(t) subset k[t]` are exported as well.
- For the roadmap's strict nodal test `R = k[x,y]/(xy)` at `I=(x,y)`, the element
  `ι(x̄)ι(ȳ)` is proved nonzero in the actual symmetric algebra by evaluating both conormal
  directions on the explicit dual-number tangent vector `(ε,ε)`.  A Rees-algebra computation
  proves that the canonical map sends it to zero because `xy=0` in `R`.  Hence the actual
  canonical map `Sym(I/I²) → gr_I(R)`, not merely a separately declared quotient model, is
  surjective and noninjective.  The same calculation is also instantiated for the split
  square-zero extension `k⊕kε`.
- The former bivariant-class and operation packages are inactive; their compatibility laws await
  geometric constructions of the underlying operations.
- The former general stack fundamental-cycle, proper-pushforward, flat-pullback, degree,
  homotopy-invariance, Chern, refined-Gysin, localization, exterior-product, and bivariant
  records are inactive.  They accepted one or more of the hard existence, descent, bijectivity,
  or compatibility theorems as fields.  General stack intersection operations therefore remain
  missing rather than conditionally exported.
- The scheme identity cases used by the proper point remain constructed: the rank-zero Gysin
  transport and the actual Rees-cone fundamental cycle.  The represented point's identity atlas
  is also proved pure of relative dimension zero.
- The generic cotangent-object record no longer contains a caller-selected type of local
  presentations, and the unused embedding-comparison record with caller-selected presentation
  and refinement types has been removed.  At the affine level, an actual `Algebra.Extension`
  now definitionally determines its two-term cochain complex and derived localization.  The
  proper-point example separately packages that concrete complex in a field-specific resolution
  whose finite/free predicate and rank are fixed.  Constructing the analogous small-etale
  cotangent object and its comparisons for every actual stack chart remains open.
- The former derived-Picard, intrinsic-cone descent, obstruction geometric-realization, resolved
  stack-cone, and resolution-independence structures are inactive.  Each supplied objects or
  hard comparison theorems that must instead be constructed.  The same is true of the relative
  and functoriality packages.
- For the point, perfectness is a fixed predicate defined by possession of an actual finite-free
  two-term resolution.  The displayed zero resolution proves perfectness, and its derived
  isomorphism to zero proves amplitude `[-1,0]`.  The rank-zero vector-bundle target `[0/0]`, zero
  intrinsic normal sheaf, zero intrinsic cone, identity normal map, closedness, and cone-stack
  comparisons are all constructed directly.
- The former auxiliary scheme-level `ResolvedCone` record is inactive: even after its arbitrary
  Chow-class field was removed, it still accepted the hard homotopy-invariance equivalence as
  data.  The proper-point path instead defines the actual integral Rees cone, its pushed
  fundamental cycle, its quotient Chow class, the ranks of the concrete resolution, and the
  rank-zero Gysin transport separately.  The pushed cone cycle is proved equal to the ordinary
  point fundamental cycle before the Gysin calculation is made.
- `Public.lean` contains no caller-fillable absolute or relative input package.  It exports the
  fully constructed proper-point virtual/fundamental equality and degree-one theorem; general
  entry points will return only after their constructions exist.

## Verification

Run `lake build`.  CI also rejects `sorry`, `admit`, custom `axiom` declarations, and
`native_decide` in project Lean sources.  These checks establish elaboration and the absence of
those explicit placeholders only; they do not show that hard geometric theorems have not been
stored as structure fields.

## Constructed acceptance-test fragments

- `Cones.Examples.NodalNormalCone` constructs the roadmap's node and origin ideal, its Rees
  normal cone and conormal normal sheaf, and a dual-number tangent evaluation.  It proves the
  actual canonical coordinate map `Sym(I/I²) → gr_I(R)` is surjective but not injective by
  exhibiting and independently detecting the nonzero kernel element `ι(x̄)ι(ȳ)`.  Thus the
  canonical normal cone is a proper closed subcone of the normal sheaf without assuming a
  presentation comparison theorem.  `DualNumberNormalCone` supplies a second square-zero test
  of the same reusable canonical-map theorem.
- `Cones.RegularSequence` supplies the positive counterpart.
  `normalSheafCoordinateMap_injective_of_principal` derives injectivity for `I = (a)` with `a` a
  non-zerodivisor directly from the general regular-sequence theorem,
  `coneToNormalSheaf_isIso_of_principal` upgrades it to a scheme isomorphism, and
  `affineLineOrigin_normalSheafCoordinateMap_injective` / `affineLineOriginIso` instantiate this
  at the origin `(t)` of the affine line `k[t]`.  A genuine length-two case is also constructed:
  `planeRegularGenerators` proves that `t, s` is a weakly regular sequence in `k[s][t]` (the second
  step is verified through the explicit identification `k[s][t]/(t) ≅ k[s]`), and
  `planeOrigin_normalSheafCoordinateMap_injective` / `planeOriginIso` deduce the comparison for
  the origin of the affine plane, so the inductive step of the theorem is exercised with a nonzero
  ideal of previous generators.  Together with the nodal and dual-number counterexamples above
  this shows that the regularity hypothesis is substantive: the same canonical map is an
  isomorphism there and strictly non-injective here.
- `IntersectionTheory.PointChow` constructs the closure-dimension grading, canonical
  rational-equivalence system,
  fundamental cycle, and equivalence `A₀(Spec(k))_ℚ ≃ ℚ`; the fundamental class maps to `1`.
- `VirtualFundamentalClass.ProperPoint` starts from the zero ideal of the identity embedding.  A
  coefficientwise proof identifies its Rees algebra with the constants, so its associated graded
  ring and affine normal cone are constructed and proved isomorphic to `Spec(k)`.  The example
  also constructs Mathlib's affine cotangent presentation of `k → k`, proves both terms zero,
  realizes that very presentation as a cochain complex in degrees `-1` and `0`, and defines the
  derived cotangent object as its image under the derived localization functor.  Its isomorphism
  to zero is derived termwise.  The obstruction theory is the identity of this derived object.
  Perfectness is defined by possession of a genuine finite-free two-term resolution and proved
  by the displayed zero resolution; amplitude is proved by applying every homology functor to the
  derived isomorphism with zero.  The identity chain map is proved to localize to the actual POT
  morphism after the resolution comparison.  The resolved cone's two ranks are defined directly
  as the ranks of those actual
  resolution terms, and only then proved zero; the rank-indexed Gysin map and all cycle and
  Chow transports use those computed ranks rather than independent literal zeros.  The
  cohomological dual complex is constructed by reversing and dualizing these
  terms; its quotient groupoid is proved to have a unique object and a unique arrow between every
  pair, so its stabilizer is computed rather than discarded.  The dual identity POT is proved to
  induce the identity functor on this quotient.
- The point's cone Chow class is then constructed by pushing the actual Rees normal cone's
  fundamental cycle through its isomorphism to the point.  The residue-field extension degree is
  proved to be one, and the resolved zero-Gysin formula gives the ordinary fundamental class and
  virtual degree `1`.  The Rees cone's isomorphism (hence closed immersion) into the affine
  normal sheaf `Spec Sym(I/I²)` is induced by the same canonical degree-one Rees map constructed
  for every ideal; its injectivity for the zero ideal is proved from the vanishing of `I/I²`, and
  its compatibility with the two explicit base identifications is proved on coordinate rings.
  The closed immersion used by the Chow calculation is proved to factor through it.  Sections of
  that affine normal sheaf are identified with objects of the actual dual-complex quotient from
  separately proved uniqueness results.  The point's global intrinsic normal sheaf and cone are
  constructed as zero cone stacks, the POT-induced normal map is the identity closed immersion,
  and both are isomorphic as cone stacks to the actual `[0/0]` obstruction target.  The represented
  affine normal sheaf and Rees cone are globally equivalent to that target, with a 2-cell proving
  compatibility of the Rees immersion.  Finally, the displayed Rees cone satisfies the
  categorical pullback universal property along the rank-zero bundle atlas.  This closes the
  point-specific scheme-level path and its zero global cone-stack model.  It does not supply the
  missing general global-stack Picard/cone construction or general resolution independence.

The point-specific scheme-level equality is fully constructed, but it does not discharge the
remaining general scheme/stack Chow, Gysin, cone, independence, and functoriality tasks above.
