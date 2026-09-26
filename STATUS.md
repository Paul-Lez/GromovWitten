# Project status

This Lean library develops theorem-backed foundations for the Tau Ceti roadmap on stable
reduction of curves and stable maps.  The implementation follows the roadmap's separation
between scheme-theoretic curve families, models over discrete valuation rings, dual-graph
stability, arithmetic-surface numerical types, and map-decorated graphs.

It also contains the Behrend--Fantechi virtual-fundamental-class development specified by the
[Tau Ceti roadmap comparison](https://github.com/TauCetiProject/TauCetiRoadmap/compare/main...Paul-Lez:TauCetiRoadmap:agent/behrend-fantechi-roadmap).
That development supplies groundwork in groupoid-valued fppf stacks, bicategorical pullbacks,
distinct stack sites with canonical regular-function sheaves, rational Chow gradings, and
derived obstruction theories.  It currently exports the fully constructed virtual class only
for the proper-point acceptance test; the general intrinsic-normal-cone, absolute/relative
virtual-class, and functoriality layers remain under construction.  Its exact layer map and
public entry points are recorded in
[VIRTUAL_FUNDAMENTAL_CLASS_STATUS.md](VIRTUAL_FUNDAMENTAL_CLASS_STATUS.md).

Implemented APIs include:

- affine perfect objects represented by bounded finite-projective complexes, with shifts,
  biproducts, mapping cones, and all three distinguished-triangle closure theorems;
  a scalar-extension functor on projective-perfect derived objects and representative-independent
  Tor amplitude, with supported-representative shift and base-change bounds; locally constant
  integer virtual rank on the prime spectrum of a nontrivial ring, independent of the projective
  representative and compatible with scalar extension; and distinguished-triangle rank
  additivity for the globally finite-free model
  (`CotangentComplex/Projective*.lean`, `PerfectTriangles.lean`);
- finite locally free direct sums with rank addition from independently chosen local bases,
  constructing a common cover from products of charts; finite-free tensor rank multiplication,
  tensor associativity with globally finite-free outer factors, and natural, involutive tensor
  symmetry (`Modules/FiniteLocallyFree.lean`, `Modules/FreeTensor.lean`, `Modules/TensorCoherence.lean`);
- exterior-power functors for module presheaves over varying rings, with their sheaf-valued
  versions constructed by module sheafification and degree-zero/one comparison isomorphisms
  (`Modules/ExteriorPower.lean`);
- fpqc, fppf, and smooth-cover descent for representable flat, separated, proper, and
  closed-immersion stack morphisms, through actual scheme presentations; the scheme-level
  proofs use faithfully flat module descent, diagonal criteria, and proper monomorphisms;
  general immersions also satisfy fppf and smooth-cover descent by descent of the locally
  closed range and closed factor (`Morphisms/*Descent.lean`, `Stacks/*Descent.lean`);
- source-cover tests for representable smooth, etale, formally unramified, flat, locally
  finite-type and locally finitely presented morphisms, using open covers of the actual
  presenting schemes (`Stacks/SourceLocality.lean`);
- a scheme-level `Unramified` morphism class, agreeing on affine spectra with Mathlib's
  ring-theoretic `Algebra.Unramified`, local on source and target, stable under composition and
  arbitrary base change, and satisfied by every immersion;
- fibrewise and field-valued geometric relative-dimension predicates, source and target
  locality, arbitrary base-change stability, and the basic `FamilyOfCurves` package;
- generic and special fibres over a DVR, faithfully flat finite DVR extensions, and models
  with a chosen natural generic-fibre identification and properness-preserving faithful base
  change;
- the local-node algebra `R[x,y]/(xy-πⁿ)`, including its universal property, unique
  axis-supported normal form, its defining equation as a regular singleton sequence over a
  domain, flatness over a DVR, arbitrary coefficient-ring base change
  with its affine fibre-product isomorphism, preservation of affineness, quasi-compactness,
  local finite presentation, and DVR-flatness under that base change, exact dimension one for
  every field-valued node,
  including the two minimal primes and irreducible affine-line components of a positive special
  fibre, and consequently relative dimension at most one and pure relative dimension one for the
  full structural morphism; Laurent-polynomial and standard-smooth
  relative-dimension-one generic fibre for every thickness, and the equation `xy = 0` on
  positive-exponent special fibres; the exact relative Jacobian ideal `(x,y)`, its quotient
  `R/(πⁿ)`, its closed structural immersion with unramified coordinate algebra, an unramified
  structural scheme map with open diagonal, an explicit arbitrary coefficient-base-change
  equivalence for the quotient and an isomorphism over the new base, and empty generic carrier;
  explicit Laurent-polynomial
  descriptions of both coordinate principal opens, each standard smooth of relative dimension
  one, proving that the nonsmooth locus is contained in the Jacobian zero locus; the exact
  tangent-order boundary `xy-πⁿ ∈ (x,y,π)² ↔ 2 ≤ n` for an irreducible parameter; and two
  closed affine-line branches with exact ideals, scheme-theoretic common-origin intersection,
  and transported smooth branch covers after coefficient base change; plus the three
  explicit over-base chart substitutions: the central substitution lowers thickness
  from `k+2` to `k`, while the two side substitutions land in thickness one by scaling one
  coordinate by `π^(k+1)`; all three have proved inverses wherever `π` is invertible and
  commute with arbitrary coefficient base change; the central substitution's `m`-fold
  composite does as well, has its own explicit generic inverse, and is also exposed directly
  as an over-base map from thickness `n` to parity thickness `n%2≤1` after `n/2`
  reductions; plus the graded Rees algebra and Proj blowup, its degree-one affine cover and
  universal principalization maps, and genuine scheme isomorphisms identifying all three node
  charts with Rees charts compatibly with the blowup projection;
- a resolution of the standard node of every thickness over a discrete valuation ring: a
  regular scheme with a proper morphism to the node which is an isomorphism away from the
  closed origin, obtained by induction on the thickness through relative gluing of the
  lower-thickness resolution into the parameter chart of the origin blowup, along the locally
  directed cover of the blowup by that chart, the two side charts, and their overlap;
- regular proper arithmetic surfaces whose numerical data is indexed by the actual irreducible
  components of the scheme-theoretic special fibre, with vertical-divisor intersection,
  resolutions, proper geometric contractions, open-complement isomorphisms, strict component
  decrease, finite contraction chains, and termination at a relatively minimal model;
- finite connected dual multigraphs with loops, valence, arithmetic genus, unpointed
  stability, and relabelling invariance;
- the geometric dual graph of a nodal curve over a field, constructed from the irreducible
  components, the finite discrete set of points without a smooth étale chart, and the finite
  set of points lying on two distinct components, with connectivity derived from connectedness
  of the curve;
- weighted numerical Picard groups, their comparison with the raw intersection cokernel,
  parity and signed-genus formulae, connectedness criteria, the rank-one theorem, and
  finite prime-torsion calculations, together with specialization of genuine relative
  line-bundle classes and prime-to-characteristic Jacobian torsion control;
- conditional semistable- and stable-reduction result types containing actual finite DVR
  extensions and models together with caller-supplied numerical/genus, dualizing-line-bundle,
  graph, and stability witnesses; the resulting genus split and comparison deductions are not
  constructions of semistable reduction, duality, or geometric stability;
- marked maps, target-changing isomorphisms with groupoid laws, functorial marking restriction
  and target postcomposition with identity/composition coherence, base change, evaluation,
  decorated graphs, stability
  inequalities, numerical clutching, evaluation-gated gluing data, and descent of target
  maps through supplied external pushouts and self-coequalizers; plus proper nodal prestable
  families and base-change-stable transport of supplied numerical stability data.  The canonical
  structure-sheaf map exists for every scheme morphism, and its geometric-fibre isomorphism is
  proved for proper geometrically reduced and geometrically connected morphisms; deriving
  geometric reducedness from the existing prestable/nodal hypotheses, the family equivalence,
  and arbitrary base-change comparison remain open.  Finiteness of
  the geometric automorphism group scheme is absent, while stabilization, forgetting, and
  geometric nodal gluing remain conditional outputs of caller-supplied engines;
- the Krull dimension of a nonzero standard-smooth algebra of relative dimension `n` over a
  field is exactly `n`; hence a smooth family of geometric pure relative dimension one is smooth
  of relative dimension one, the relative smooth locus of every locally finitely presented
  family of geometric pure relative dimension one is smooth of relative dimension one, every
  closed section of such a morphism is an effective Cartier divisor, and every marking of a
  pointed prestable family gives an effective Cartier divisor with base-isomorphic subscheme,
  together with the sum of finitely many marking divisors;
- the Krull dimension of a finitely generated domain over a field is its transcendence degree,
  the coheight of a prime of a finitely generated algebra is the transcendence degree of its
  residue field, and the fibre-dimension formula holds for primes lying over primes; hence
  morphisms of schemes locally of finite type over a field satisfy the fibre-dimension
  inequality, and geometric relative dimension bounds add under composition;
- common refinements of finite DVR extensions exist unconditionally, so the former
  common-refinement engine is gone; the normalization of an integral scheme locally of finite
  type over a characteristic-zero field is finite, with nonzero conductor;
- differential Fitting ideals are defined without choosing a presentation, are compatible with
  base change and localization, and glue to a genuine ideal sheaf and closed Fitting locus for
  every locally finitely presented morphism to an affine base; on an étale node chart the first
  Fitting ideal is generated by the two node coordinates;
- equivariant fppf torsors pull back along arbitrary scheme morphisms, with the group action,
  principal map and local triviality constructed, forming a pseudofunctor on the locally
  discrete bicategory of schemes whose fibres are the action-torsor groupoids;
- the affine Rees blowup commutes with flat base change: the base-changed blowup is the
  fibre product of the blowup with the new base, so the blowup of a localized ideal is the part of
  the blowup over the corresponding principal open;
- the blowup of an arbitrary scheme along a quasi-coherent ideal sheaf, glued from the affine
  Rees blowups of its affine opens along the flat restriction maps, with cartesian affine pieces,
  properness over a locally Noetherian base, and the isomorphism away from the centre;
- the blowup of a model of a curve over a DVR along a centre in its special fibre is again a
  model of the same curve, flat by torsion-freeness of the Rees charts and with the generic fibre
  untouched, and the projection is a proper modification of models; finite chains of such
  blowups compose to proper modifications and preserve properness;
- the normalisation of a model of a curve over a DVR is again a model: flatness of the normalisation over
  the DVR is proved unconditionally (flat ⟺ injective into a domain over a Bézout domain, chart by chart on
  Mathlib's normalisation cover), and with finiteness of the normalisation and the generic-fibre isomorphism
  as explicit hypotheses `Model.normalize`/`Model.normalizeModification` are constructed
  (`Curves/StableReduction/ModelNormalization.lean`); the fibre product of two modifications of a model with
  its proper projections and proper structure map (`Curves/StableReduction/CommonModification.lean`);
- `Proj` commutes with arbitrary base change: a graded map which is a base change in every
  degree induces a cartesian square of `Proj`s over the spectra of the base rings, with the
  affine chart comparisons proved bijective by clearing denominators;
- relative `Proj` over an arbitrary scheme, glued from the affine `Proj`s of a quasi-coherent
  graded algebra given on the affine opens, with cartesian affine pieces and properness under
  affine-local finite-type hypotheses;
- relative `Spec` over an arbitrary scheme, glued from the affine spectra of a quasi-coherent
  algebra given on the affine opens, with cartesian affine pieces and an affine structure
  morphism; morphisms of such algebras induce morphisms of relative spectra over the base which
  are closed immersions when the algebra maps are surjective;
- the normal cone `C_{Z/X} = Spec gr_I` and normal sheaf `N_{Z/X} = Spec Sym(I/I²)` of an
  arbitrary quasi-coherent ideal sheaf on an arbitrary scheme, as relative spectra whose affine
  pieces are the affine constructions, together with the closed immersion of the normal cone
  into the normal sheaf over the base; the transition squares are proved from flat base change of
  Rees algebras, of ideals, and of symmetric algebras;
- Vistoli's lemma in the polynomial model: for an ideal `I` of `R = A[x_σ]`, the translation
  action of the tangent bundle `T_{𝔸^σ}|_U = U × 𝔸^σ` on the normal sheaf `Spec Sym(I)/I·Sym(I)`
  preserves the normal cone `Spec gr_I(R)`: the coaction `gr_I(R) → gr_I(R)[ε]`, obtained by
  translating the deformation space `x ↦ x + ε t⁻¹` and restricting to the special fibre,
  satisfies the unit and associativity laws and is compatible with the normal-sheaf coaction
  through the surjection `Sym(I)/I·Sym(I) ↠ gr_I(R)`;
- the affine intrinsic normal sheaf: the quotient groupoid `[N_{U/M}/T_M|_U]` of the normal sheaf
  by the tangent bundle is isomorphic, over every test algebra and compatibly with reindexing and
  contraction, to the `h¹/h⁰` Picard groupoid of the dual of the presentation complex
  `[I/I² → Ω ⊗ R/I]`, with `Sym(M × N) ≃ Sym(M) ⊗ Sym(N)`;
- the affine Behrend--Fantechi criterion: a map of two-term complexes is an obstruction theory
  (`H⁰` bijective, `H⁻¹` surjective) if and only if the induced map of `h¹/h⁰` groupoids of dual
  points is fully faithful over every test algebra (the converse using trivial square-zero
  extensions), with the obstruction cone as the image of a cone inside the normal sheaf;
- flat local extensions with `m_R·S = m_S` preserve the order of vanishing without any
  unramifiedness, giving the equality of orders at bundle points and the principal-divisor
  comparison `π^* div(f) = div(π^* f)` for the flat pullback along an affine vector bundle over
  an integral Noetherian base;
- the flat pullback along an affine vector bundle descends to rational Chow groups,
  `A_i(Spec R) → A_{i+r}(E)`, for every Noetherian base, through the affine presentation of an
  integral closed subscheme as `Spec (R ⧸ p)` and the base change of the bundle along it;
- the dimension formula `dim W = dim U + r` for a flat morphism of pure relative dimension `r`
  between schemes locally of finite type over a field, and hence the atlas independence of the
  dimension of an algebraic stack whose atlases are locally of finite type over a field, the
  second projection of the overlap of two atlases being handled by the leg-exchange of chart
  pullback presentations;
- the global normal cone of an ideal sheaf locally generated by a quasi-regular sequence is the
  normal sheaf, the normal sheaf is the abelian hull of the normal cone, and both cones map to
  the closed subscheme; products and fibre products of affine cones and cone actions, and
  smoothness of `Spec Sym F` for every finite projective `F`;
- the dual of a perfect complex is well defined up to canonical isomorphism, with biduality and
  full faithfulness of duality on strictly perfect complexes;
- the underlying topological space of an algebraic stack is independent of the atlas: the point
  spaces of any two smooth surjective charts are canonically homeomorphic, compatibly with the
  point maps and with the cocycle law, and the stack represented by a scheme has that scheme as
  its underlying space;
- flat pullback of cycles along étale morphisms, étale presentation groupoids with their
  Vistoli cycles and Chow groups, and the first Vistoli rational Chow group of a Deligne--Mumford
  stack from the self-overlap of its chosen étale atlas;
- exactness of the localization sequence of rational Chow groups in the middle, through the
  closure of an integral closed subscheme of an open subscheme (the scheme-theoretic image) and
  the restriction of cycles supported on a closed subscheme, conditional only on the gradedness
  of principal divisors;
- binary products of stacks and of stack morphisms with a one-dimensional universal property,
  the 2-commuting diagonal square of a chart, and the reduction of one direction of the
  Deligne--Mumford diagonal criterion to two named representability hypotheses;
- coherent cohomology `Hⁿ(X, M)` of `𝒪_X`-modules as Mathlib's `Ext`-theoretic sheaf
  cohomology, with its `Γ(X, 𝒪_X)`- and `k`-module structure constructed from multiplication
  by global functions and additivity of the cohomology functor; the arithmetic genus
  `dim_k H¹(X, 𝒪_X)` of a curve over a field, with `H⁰ = Γ` as a linear isomorphism,
  isomorphism-invariance, invariance under field extension from the base-change dimension
  formula, the locally-free-rank characterization, and the normalization formula
  `p_a(X) = p_a(X̃) + δ` agreeing with the dual-graph genus; finite-dimensionality, the
  long exact sequence and flat base change remain hypotheses because Mathlib lacks them;
- higher direct images of abelian sheaves are genuine right derived functors of pushforward,
  with `R⁰ f_* = f_*` and the degree-zero base-change comparison identified with the canonical
  Beck--Chevalley morphism;
- the rank of a strictly perfect complex is invariant under homotopy equivalence, so the rank
  of a perfect object of the derived category and of its dual is unconditionally well defined;
- the dimension formula `dim (A ⧸ p) + ht p = dim A` for finitely generated domains over a
  field, hence the purity of the affine normal cone `Spec (gr_I R)` of a proper ideal of an
  `n`-dimensional finitely generated domain (Fulton B.6.6), and the grading of `gr_I R` by
  orthogonal degree projections with the degree-zero and degree-one parts identified;
- the elementwise quasi-isomorphism predicate of two-term complexes agrees with Mathlib's
  `QuasiIso`, short exact sequences of two-term complexes give distinguished triangles and
  conversely, the resolution-independence equivalence of `h¹/h⁰` is canonical up to natural
  isomorphism, `h¹/h⁰` extends to arbitrary derived objects by two-term truncation with
  independence of the representative proved by roofs of quasi-isomorphisms, a complex of finite
  projectives exact outside `[-1,0]` has `h¹/h⁰` a fibrewise vector-bundle stack, and split short
  exact sequences of two-term complexes dualise to short exact sequences of Picard groupoids;
- the affine cone quotient `[C/E]` is realised as a torsor prestack (fully faithful comparison
  with the trivial torsors), base changes and fibre products of cone stacks are constructed on
  genuine two-pullbacks of stacks, unconditionally for coherent cone stacks;
- the tangent action on the affine normal cone is an honest `ConeAction` (Vistoli's lemma in
  cone-action form), with the lci specialisation `𝔠 = 𝔑` and the smooth specialisation
  `𝔠 = B T_M` fibrewise, invariance under scalar extension, and `dim C − rank T = 0`;
- the refinement lemma for local embeddings (`C_{U/M × 𝔸^τ} = C_{U/M} × 𝔸^τ` equivariantly,
  and the quotient groupoids `[C/T]` unchanged by the refinement) and the independence of the
  embedding with the Behrend--Fantechi cocycle condition, in the polynomial model; the product
  formula for normal cones with the comparison map surjective and its injectivity reduced to a
  finite-sum distributivity statement;
- the intrinsic pullback sequence of Picard groupoids for a tower `R → S → T`, unconditional
  when `S` is formally smooth over `R` and `T` is flat and formally smooth over `S`;
- obstruction cones of the affine intrinsic normal cone inside `h¹/h⁰(Eᵛ)` (fibrewise closed
  immersions), the identification of the two-term obstruction-theory criterion with the derived
  one, virtual rank, external sums and base change of obstruction theories, invariance under
  derived isomorphism, and the deformation-theoretic meaning: the obstruction of `E` vanishes iff
  the square-zero lift exists, lifts are a torsor under `Ext⁰(E, J)`, the lifting groupoid is the
  torsor of trivialisations of the obstruction object, the obstruction space at a point is a
  universal obstruction space, and curvilinear obstructions form a `κˣ`-stable cone containing
  the origin;
- descent of morphisms and effective descent of fppf sheaves over a base along any covering sieve
  (no sheafification), the reduction of fppf covering sieves to small covering families, and the
  gluing infrastructure for the quotient prestack `[U/G]`;
- effective descent of actual scheme morphisms along a surjective étale cover from an explicit
  over-base kernel-pair equation, descent of actual local inverse maps to scheme isomorphisms,
  coherence with one arbitrary base change, and globalization/uniqueness of supplied contraction
  factorizations (`AlgebraicGeometry/Descent/{EtaleMorphisms,SchemeIsomorphisms,BaseChange,Contractions}.lean`).
  This morphism layer does not construct descended polarized schemes, line bundles, polarization
  isomorphisms, graded section algebras, `Proj`s, or a contraction universal property.
- fppf descent for the quotient prestack `[U/G]`: descent of morphisms and effectiveness of
  descent along every fppf covering sieve, proved with explicit fibre-product data and without
  sheafification (`Stacks/TorsorStackDescent.lean`, `Stacks/TorsorStackEffective.lean`,
  `Stacks/TorsorStackCover.lean`), the sheaf-theoretic input `SheafDescentInput` proved
  (`Stacks/SieveDescentEffective.lean`), and, through repository-local proof-irrelevance versions
  of Mathlib's descent lemmas that avoid the kernel wall (`Stacks/TorsorStackMathlib.lean`),
  Mathlib's `Pseudofunctor.IsStack` for `[U/G]`, so `[U/G]` and `BG` are bundled as stacks in
  groupoids (`Stacks/TorsorStackBundle.lean`; at the fibre universe of torsors, one above the
  repository's `FppfStack`);
- the pushout `r_* P` of an fppf torsor along a homomorphism of group objects, constructed by
  descent with all torsor axioms proved (`Stacks/TorsorPushout.lean`), and the `𝔸¹`-contraction
  of `[C/E]` on trivialised torsors with its five coherence laws
  (`Cones/QuotientTorsorStack.lean`);
- coherence of fibre products of coherent cone stacks, the fibre universal property of the
  product, the pasting law for genuine two-pullbacks of stacks and the composition half of the
  pseudofunctoriality of base change (`Cones/StackProdCoherence.lean`,
  `Cones/StackBaseChangeComp.lean`);
- the product formulas `C_{U×U'/M×M'} ≅ C_{U/M} × C_{U'/M'}` and
  `N_{U×U'/M×M'} ≅ N_{U/M} × N_{U'/M'}` over a field, with no remaining hypothesis
  (`Cones/NormalConeProductInj3.lean`, `Cones/NormalSheafProduct.lean`);
- the normal-sheaf refinement lemma `N_{U/M×𝔸^τ} = N_{U/M} × 𝔸^τ`, the equivalence of the
  normal-sheaf quotient groupoids and the presentation-independence package with cocycle for
  normal sheaves (`Cones/RefinementNormalSheaf.lean`);
- the tangent action on the affine normal cone beyond the polynomial model: for every flat
  algebra over the polynomial ring with an extended ideal by flat base change
  (`Cones/SmoothAmbient.lean`), and for an arbitrary ideal of a formally étale chart by Taylor
  lifts, with counit, coassociativity, the point action, the normal-sheaf coaction, Vistoli's
  lemma, the `ConeAction` packaging via the Kähler differentials of the chart, the obstruction
  cone, and agreement with the polynomial model (`Cones/SmoothAmbientEtale.lean`,
  `Cones/SmoothAmbientEtaleAction.lean`, `Cones/SmoothAmbientEtaleConeAction.lean`);
- the prestack-level gluing of the intrinsic normal cone: abstract two-descent data of groupoids
  with the glued groupoid and every chart inclusion an equivalence, its instance for families of
  polynomial presentations with the Behrend–Fantechi cocycle, strict functoriality in the test
  algebra, gluing over covers of flat charts, and Zariski descent in the test algebra
  (unconditional for finite covers) (`Cones/IntrinsicConeGluing.lean`,
  `Cones/IntrinsicConeGluingPoly.lean`, `Cones/IntrinsicConeGluingCover.lean`,
  `Cones/IntrinsicConeDescent.lean`);
- Fulton's Proposition 1.9 for trivialised affine vector bundles over Noetherian rings: the flat
  pullback `π^* : A_i(X) → A_{i+r}(E)` on rational Chow groups is surjective, proved through the
  rank-one key lemma (a rational function on `Spec (R/p)[X]` with principal divisor `[V]` plus
  cycles over a proper closed subset), Noetherian induction on the base and induction on the
  rank, under homogeneity of principal divisors on the total space only
  (`IntersectionTheory/BundleHomotopyRankOne.lean`, `IntersectionTheory/BundleHomotopy.lean`,
  `IntersectionTheory/BundleHomotopyKey.lean`); the zero-section Gysin isomorphism
  `0^! = (π^*)^{-1}` is defined under the explicit hypothesis that `π^*` is injective, which is
  the Chern-class half of homotopy invariance and remains the one missing intersection-theoretic
  input;
- the Behrend–Fantechi resolved cone `C(E) = 𝔠_X ×_{h¹/h⁰(E^∨)} E₁` in the affine two-term model,
  as the scheme-theoretic image of `C_{U/M} ×_U E₀ → E₁`, with its closed immersion into `E₁`,
  translation invariance under `E₀`, the comparison with the obstruction-cone functor on test
  algebras, the trivialisation of the tangent torsor `C_{U/M} ×_U E₀ → C(E)` by the invariant
  ideal lemma and Vistoli's coaction, and purity of `C(E)` in dimension `rk E⁰` under the
  dimension formula for the extended Rees algebra
  (`VirtualFundamentalClass/ResolvedCone.lean`, `VirtualFundamentalClass/ResolvedConeDimension.lean`,
  `VirtualFundamentalClass/ResolvedConeTrivialisation.lean`);
- the virtual fundamental class `[X]^vir = 0^!_{E₁}[C(E)]` in the affine model with a global
  two-term resolution: the resolved-cone class in `A_{vd + rk E⁻¹}(E₁)`, the canonical class in
  `A_{vd}(X) ⧸ ker π^*` with no injectivity assumption, the class in `A_{vd}(X)` characterised by
  `π^*[X]^vir = [C(E)]` once `π^*` is injective, the expected dimension
  `vd = rk E⁰ − rk E⁻¹` as a chain-homotopy invariant, the rank-zero and proper-point checks, and
  independence of the resolution under isomorphisms of two-term resolutions and under adding
  an acyclic summand `[F = F]` (`C(E ⊕ [F = F])` is the preimage of `C(E)`, with the flat
  pullback of fundamental cycles along a vector bundle proved by base change of lengths)
  (`VirtualFundamentalClass/Construction.lean`, `VirtualFundamentalClass/Independence.lean`,
  `VirtualFundamentalClass/IndependenceAcyclic.lean`);
- injectivity of the flat pullback `π^* : A_i(X) → A_{i+r}(E)` along a trivialised affine vector
  bundle over a Noetherian ring, without Chern classes: a generic translate `{t = c}` of the zero
  section (`UnitDifferences R`: an infinite set of elements of `R` with unit differences, e.g. an
  infinite field inside `R`) gives a cycle-level Gysin map `i_c^*` with `i_c^* ∘ π^* = id`
  (`IntersectionTheory/BundleSectionGysin.lean`), and `i_c^*` kills every principal divisor in
  good position by Fulton's symmetric local identity in two-dimensional local domains
  (Appendix A.2–A.3: Koszul symmetry and dévissage, proved unconditionally in
  `IntersectionTheory/LocalOrdSymmetry.lean`, lifted to cycles in
  `IntersectionTheory/BundleSectionGysinIdentity.lean`); with rank induction along the tower this
  gives `VectorBundle.chowPullbackBundle_injective` and the honest zero-section Gysin isomorphism
  `A_{i+r}(E) ≃ A_i(X)` (`IntersectionTheory/BundleHomotopyInjective.lean`) under the catenarity
  hypothesis `HasUniversalDimensionFormula R` (the dimension formula for all prime quotients of
  all polynomial rings over `R`, true for finite-type algebras over a field but not yet proved in
  the repository), which also discharges the round-14 homogeneity hypothesis on principal
  divisors;
- chain-homotopy invariance of the virtual fundamental class in the affine model: the
  resolved-cone ideal depends on the obstruction theory only through its degree `−1` component,
  and a degree-zero chain homotopy is absorbed by a translation automorphism of
  `gr_I(R) ⊗ Sym(E⁰)`, so homotopic obstruction theories have literally the same resolved cone
  (`VirtualFundamentalClass/HomotopyInvariance.lean`); a quasi-isomorphism `f : E → F` of perfect
  two-term complexes yields an isomorphism `F ⊕ [E⁰ = E⁰] ≅ E ⊕ [F⁰ = F⁰]` compatible with the
  obstruction maps up to such a homotopy (`VirtualFundamentalClass/QuasiIsoSplitting.lean`), and
  combining this with the round-14 isomorphism and acyclic-summand invariance proves
  Behrend–Fantechi Proposition 5.3 in the affine model, `[X]^vir_φ = [X]^vir_ψ` for
  quasi-isomorphic (or homotopy-equivalent) obstruction theories
  (`VirtualFundamentalClass/QuasiIsoInvariance.lean`); the virtual class and its invariance are
  restated with the two ring hypotheses `HasUniversalDimensionFormula (R ⧸ I)` and
  `UnitDifferences (R ⧸ I)` as the only inputs beyond round 14's construction
  (`VirtualFundamentalClass/Unconditional.lean`);
- the virtual fundamental class in the affine model with no ring-theoretic hypotheses at all: the
  dimension formula for prime quotients of polynomial algebras over a finitely generated algebra
  over a field (`VectorBundle.HasUniversalDimensionFormula`, proved in
  `Algebra/FiniteTypeDimensionFormula.lean` from the height-one case already in
  `Algebra/DimensionFormula.lean`) and the unit-difference condition for an infinite field
  discharge the two inputs of round 15, so `VirtualFundamentalClass/OverField.lean` states the
  construction, its uniqueness, its quasi-isomorphism invariance and the purity of the resolved
  cone for `[Field k] [Infinite k] [Algebra.FiniteType k R]` only;
- relative obstruction theories over a smooth polynomial base (Layer 9, affine model): for
  `X ⊆ 𝔸^σ × 𝔸^τ` and an obstruction theory relative to `Y = 𝔸^τ`, the absolute obstruction
  theory of Behrend–Fantechi §7 is constructed (`RelativeAbsolute.absHom`), its resolved cone is
  literally the resolved cone of the relative datum (the tangent coaction in the `τ`-directions
  absorbs the extra differential; `ideal_absHom`), its virtual class is the relative virtual class
  in degree `vd + dim Y` (`virtualClassAt_absHom`), and it is an obstruction theory exactly when
  the relative datum is (`isObstructionTheory_absHom_iff`,
  `VirtualFundamentalClass/RelativeAbsolute*.lean`); adjoining a degree-one summand leaves the
  resolved cone unchanged in general (`VirtualFundamentalClass/DegreeOneSummand.lean`);
- functoriality under the smooth projection `X × 𝔸^τ → X` (Layer 8, affine model): the flat
  pullback along a trivialised bundle is transitive on Chow groups, commutes with pushforward along
  closed immersions and with the zero-section Gysin map
  (`IntersectionTheory/BundlePullbackBaseChange.lean`); the base change of an obstruction datum
  is constructed, its resolved cone is the polynomial extension of the original one
  (`VirtualFundamentalClass/BaseChangeCone*.lean`), and the virtual class of the base change is
  the flat pullback of the virtual class, `[X × 𝔸^τ]^vir = π^*[X]^vir` in the relative form
  (`BaseChangeInvariance.virtualClassAt_baseChangeHom`; Behrend–Fantechi, Proposition 7.2 for
  this smooth projection); the transfer of the obstruction-theory property along the base change
  is still stated separately and not yet proved;
- global intersection-theory foundations for the virtual class of a general scheme (Layer 2):
  rational cycles are Zariski-local (`IntersectionTheory/CycleGluing.lean`: a cycle is determined
  by its restrictions to an open cover, compatible local cycles glue, the fundamental cycle
  restricts to the fundamental cycle along open immersions); homogeneity of principal divisors is
  a Zariski-local property, characterised by the certified dimension dropping by one along the
  covering relation of the specialisation order and verified affinely from the dimension formula
  (`IntersectionTheory/HomogeneityLocal.lean`); for a scheme locally of finite type over a field
  the dimension function is the transcendence degree of the residue field, compatible with every
  open immersion (`IntersectionTheory/FiniteTypeDimension.lean`);
- vector bundles over a general scheme (Layer 1/2): the total space `Spec_X 𝒜` of a quasi-coherent
  algebra with an augmentation and trivialisations `𝔸^ι_U` over an affine cover
  (`VectorBundleTotalSpace.lean`: affine projection, zero section as a closed immersion, chart
  pullback squares), the restriction of a relative `Spec` to an open subscheme with the pullback
  square `Spec_V (𝒜|_V) = Spec_X 𝒜 ×_X V` and its corollary for the global normal cone
  (`RelativeSpecRestrict.lean`), the flat pullback of cycles `π^* : Z_*(X) → Z_{*+r}(E)` defined
  through the chart-independent generic points of the fibres, agreeing with the affine pullback on
  every chart, injective and taking the fundamental cycle to the fundamental cycle
  (`IntersectionTheory/BundlePullbackGlobal.lean`, `BundlePullbackFundamental.lean`); the
  restriction `E_V = E ×_X V` to an integral closed subscheme is an integral closed subscheme with
  dominant projection (`IntersectionTheory/BundleOverSubscheme.lean`), the identity
  `π^*(ι_V)_* div f = (ι_{E_V})_* div(π_V^* f)` holds, and hence `π^*` descends to rational Chow
  groups, `chowPullbackBundleGlobal : A_i(X) → A_{i+r}(E)`, restricting on every chart to the affine
  `chowPullbackBundle` (`IntersectionTheory/BundlePullbackGlobalChow.lean`); injectivity and
  surjectivity of the global `π^*` on Chow groups (Fulton 1.9, 3.3(a)) are not yet proved beyond an
  affine base;
- the virtual fundamental class of a general scheme (Layer 7): the affine resolved cone commutes
  with flat formally étale base change, in particular with localisation at an element, and the
  obstruction-theory property transfers along it and along the round-16 polynomial base change,
  with faithfully flat converses (`VirtualFundamentalClass/LocalisationCone.lean`,
  `BaseChangeObstruction.lean`); a global cone datum `GlobalConeData` (bundle, cone algebra, closed
  immersion `C ↪ E₁`, affine models on charts) has a global cone cycle `[C] ∈ Z_*(E₁)` which
  restricts on every chart to the affine resolved-cone cycle (`VirtualFundamentalClass/GlobalCone.lean`);
  the global virtual class `[X]^vir` is defined as the unique class with `π^*[X]^vir = [C]` for the
  global Chow pullback, under the two remaining hypotheses that `π^*` is injective on `A_*(X)` and
  that `[C]` lies in its range (`VirtualFundamentalClass/GlobalVirtualClass.lean`); for an affine
  scheme with the single chart `⊤` the global data are constructed from an affine obstruction datum
  and the global class is the affine class of round 16, with both hypotheses discharged
  (`VirtualFundamentalClass/GlobalConeAffine.lean`); the construction of `GlobalConeData` from a
  global embedding or from local embeddings (gluing of the cones on overlaps) is not yet done;
- the global homotopy property of vector bundles (Layer 2): Fulton's Proposition 1.9 for an
  arbitrary `BundleData X ι` over a compact locally Noetherian base, proved by well-founded
  induction on closed subsets with the supports of cycles and relations tracked
  (`IntersectionTheory/SupportedCycles.lean`, `BundleHomotopyClosed.lean`,
  `BundleHomotopyGlobal.lean`: `chowPullbackBundleGlobal_surjective`, hypothesis-free for
  schemes of finite type over a field); injectivity of the global `π^*` (Fulton 3.3(a)) for
  bundles with a global trivialisation over a compact scheme locally of finite type over an
  infinite field, by a global constant translate of the zero section, the invariance of principal
  divisors under the choice of the reduced subscheme (`GeneratorInvariance*.lean`), a global
  section Gysin map glued from the affine one (`LineBundleInjective*.lean`) and rank induction
  through the trivial tower (`BundleHomotopyInjectiveGlobal.lean`:
  `chowPullbackBundleGlobal_injective`); injectivity for non-trivial bundles needs Chern classes
  and is not attempted;
- relative `Spec` of an affine morphism and trivial bundles (Layer 1): `AlgebraData.ofAffineHom`,
  `relativeSpecOfAffineHomIso`, morphisms of relative `Spec`s from morphisms over the base
  (`RelativeSpecAffineHom.lean`); `trivialData X ι`, `GlobalTrivialisation`, constant sections and
  the rename tower (`VectorBundleTrivial.lean`);
- the global cone from local embeddings and the unconditional virtual class (Layer 7): a
  `LocalConeData` (affine obstruction models on charts whose resolved-cone ideals agree on the
  affine opens of the overlaps) glues to a closed subscheme of the total space via the kernel
  ideal sheaf of the map from the disjoint union of the affine cones, whose ideal on every chart
  is the affine resolved-cone ideal, hence to a `GlobalConeData`
  (`VirtualFundamentalClass/ConeGluing.lean`, `ConeGluingGlobal.lean`); the overlap condition
  follows from flat formally étale base change of the affine models plus a transition datum
  (`ConeGluingCompatible.lean`); the membership hypothesis of round 17 is discharged by the
  global surjectivity, so `virtualClassFT'` is the virtual class of a compact scheme locally of
  finite type over a field with no hypothesis, and it is the unique class with `π^*[X]^vir = [C(E)]`
  when the obstruction bundle has a global trivialisation
  (`GlobalVirtualClassSurjective.lean`, `GlobalVirtualClassUnconditional.lean`);
- executable worked examples for the combinatorial acceptance cases.

Some classical existence results beyond the pinned Mathlib snapshot currently appear only as
typed caller-supplied construction engines.  Their outputs contain actual schemes, morphisms,
line bundles, colimits, and isomorphisms, but supplying an engine is a dependency boundary—not a
formalization of the existence or geometry it assumes.  Results depending on such engines are
conditional and do not count as completed roadmap items.  No placeholder proofs or custom axioms
are used; see [ROADMAP_STATUS.md](ROADMAP_STATUS.md) for the exact construction boundary and audit
result.

The specification is [TauCetiRoadmap PR #142](https://github.com/TauCetiProject/TauCetiRoadmap/pull/142).

## Build

Install the Lean toolchain selected by `lean-toolchain`, then run:

```console
lake update
lake build
```

Project warnings are treated as errors, so placeholder proofs and linter regressions fail this
build.
