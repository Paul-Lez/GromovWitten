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
  families and base-change-stable transport of supplied numerical stability data.  Finiteness of
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
