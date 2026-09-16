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
| 0: spaces and stacks | `Spaces/*`, `Stacks/*` | fppf sheaves, fully faithful schemes and algebraic spaces as discrete stacks, representable properties, constructed binary categorical products and arbitrary categorical pullbacks of algebraic spaces, a constructed algebraic/Deligne--Mumford stack structure on every algebraic space, groupoid fibres, strong-morphism scheme charts, action-torsor groupoids together with their constructed base change along an arbitrary scheme morphism (the underlying fppf sheaf is the actual fibre product, and the group action, the equivariant map to `U`, the principal map, and the fppf-local section — whose cover is the base change of the original cover — are all constructed rather than assumed), which is proved functorial and equipped with identity and composition comparison isomorphisms, the unit and associativity coherence laws, and hence an assembled contravariant pseudofunctor `ActionTorsor.pullbackPseudofunctor` from the locally discrete bicategory of schemes into `Cat` whose fibres are exactly the torsor groupoids, now exported as the quotient prestack `quotientPrestack G U = [U/G]` and the classifying prestack `classifyingPrestack G = BG` (the trivial action on the one-point algebraic space), together with the constructed trivial torsor `G × T` over every scheme, whose left-multiplication action, principal isomorphism and global section are all built so that every fibre of `BG` is nonempty, the proved equivalence of each `BG` fibre with the groupoid `FppfTorsor G T` of fppf `G`-torsors, which commutes strictly with base change, and a genuine strong transformation `ActionTorsor.mapTargetStrongTrans` induced by every equivariant map of `G`-spaces, with all three strong-transformation coherence laws proved, in particular the structure morphism `[U/G] ⟶ BG`; the fppf descent condition of these prestacks, namely descent of arrows and effectivity of descent, remains open, so they are not bundled as `FppfStack`, algebraic/DM stack data, functorial transport of descent data along arbitrary strong transformations (including explicit vertical-composition coherence), a concrete groupoid-valued fibrewise two-pullback pseudofunctor with constructed strong projections and invertible comparison, a proved equivalence between its descent-data category and the genuine two-pullback of the projected descent-data categories, a proved comparison of the canonical global-to-descent functor with the induced pullback of the three component equivalences, and therefore a constructed general fibrewise two-pullback `FppfStack`; the canonical presentation is now equipped with a constructed full bicategorical bilimit proof, including explicit cone lifts, comparison-face coherence, uniqueness isomorphisms, and reconstruction of modifications from compatible projected pairs. Complete scheme presentations now transport across invertible stack 2-cells, stack equivalences are presented by identity scheme maps, representable properties are proved invariant under compatible equivalences of both source and target, any two genuine two-pullback presentations are proved equivalent from their bilimit properties, and multiplicative representable properties are stable under every genuine two-pullback projection with both universal-property uniqueness laws retained. Representable properties now also satisfy honest descent (`Stacks/PropertiesDescent.lean`): any two actual scheme presentations of the same base change are proved to sit in a genuine cartesian square of schemes (`StackMorphismPresentation.isPullback_baseChangeHom`, derived only from the two universal properties together with newly proved composition and target-change coherence for induced comparisons), so a Mathlib scheme-morphism property is independent of the chosen presentation, descends along every class of covers for which Mathlib supplies `MorphismProperty.DescendsAlong`, is local on the test schemes for every `IsZariskiLocalAtTarget` property, and remains compatible with composition, base change, arbitrary genuine two-pullbacks, and equivalences of source and target. fppf, hence also smooth and etale, descent is available for smooth, etale, unramified, locally-of-finite-type, locally-of-finite-presentation, quasi-compact, finite-type, finite-presentation, surjective, open-immersion and isomorphism morphisms; fpqc descent for quasi-compactness is absent from the pinned Mathlib and is proved here (`quasiCompact_descendsAlong_fpqcCover`), which is what makes the finite-type and finite-presentation cases available. Flat, separated, proper, and the immersion properties currently descend only along open covers of the test schemes, because Mathlib supplies no faithfully flat descent for `IsAffineHom`, `IsClosedImmersion`, or `Flat`. Constructed symmetry and left/right identity two-pullbacks, honest atlas-refinement witness records (with general existence still open), and a constructed quotient topology from a chosen smooth atlas and its actual self-overlap also remain available, while general atlas-refinement existence and the former quotient-stack and algebraic-stack-product presentation records remain open or inactive |
| 1: modules and cones | `Sites/*`, `Modules/Stack.lean`, `Cones/Affine.lean`, `Cones/Stack.lean` | distinct stack sites, canonical regular-function sheaves, constructed ringed-site identity/composition and module pullback adjunctions, actual module sheaves, direct sums and canonical finite-free sheaves, symmetric affine cones, Rees normal cones, the proved canonical closed immersion `Spec(gr_I R) → Spec Sym(I/I²)`, the proof that this canonical map is an isomorphism when the affine ideal comes with a chosen finite regular generating sequence (`Cones/RegularSequence.lean`, on top of the neutral commutative-algebra file `Algebra/QuasiRegular.lean`), concrete quotient groupoids, and a constructed rank-zero vector-bundle stack; the former relative-Spec/Proj and derived-Picard theorem packages are inactive |
| 2: rational intersection theory | `IntersectionTheory/*` | scheme cycles graded by actual closure dimension, functorial proper pushforward on those cycle groups, constructed orders of vanishing, canonical rational equivalence, closed-immersion Chow pushforward, the proper-point Chow computation, and a constructed flat pullback along arbitrary open immersions which is proved rational-linear and contravariantly functorial, proved to descend to the rational Chow quotient, and assembled into the right-exact part of the localization sequence: restriction to an open subscheme of a Noetherian scheme is proved surjective through an actual extension-by-zero section, and it is proved to annihilate every class pushed forward from a closed subscheme of the complement; the principal divisor of a rational function is proved to have zero Chow class. General proper descent to Chow groups is still missing: it needs the norm/divisor theorem, whose Mathlib input (norms along finite extensions of function fields, and additivity of `Ring.ord` along a finite local extension) does not exist in v4.33.1. Stack cycle generators, rational functions, and atlas divisor calculations remain experimental and their uncertified quotient and all stack pullback, degree, positive-rank Gysin, and Chern operations are inactive |
| 3: cotangent complexes | `CotangentComplex/*` | Mathlib derived categories, homology-defined amplitude, affine presentation/conormal comparison, flat base change in the affine model, and a constructor sending an actual affine presentation to its derived object; a geometric cotangent complex and its Jacobi--Zariski transitivity triangle are absent, and the arbitrary-predicate global-resolution constructor is inactive |
| 4: cone stacks | `Cones/TwoTermQuotient.lean`, `Cones/Picard.lean`, `Cones/Stack.lean` | actual Picard groupoids, fixed-base groupoid fibres, pullback-natural addition/actions, contraction and stabilizers, chain-homotopy 2-isomorphisms, quasi-isomorphism equivalences, an explicit `[K ≃ K]` acyclic-summand homotopy equivalence, vector-bundle-stack ranks derived from an actual local finite-free matrix quotient presentation, and a constructed rank-zero bundle stack whose fibres are explicitly equivalent to `[0/0]` |
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
