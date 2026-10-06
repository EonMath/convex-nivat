# Source issues and formalization audit

## Current conclusion

The retained source audit identifies one confirmed false inference in the
manuscript: Appendix C.3 tests a factor `A1` but presents the result as a
counterexample for the complete operator `A`. Its narrower computation is
correct. The general assertion in Remark 3.1' is proved here using a different
witness; the printed witness remains invalid for that assertion.

The completion audit of 6 October 2026 records accepted Lean counterparts for
all **49 precise original mathematical results** in sections 0-8 and Appendix D.
The remaining Appendix B announcements and Appendix C experiment records have
separate source limitations below. No finding here refutes Theorems A or B.
This completion claim concerns precise mathematics, not every sentence or
reported computation in the manuscript.

## Source and audit scope

Source: *The Convex Nivat Conjecture: A Complexity Lower Bound for Star
Configurations, and a Reduction from Low Convex Complexity to Star
Configurations*, Apex Intelligence, **12 September 2026**, 37 pages.

- Supplied PDF SHA-256:
  `7fd67831155f4226c010fd6af32de558b76643771e6be12dea4eebafa21745a8`.
- Supplied text extraction SHA-256:
  `1904029d6095db81a40b48a981dcf497b6b8fca36a2d3390a3e4904513f71a44`.
- Accepted paper checkpoint:
  `64cd0ff9359f8a019ec457e0a82fa4add5a914a4`.

Page references are printed manuscript pages. Extraction lines refer only to
the pinned text above. The PDF is identified by hash and is not needed to build
the Lean project. This document consolidates retained source reviews and the
final paper-only accounting audit; it does not claim a new exhaustive referee
review or a fresh compiler run. Build verification is described in
[README.md](README.md).

## Confirmed manuscript issue

### CN-01: C.3 does not refute the full-operator identity

**Location:** Remark 3.1', p. 11, lines 627-632; Appendix C.3, p. 32,
lines 1784-1800. The complete operator is defined on p. 8, lines 437-447.
Historical source finding: SA-08 / SOURCE-I01.

The example uses directions `(1,0)`, `(0,-1)`, `(1,-1)`, zero left tails,
right tail `1[2 divides x]` for component 1, and right tails `1[3 divides x]`
for components 2 and 3. Every tail-colour field is independent of `y`.
Consequently the direction-2 factor `A2 = T^(0,-1) - 1` annihilates every
such field. The product `A` therefore annihilates all eight tail choices,
including the unrealised choices.

C.3 correctly computes a mixed colour difference with values
`(-1,0,1,0,1,0)` modulo 6 and an `A1` image of maximum absolute value 2.
Nevertheless its full-`A` image is zero. A mode surviving one factor can be
killed by another factor; the closing inference from `A1` to `A` is false.

**Correction:** describe C.3 as a limitation of the individual factor `A1`.
To support the full-`A` assertion in Remark 3.1', replace its witness and
verify the complete operator. This repository supplies that separate witness
in `ConvexNivat.remark3_1_prime_full_A_nonextension`, with the full inherited
source context. It does not turn the printed C.3 witness into a valid one.

**Formalization:** the exact zero statements
`ConvexNivat.Appendix.C3.all_tailChoices_fullA_zero` and
`ConvexNivat.Appendix.C3.mixed_fullA_zero` were accepted in the development's
`ConvexNivat.Appendix.C3Arithmetic` diagnostic module. This auxiliary module
is outside the reduced release's main mathematical closure. The different
existential witness is retained in
[FullARemark.lean](convex-nivat/Star/ConvexNivat/SourceGaps/FullARemark.lean).
The accepted explicit C.3 representative fixes strip placements omitted by
the source; it does not identify the missing original script run.

**Impact:** this corrects an illustrative counterexample. It does not affect
the realised-sector Lemmas 3.1/3.2 or the main theorem proofs.

## Source limitations

### CN-02: Appendix B announces seven results without exact contracts

**Location:** Appendix B, p. 29, lines 1651-1663.

The manuscript expressly omits the required notation and proofs and promises
a separate treatment. Its seven announcements concern a lattice-width
identity, consecutive-edge determinant divisibility, propagation on layers,
periods after repeated differences, far-field edge-pattern counts, a short-edge
increment bound, and a general row-length increment bound.

The exact formulas, hypotheses and conventions are unavailable in the supplied
source. They cannot be certified by substituting convenient geometry lemmas.
The two displayed increment bounds also lack the conditions defining the
short-edge case and the general row-length quantity.

**Disposition:** obtain the promised separate statements before treating these
as formalization targets. All seven remain source metadata limitations, with
no proof credit. The manuscript explicitly excludes them from sections 0-8;
they are not blockers for its precise main results.

### CN-03: The original Appendix C experiment package is unavailable

**Location:** Appendix C introduction, pp. 29-30, lines 1665-1674;
C.1-C.2, pp. 30-31, lines 1706-1769; C.3, p. 32, lines 1784-1791.
The empirical final sentence of Remark 7.4, p. 18, lines 1059-1060, refers to
the same experiment records.

The manuscript names `star.py`, `verify.py`, `verify2.py`, `lemma31.py`, three
supplementary checkers and `BUILD.md`, and says their seeded output is supplied
as ancillary material. The original package and complete generated records
were not available to this development. This is a local provenance gap; it
does not establish that the author never supplied them.

Eighteen source records remain unverified: ancillary provenance; the exact
570-component spectral and encoding checks; witness/background computations;
Experiment 1 generation and outputs; Experiment 2 generation, classifications,
six representative rows and aggregate rank/criterion statistics; and the
original C.3 instance, spectrum-run provenance and floating residual.
Seeds and distributions do not determine the original samples without program
versions and random-call order. The C.3 text also omits its strip placements.

**Disposition:** recover and hash the original programs, configuration tables,
encodings, matrices and output before reproducing those exact records. Generic
method proofs, the accepted Observation C.1, and exact C.3 mathematics do not
certify the absent seeded runs. These records are not used as proof evidence
for Theorems A or B.

### CN-04: Preserve the stated meaning of the numerical measurements

**Location:** C.1, p. 30, lines 1685-1722; C.2, p. 31, lines 1764-1767.

The paper itself distinguishes sampled counts from global complexity and
modular ranks from full rational ranks. Agreement of counts in radius-90 and
radius-180 boxes does not establish exhaustive pattern enumeration. An all-zero
box test needs a proved support cover; a numerical spectral threshold needs
the separately claimed exact cyclotomic check. Equal sampled modular rank
increments do not identify the full rational relation space.

**Disposition:** retain these caveats when presenting or reproducing the
experiments. This is an acknowledged verification boundary, not an additional
false theorem. The missing exact records belong to CN-03.

## Cited inputs and proof-method scope

### CN-05: Colle numbering and regional periodicity require precise bindings

**Location:** section 8.2, pp. 20-21, lines 1162-1219.
Historical findings: SA-06 and SA-07.

The citations to Colle refer to the published article
[doi:10.3934/dcds.2023088](https://www.aimsciences.org/article/doi/10.3934/dcds.2023088).
Theorem 1.9 is on published p. 4303; the regional construction occurs in the
proof of Lemma 4.6 on pp. 4323 and 4325. The arXiv v4 numbering differs, so a
same-number substitution would cite a different result. The checked published
PDF has SHA-256
`9ac0a0ef5eeadde742273d3005043b1842d3d012d23465c8ef9db1c7cafc4a1a`.

The source also explicitly bridges overlap periodicity to its stronger
forward-invariant regional convention using recession geometry. Arbitrary
periods on an arbitrary set cannot replace that same-region argument.
Neither finding establishes a missing source bridge or a source contradiction.

The delivered exact paper-use contracts 8.4, 8.6 and 8.7 are proved. The final
route uses the independently checked `NivatTrial` provider; in particular 8.7
is proved by contradiction from its unchanged minimal-counterexample premise
and the provider's full convex theorem. This is an accepted alternative proof
of that exact contract. It is not a reconstruction of Colle's geometric proof,
and completion of Colle's separate article is not a goal of this release.
See [THIRD_PARTY.md](THIRD_PARTY.md) for code provenance.

## Development findings that are not manuscript errata

Earlier audit entries describe real translation hazards and proof work. Their
rejection labels must not be transferred to the paper.

| Retained finding | Correct source or current disposition |
| --- | --- |
| SA-01: Lemma 4.2 needed the standing Case B premise, scalar encoding and subset multiplicities. | These are source dependencies; coincident subset sums must keep their multiplicities. The exact lemma is accepted. |
| SA-02: Lemma 5.2 required full Laurent-field descent, CRT selectors and lattice cosets. | The source supplies the selector construction; individual quotient bases alone were an incomplete Lean route. The exact lemma is accepted. |
| SA-03: Lemma 6.1 needed dimension-two integer decomposition. | The source uses a unimodular triangulation of a lattice polygon. No arbitrary-dimensional claim or counterexample is attributed to it. The lemma is accepted. |
| SA-04: Theorem 8.12 needed every subsequential limit and a finite limit set. | The source supplies those quantifiers and the finiteness argument. The theorem is accepted. |
| SA-05: Appendix D needed the finite-field convex argument, balanced sets and both determination rules. | Appendix D is already proved and supplies Theorem D.1 to Proposition 8.14. It is part of the completed mathematical scope. |
| Colle helper translations omitted positive area, ordered boundary arcs, same-seed opposite edges, branch conditions or orientation; Claim 4.4 used the wrong direction. | These were Lean scaffold/interface defects, with rejected statements preserved in development history. They establish no corresponding source error. |
| Prop-level seed interfaces lost constructive witness data; an extraction packet lost image apostrophes. | These concern interface design and packet generation, not the printed mathematics. |
| HIGH-seed sweeps, hull completion and fixed-patch routes lacked usable same-witness agreement producers. | These are bounded proof-route obstructions in auxiliary Colle work. No full-context counterexample or established source-error verdict resulted. The accepted final route does not depend on completing those routes. |
| Experimental source-rank bindings lacked the original row/script data. | Rejection records CN-03's provenance gap; it does not refute the reported numerical values. |

Historical counts of hundreds of support declarations are not counts of the
paper's results. The source inventory has 60 headings: 49 precise original
results, three aliases, three explanatory remarks with covered mathematical
content, three proved cited usable contracts, and two accepted definitions.
The precise mathematical inventory is complete; the expressly limited B/C
source dispositions above remain separate.
