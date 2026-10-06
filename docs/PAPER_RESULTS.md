# Paper result index

The table maps the supplied manuscript to the retained Lean declarations. Start with [MainTheorem.lean](../MainTheorem.lean); the headline result is `ConvexNivat.convexNivat` (8.18).

There are 49 distinct precise original results. The 60 headings also include three introductory aliases, three explanatory remarks, three cited contracts, and two definitions. The source correspondence was accepted before packaging; module identities and statements are preserved.

| Source | Result | Lean declarations |
| --- | --- | --- |
| A | Introductory alias of 7.3 | [`ConvexNivat.theoremT`](../Star/ConvexNivat/MainTheorem.lean) |
| B | Introductory alias of 8.18 | [`ConvexNivat.convexNivat`](../Reduction/ConvexNivat/OriginalMain.lean) |
| T | Main theorem alias of 7.3 | [`ConvexNivat.theoremT`](../Star/ConvexNivat/MainTheorem.lean) |
| 0.1 | Absorbing a doubly periodic background | [`ConvexNivat.remark0_1_absorb_background`](../Star/ConvexNivat/SourceGaps/PeriodicBackground.lean)<br>[`ConvexNivat.remark0_1_background_complexity`](../Star/ConvexNivat/SourceGaps/PeriodicBackground.lean) |
| 1.1 | Finite support after differencing a local observable | [`ConvexNivat.lemma_1_1_support_bound`](../Star/ConvexNivat/StarFiniteSupport.lean)<br>[`ConvexNivat.lemma_1_1`](../Star/ConvexNivat/StarFiniteSupport.lean) |
| 1.2 | Laurent action is faithful on nonzero finite support | [`ConvexNivat.lemma_1_2`](../Algebra/ConvexNivat/OperatorFiniteSupport.lean) |
| 1.3 | Case A complexity bound | [`ConvexNivat.proposition_1_3`](../Star/ConvexNivat/StarFirstCase.lean) |
| 1.4 | Dichotomy independent of period multiples | [`ConvexNivat.starDifference_dichotomy_independent`](../Star/ConvexNivat/StarFirstCase.lean) |
| 2.0 | Fourier spectral projection, all four parts | [`ConvexNivat.spectral_projection_row_formula`](../Spectral/ConvexNivat/SpectralFourier.lean)<br>[`ConvexNivat.spectral_projection_complete`](../Spectral/ConvexNivat/SpectralFourier.lean)<br>[`ConvexNivat.spectral_projection_eigen`](../Spectral/ConvexNivat/SpectralFourier.lean)<br>[`ConvexNivat.spectral_projection_translate`](../Spectral/ConvexNivat/SpectralFourier.lean)<br>[`ConvexNivat.spectral_occurs_iff_row`](../Spectral/ConvexNivat/SpectralFourier.lean)<br>[`ConvexNivat.spectral_projection_polynomial_action`](../Spectral/ConvexNivat/SpectralLaurentBridge.lean)<br>[`ConvexNivat.spectral_projection_commutes_laurent`](../Spectral/ConvexNivat/SpectralLaurentBridge.lean)<br>[`ConvexNivat.spectral_laurent_row_formula`](../Spectral/ConvexNivat/SpectralLaurentBridge.lean) |
| 2.1 | Exceptional spectrum is nonempty | [`ConvexNivat.exceptional_spectrum_nonempty`](../Star/ConvexNivat/StarSpectral.lean) |
| 2.1prime | Galois stability and integral coefficients | [`ConvexNivat.exceptional_spectrum_galois_stable`](../Spectral/ConvexNivat/SpectralGalois.lean)<br>[`ConvexNivat.exceptional_univariate_integer_coefficients`](../Spectral/ConvexNivat/SpectralCyclotomic.lean)<br>[`ConvexNivat.exceptional_univariate_cyclotomic_factors`](../Spectral/ConvexNivat/SpectralCyclotomic.lean)<br>[`ConvexNivat.exceptional_polynomial_integer_coefficients`](../Spectral/ConvexNivat/SpectralIntegerLaurent.lean) |
| 2.2 | Spectrum-preserving injective integer encoding | [`ConvexNivat.spectrum_preserving_integer_encoding`](../Star/ConvexNivat/StarSpectral.lean) |
| 2.3 | One-sided vanishing forces a line factor | [`ConvexNivat.one_sided_spectral_divisibility`](../Spectral/ConvexNivat/SpectralDivisibility.lean) |
| 2.4 | Divisibility of every scalar affine relation | [`ConvexNivat.affine_relation_divisible`](../Spectral/ConvexNivat/AffineRelationConsumer.lean) |
| 2.5 | Affine dimension budget | [`ConvexNivat.affine_observable_dimension_budget`](../Spectral/ConvexNivat/AffineDimensionConsumer.lean) |
| 2.6 | Empty erosion branch and degenerate windows | [`ConvexNivat.erosion_placement`](../Geometry/ConvexNivat/Geometry/Basic.lean)<br>[`ConvexNivat.erosion_eq_empty_of_empty_interior`](../Geometry/ConvexNivat/Geometry/Basic.lean)<br>[`ConvexNivat.remark2_6_empty_erosion_dimension_join`](../Star/ConvexNivat/SourceGaps/DimensionJoin.lean)<br>[`ConvexNivat.remark2_6_empty_erosion_complexity`](../Star/ConvexNivat/SourceGaps/DimensionJoin.lean)<br>[`ConvexNivat.remark2_6_empty_interior_complexity`](../Star/ConvexNivat/SourceGaps/DimensionJoin.lean) |
| 3.0 | Realised sector adjacency | [`ConvexNivat.sectors_adjacent_signs`](../Geometry/ConvexNivat/SectorGeometry.lean)<br>[`ConvexNivat.sectors_adjacent_backgrounds`](../Geometry/ConvexNivat/SectorGeometry.lean)<br>[`ConvexNivat.realised_sectors_cycle`](../Star/ConvexNivat/SectorCycle.lean) |
| 3.1 | One common realised-tail background | [`ConvexNivat.exceptional_polynomial_ray_backgrounds_equal`](../Star/ConvexNivat/SectorRayEquality.lean)<br>[`ConvexNivat.realised_sector_applied_backgrounds_equal`](../Star/ConvexNivat/SectorConnectivity.lean)<br>[`ConvexNivat.appliedSectorBackground`](../Star/ConvexNivat/SectorSpectralDefinitions.lean)<br>[`ConvexNivat.applied_sector_background_doubly_periodic`](../Star/ConvexNivat/SectorPeriods.lean) |
| 3.1prime | Warning about unrealised tail choices | [`ConvexNivat.remark3_1_prime_full_A_nonextension`](../Star/ConvexNivat/SourceGaps/FullARemark.lean) |
| 3.2 | Finite error support for A eθ | [`ConvexNivat.applied_colour_difference_finite_support`](../Star/ConvexNivat/SectorFiniteSupport.lean) |
| 3.3 | A maps θ colours and scalar encoding to periodic background | [`ConvexNivat.applied_colour_equals_background`](../Star/ConvexNivat/SectorCaseB.lean)<br>[`ConvexNivat.encoded_star_applied_background`](../Star/ConvexNivat/SectorCaseB.lean) |
| 4.1 | Nonzero component-isolating differences in strips | [`ConvexNivat.lemma_4_1`](../Star/ConvexNivat/StarIsolated.lean) |
| 4.2 | Some two-point witness survives D | [`ConvexNivat.quadraticWitness_finite_support`](../Star/ConvexNivat/StarWitness.lean)<br>[`ConvexNivat.lemma_4_2`](../Star/ConvexNivat/StarWitness.lean) |
| 5.1 | Two independent recursions | [`ConvexNivat.lemma_5_1`](../Algebra/ConvexNivat/OperatorWitness.lean) |
| 5.2 | Laurent quotient spanned by the difference zonotope | [`ConvexNivat.quotient_spanned_by_spectral_difference_body`](../Spectral/ConvexNivat/QuotientSpanning.lean) |
| 5.3 | Nonzero witness within Z−Z | [`ConvexNivat.quadratic_witness_in_spectral_difference_body`](../Spectral/ConvexNivat/SpectralWitnessConsumers.lean) |
| 6.1 | Integer points of the difference zonotope | [`ConvexNivat.lemma6_1`](../Geometry/ConvexNivat/Geometry/ZonotopeDecomposition.lean)<br>[`ConvexNivat.lemma6_1_pair`](../Geometry/ConvexNivat/Geometry/ZonotopeDecomposition.lean) |
| 6.2 | Two points in one integral zonotope | [`ConvexNivat.corollary6_2`](../Geometry/ConvexNivat/Geometry/ZonotopeDecomposition.lean) |
| 7.1 | Both witness sites fit every erosion translate | [`ConvexNivat.lemma7_1`](../Geometry/ConvexNivat/Geometry/Basic.lean) |
| 7.2 | Quadratic observables independent modulo affine observables | [`ConvexNivat.lemma7_2`](../Star/ConvexNivat/SourceGaps/QuadraticObservables.lean) |
| 7.3 | Complexity lower bound for every star configuration | [`ConvexNivat.theoremT`](../Star/ConvexNivat/MainTheorem.lean) |
| 7.4 | Exact cancellation of the affine deficit | [`ConvexNivat.affine_observable_dimension_budget`](../Spectral/ConvexNivat/AffineDimensionConsumer.lean)<br>[`ConvexNivat.lemma7_2`](../Star/ConvexNivat/SourceGaps/QuadraticObservables.lean)<br>[`ConvexNivat.quadraticObservableSpace_finrank`](../Star/ConvexNivat/SourceGaps/QuadraticObservables.lean)<br>[`ConvexNivat.quadraticObservableSpace_dimension_join`](../Star/ConvexNivat/SourceGaps/QuadraticObservables.lean)<br>[`ConvexNivat.theoremT`](../Star/ConvexNivat/MainTheorem.lean) |
| 8.1 | Full structure producer | [`ConvexNivat.theorem8_1`](../Reduction/ConvexNivat/ReductionJoin.lean) |
| 8.2 | Global extension of forward regional periods | [`ConvexNivat.lemma8_2_eventual_entry`](../Dynamics/ConvexNivat/RegionExtension.lean)<br>[`ConvexNivat.lemma8_2_extensionAlong`](../Dynamics/ConvexNivat/RegionExtension.lean)<br>[`ConvexNivat.lemma8_2_region_cone`](../Dynamics/ConvexNivat/RegionExtension.lean)<br>[`ConvexNivat.lemma8_2_halfPlane_normal`](../Dynamics/ConvexNivat/RegionExtension.lean) |
| 8.3 | Minimal counterexample and equal order on nonperiodic orbit points | [`ConvexNivat.remark8_3_equal_order`](../Reduction/ConvexNivat/ReductionOrderAndModPrime.lean)<br>[`ConvexNivat.remark8_3_select_minimal`](../Reduction/ConvexNivat/ReductionOrderAndModPrime.lean) |
| 8.4 | Kari–Szabados external package | [`ConvexNivat.external8_4a_obligation`](../Algebra/ConvexNivat/ExternalAnnihilator.lean)<br>[`ConvexNivat.external8_4b_factors_obligation`](../Algebra/ConvexNivat/ExternalFactors.lean)<br>[`ConvexNivat.external8_4b_decomposition_obligation`](../Algebra/ConvexNivat/ExternalDecomposition.lean) |
| 8.5 | Orbit closure and reduction modulo a large prime | [`ConvexNivat.lemma8_5`](../Reduction/ConvexNivat/ReductionOrderAndModPrime.lean)<br>[`ConvexNivat.lemma8_5_merge_parallel`](../Star/ConvexNivat/Normalization.lean) |
| 8.6 | Colle oriented nonexpansive boundary | [`ConvexNivat.external8_6_obligation`](../Reduction/ColleJoins86/External86.lean)<br>[`ConvexNivat.external8_6_both_directions_obligation`](../Reduction/ColleJoins86/External86.lean) |
| 8.7 | Colle nonperiodic regional accumulation point | [`ConvexNivat.external8_7_obligation`](../Reduction/ConvexNivat/External87.lean) |
| 8.8 | One-sided reversible finite-state recursion | [`ConvexNivat.lemma8_8`](../Dynamics/ConvexNivat/FiniteState.lean)<br>[`ConvexNivat.lemma8_8_global`](../Dynamics/ConvexNivat/FiniteState.lean) |
| 8.9 | First half-plane producer | [`ConvexNivat.proposition8_9`](../Dynamics/ConvexNivat/FirstHalfPlane.lean) |
| 8.10 | Remove doubly periodic terms, retain first tails and cone | [`ConvexNivat.corollary8_10`](../Dynamics/ConvexNivat/FirstHalfPlaneCorollary.lean) |
| 8.11 | Role of finite-state lemma and minimality | [`ConvexNivat.lemma_4_1`](../Star/ConvexNivat/StarIsolated.lean)<br>[`ConvexNivat.lemma8_8`](../Dynamics/ConvexNivat/FiniteState.lean)<br>[`ConvexNivat.proposition8_9`](../Dynamics/ConvexNivat/FirstHalfPlane.lean)<br>[`ConvexNivat.corollary8_10`](../Dynamics/ConvexNivat/FirstHalfPlaneCorollary.lean) |
| 8.12 | Second half-plane producer | [`ConvexNivat.theorem8_12`](../Dynamics/ConvexNivat/SecondHalfPlane.lean) |
| 8.13 | Finite-field lifting of a periodic difference | [`ConvexNivat.lemma8_13`](../Dynamics/ConvexNivat/Biperiodicity.lean) |
| 8.14 | Two-component limits are doubly periodic | [`ConvexNivat.proposition8_14`](../Dynamics/ConvexNivat/TwoComponentLimits.lean) |
| 8.15 | Available safe direction at every stage | [`ConvexNivat.lemma8_15`](../Dynamics/ConvexNivat/AvailableDirections.lean) |
| 8.16 | All periodic far-side limits force an actual periodic tail | [`ConvexNivat.lemma8_16_finite_limits`](../Dynamics/ConvexNivat/Propagation.lean)<br>[`ConvexNivat.lemma8_16`](../Dynamics/ConvexNivat/Propagation.lean) |
| 8.17 | Normalise admissible decompositions to stars | [`ConvexNivat.lemma8_17_alignment`](../Star/ConvexNivat/Normalization.lean)<br>[`ConvexNivat.lemma8_17_component`](../Star/ConvexNivat/Normalization.lean)<br>[`ConvexNivat.admissible_absorb_double`](../Star/ConvexNivat/Normalization.lean)<br>[`ConvexNivat.admissible_merge_parallel`](../Star/ConvexNivat/Normalization.lean)<br>[`ConvexNivat.lemma8_17`](../Star/ConvexNivat/Normalization.lean) |
| 8.18 | Full convex Nivat theorem | [`ConvexNivat.convexNivat`](../Reduction/ConvexNivat/OriginalMain.lean) |
| 8.19 | Rectangular Nivat theorem | [`ConvexNivat.nivatRectangles`](../Reduction/ConvexNivat/OriginalMain.lean) |
| D.1 | Two periodic components, finite-field convex version | [`ConvexNivat.theoremD_1`](../Dynamics/ConvexNivat/AppendixD.lean) |
| D.2 | Minimal modular order two forbids low convex complexity | [`ConvexNivat.corollaryD_2`](../Dynamics/ConvexNivat/AppendixD.lean) |
| D.3 | Periodic strip propagates to the whole plane | [`ConvexNivat.lemmaD_3`](../Dynamics/ConvexNivat/AppendixBase.lean) |
| D.4 | Balanced finite convex set | [`ConvexNivat.BalancedSet`](../Reduction/ConvexNivat/ReductionDefinitions.lean) |
| D.5 | Produce a balanced subset of any low-complexity convex window | [`ConvexNivat.delete_extreme_row_convex`](../Dynamics/ConvexNivat/AppendixBase.lean)<br>[`ConvexNivat.intermediate_row_cardinality`](../Dynamics/ConvexNivat/AppendixRows.lean)<br>[`ConvexNivat.lemmaD_5`](../Dynamics/ConvexNivat/AppendixBalanced.lean) |
| D.6 | Ambiguity strip with orbit-closure witness | [`ConvexNivat.AmbiguityStrip`](../Reduction/ConvexNivat/ReductionDefinitions.lean) |
| D.7 | Balanced ambiguity produces a global period | [`ConvexNivat.balanced_two_determination_rules`](../Dynamics/ConvexNivat/AppendixBalanced.lean)<br>[`ConvexNivat.lemmaD_7`](../Dynamics/ConvexNivat/AppendixPropagation.lean) |
| D.8 | Internal replacement for an older cited algebraic argument | [`ConvexNivat.balanced_two_determination_rules`](../Dynamics/ConvexNivat/AppendixBalanced.lean)<br>[`ConvexNivat.lemmaD_3`](../Dynamics/ConvexNivat/AppendixBase.lean)<br>[`ConvexNivat.lemmaD_7`](../Dynamics/ConvexNivat/AppendixPropagation.lean) |
| D.9 | Abelian-group-valued generalisation | [`ConvexNivat.remarkD_9`](../Dynamics/ConvexNivat/SourceGaps/AbelianTwoComponent.lean) |

Appendix B only announces further results and is not part of the proof chain. The original Appendix C experimental records are not reproduced. Their limitations and the C.3 printed inference issue are recorded in [SOURCE_ISSUES.md](../SOURCE_ISSUES.md).
