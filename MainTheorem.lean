import ConvexNivat.OriginalMain
import ConvexNivat.MainTheorem
import ColleJoins86.External86
import ConvexNivat.AffineDimensionConsumer
import ConvexNivat.AffineRelationConsumer
import ConvexNivat.AppendixBalanced
import ConvexNivat.AppendixBase
import ConvexNivat.AppendixD
import ConvexNivat.AppendixPropagation
import ConvexNivat.AppendixRows
import ConvexNivat.AvailableDirections
import ConvexNivat.Biperiodicity
import ConvexNivat.External87
import ConvexNivat.ExternalAnnihilator
import ConvexNivat.ExternalDecomposition
import ConvexNivat.ExternalFactors
import ConvexNivat.FiniteState
import ConvexNivat.FirstHalfPlane
import ConvexNivat.FirstHalfPlaneCorollary
import ConvexNivat.Geometry.Basic
import ConvexNivat.Geometry.ZonotopeDecomposition
import ConvexNivat.Normalization
import ConvexNivat.OperatorFiniteSupport
import ConvexNivat.OperatorWitness
import ConvexNivat.Propagation
import ConvexNivat.QuotientSpanning
import ConvexNivat.ReductionDefinitions
import ConvexNivat.ReductionJoin
import ConvexNivat.ReductionOrderAndModPrime
import ConvexNivat.RegionExtension
import ConvexNivat.SecondHalfPlane
import ConvexNivat.SectorCaseB
import ConvexNivat.SectorConnectivity
import ConvexNivat.SectorCycle
import ConvexNivat.SectorFiniteSupport
import ConvexNivat.SectorGeometry
import ConvexNivat.SectorPeriods
import ConvexNivat.SectorRayEquality
import ConvexNivat.SectorSpectralDefinitions
import ConvexNivat.SourceGaps.AbelianTwoComponent
import ConvexNivat.SourceGaps.DimensionJoin
import ConvexNivat.SourceGaps.FullARemark
import ConvexNivat.SourceGaps.PeriodicBackground
import ConvexNivat.SourceGaps.QuadraticObservables
import ConvexNivat.SpectralCyclotomic
import ConvexNivat.SpectralDivisibility
import ConvexNivat.SpectralFourier
import ConvexNivat.SpectralGalois
import ConvexNivat.SpectralIntegerLaurent
import ConvexNivat.SpectralLaurentBridge
import ConvexNivat.SpectralWitnessConsumers
import ConvexNivat.StarFiniteSupport
import ConvexNivat.StarFirstCase
import ConvexNivat.StarIsolated
import ConvexNivat.StarSpectral
import ConvexNivat.StarWitness
import ConvexNivat.TwoComponentLimits

/-!
# Convex Nivat: Theorem B (Theorem 8.18)

The headline result is `ConvexNivat.convexNivat`:
a configuration over a finite alphabet is periodic whenever one nonempty
finite lattice-convex window has complexity at most its cardinality.

`ConvexNivat.nivatRectangles` is the rectangular consequence.
`ConvexNivat.theoremT` is the supporting star-configuration theorem (7.3).
The imports also expose all retained numbered results in sections 0-8
and Appendix D, preserving their original declarations and module identities.
-/
