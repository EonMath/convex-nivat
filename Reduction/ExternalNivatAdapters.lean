import ConvexNivat.Core
import ConvexNivat.CorePatterns
import NivatTrial.LatticePolygon
import NivatTrial.Periodicity
import NivatTrial.TheoremB

namespace ConvexNivat.ExternalNivatAdapters

/-- Restrict the codomain to a supplied finite alphabet, retaining every value. -/
def alphabetLift {A : Type*} (B : Finset A) (f : ConvexNivat.Configuration A)
    (hf : ∀ z, f z ∈ B) : ConvexNivat.Configuration {a : A // a ∈ B} :=
  fun z => ⟨f z, hf z⟩

theorem embed_eq (z : ConvexNivat.Lattice) :
    ConvexNivat.embed z = NivatTrial.Zonotope.embed z := by rfl

theorem windowHull_eq (S : Finset ConvexNivat.Lattice) :
    ConvexNivat.windowHull S = NivatTrial.LatticePolygon.windowHull S := by rfl

theorem latticeConvex_iff (S : Finset ConvexNivat.Lattice) :
    ConvexNivat.LatticeConvex S ↔ NivatTrial.LatticePolygon.IsLatticeConvex S := by rfl

theorem translate_eq_shift {A : Type*} (f : ConvexNivat.Configuration A)
    (u : ConvexNivat.Lattice) :
    ConvexNivat.translate u f = NivatTrial.Dynamics.shift u f := by
  funext z
  exact congrArg f (add_comm z u)

theorem pattern_eq_patternAt {A : Type*}
    (f : ConvexNivat.Configuration A) (S : Finset ConvexNivat.Lattice)
    (u : ConvexNivat.Lattice) :
    ConvexNivat.pattern f S u = NivatTrial.patternAt f S u := by rfl

theorem patternSet_eq {A : Type*}
    (f : ConvexNivat.Configuration A) (S : Finset ConvexNivat.Lattice) :
    ConvexNivat.patternSet f S = NivatTrial.patternSet f S := by rfl

theorem patternComplexity_eq {A : Type*}
    (f : ConvexNivat.Configuration A) (S : Finset ConvexNivat.Lattice) :
    NivatTrial.patternComplexity f S = ConvexNivat.complexity f S := by rfl

theorem hasPeriod_iff {A : Type*} (f : ConvexNivat.Configuration A)
    (h : ConvexNivat.Lattice) :
    ConvexNivat.HasPeriod f h ↔ NivatTrial.Periodicity.IsPeriod f h := by rfl

theorem periodic_iff {A : Type*} (f : ConvexNivat.Configuration A) :
    ConvexNivat.Periodic f ↔ NivatTrial.Periodicity.IsPeriodic f := by rfl

theorem alphabetLift_values {A : Type*} (B : Finset A)
    (f : ConvexNivat.Configuration A) (hf : ∀ z, f z ∈ B) :
    (fun z => (alphabetLift B f hf z).val) = f := by rfl

theorem alphabetLift_complexity_eq {A : Type*} (B : Finset A)
    (f : ConvexNivat.Configuration A) (hf : ∀ z, f z ∈ B)
    (S : Finset ConvexNivat.Lattice) :
    NivatTrial.patternComplexity (alphabetLift B f hf) S =
      ConvexNivat.complexity f S := by
  rw [patternComplexity_eq]
  have h := ConvexNivat.complexity_injective_encoding (alphabetLift B f hf)
    Subtype.val Subtype.val_injective S
  change ConvexNivat.complexity f S = ConvexNivat.complexity (alphabetLift B f hf) S at h
  exact h.symm

theorem alphabetLift_periodic_iff {A : Type*} (B : Finset A)
    (f : ConvexNivat.Configuration A) (hf : ∀ z, f z ∈ B) :
    NivatTrial.Periodicity.IsPeriodic (alphabetLift B f hf) ↔
      ConvexNivat.Periodic f := by
  rw [← periodic_iff]
  have h := ConvexNivat.periodic_injective_encoding_iff (alphabetLift B f hf)
    Subtype.val Subtype.val_injective
  change ConvexNivat.Periodic f ↔ ConvexNivat.Periodic (alphabetLift B f hf) at h
  exact h.symm

/-- Theorem 8.18 in the project's actual definitions, with no regional premise. -/
theorem periodic_of_low_convex_complexity {A : Type*} [Finite A]
    (f : ConvexNivat.Configuration A) (S : Finset ConvexNivat.Lattice)
    (hne : S.Nonempty) (hS : ConvexNivat.LatticeConvex S)
    (hlow : ConvexNivat.complexity f S ≤ S.card) :
    ConvexNivat.Periodic f := by
  let : Fintype A := Fintype.ofFinite A
  apply (periodic_iff f).mpr
  apply NivatTrial.TheoremB.periodic_of_low_convex_complexity f S hne
    ((latticeConvex_iff S).mp hS)
  rwa [patternComplexity_eq]

end ConvexNivat.ExternalNivatAdapters
