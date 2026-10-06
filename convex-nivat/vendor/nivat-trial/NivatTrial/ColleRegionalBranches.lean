import NivatTrial.ColleCaseOne
import NivatTrial.ColleDecompositionTransforms

/-! The regional construction splits at actual orbit translates. Its first
branch already produces a nonperiodic configuration with a periodic wedge;
the second supplies real finite agreement windows with half-strip defects. -/

namespace NivatTrial.ColleRegionalBranches

open NivatTrial.Geometry NivatTrial.Dynamics NivatTrial.Nonexpansive
open NivatTrial.Periodicity NivatTrial.RegionGeometry NivatTrial.ExternalInputs
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleLongFaces
open NivatTrial.ColleEnvelopeGeometry NivatTrial.ColleFiniteEnvelope
open NivatTrial.ColleZonotopeEnvelope NivatTrial.ColleRegionDichotomy
open NivatTrial.ColleCaseOne NivatTrial.ColleDecompositionTransforms
open scoped Classical
noncomputable section

def HasPeriodicWedge {M n : ℕ} (θ : Lattice → Fin M)
    (v : Fin n → Lattice) (u : Lattice) : Prop :=
  ∃ x ∈ languageHull θ, ¬IsPeriodic x ∧ ∃ k ∈ signedDirections v, ∃ c : ℤ,
    ∃ Q : ℕ, 0 < det u k ∧ 0 < Q ∧
      LatticeConvexRegion (wedge u k c) ∧ (wedge u k c).Nonempty ∧
      PeriodicOn x (wedge u k c) (Q•u) ∧ ForwardInvariant (wedge u k c) k

def HasDefectiveHalfStripPatches {A : Type*} {n : ℕ}
    (θ p : Lattice → A) (v : Fin n → Lattice) (i : Fin n) : Prop :=
  ∀ B₀ : Finset Lattice,
    IsEnvelope (signedDirections v) (B₀ : Set Lattice) →
    LongFaces (signedDirections v) (B₀ : Set Lattice) → lowerSupport B₀ (v i) = 0 →
    ∃ B : Finset Lattice, ∃ x ∈ languageHull θ,
      B₀ ⊆ B ∧ IsEnvelope (signedDirections v) (B : Set Lattice) ∧
      LongFaces (signedDirections v) (B : Set Lattice) ∧ lowerSupport B (v i) = 0 ∧
      AgreeOn x p (B : Set Lattice) ∧ ∃ z ∈ halfStrip B (v i), x z ≠ p z

theorem periodic_wedge_of_actual_translate {M m : ℕ} (hm : 2 ≤ m)
    (θ p : Lattice → Fin M) (E : IntegerDecomposition (integerField θ) m)
    (hnot : ¬IsPeriodic θ) (i : Fin m)
    (q : ℕ) (hq : 0 < q) (hp : IsPeriod p (q•E.period i))
    (T : Finset Lattice) (t : Lattice)
    (hzero : (0:Lattice) ∈ T)
    (hclosed : IsEnvelope (signedDirections E.period) (T : Set Lattice))
    (hfaces : LongFaces (signedDirections E.period) (T : Set Lattice))
    (hlevel : lowerSupport T (E.period i) = 0)
    (hxp : AgreeOn (shift t θ) p (halfStrip T (E.period i))) :
    HasPeriodicWedge θ E.period (E.period i) := by
  let E' := translate E t
  obtain ⟨j,k,c,Q,hki,huk,hQ,hconv,hne,hper,hforw⟩ := periodic_wedge_at_component hm
    (shift t θ) p E' T i hclosed hfaces hzero hlevel q hq hp hxp
  refine ⟨shift t θ,shift_mem_languageHull (self_mem_languageHull θ) t,?_,k,?_,
    c,Q,huk,hQ,hconv,hne,hper,hforw⟩
  · exact fun ht => hnot ((isPeriodic_shift_iff θ t).mp ht)
  · exact (mem_signedDirections E.period k).mpr ⟨j,hki⟩

theorem actual_regional_dichotomy {M m : ℕ} (hm : 2 ≤ m)
    (θ p : Lattice → Fin M) (E : IntegerDecomposition (integerField θ) m)
    (hpHull : p ∈ languageHull θ) (hnot : ¬IsPeriodic θ)
    (i : Fin m) (q : ℕ) (hq : 0 < q) (hp : IsPeriod p (q•E.period i)) :
    HasPeriodicWedge θ E.period (E.period i) ∨
      HasDefectiveHalfStripPatches θ p E.period i := by
  obtain hcase | hcase := halfStrip_agreement_or_arbitrarily_large_defects
    hm θ p hpHull E.period E.independent i
  · obtain ⟨T,t,h0,hclosed,hfaces,hlevel,hagree⟩ := hcase
    exact Or.inl (periodic_wedge_of_actual_translate hm θ p E hnot i q hq hp
      T t h0 hclosed hfaces hlevel hagree)
  · right
    intro B₀ _ _ hlevel
    have hB₀ : ∀ z ∈ B₀, 0 ≤ det (E.period i) z := by
      intro z hz
      rw [← hlevel]
      exact lowerSupport_le hz _
    obtain ⟨B,t,hB₀B,_,hclosed,hfaces,hlevel',hagree,hbad⟩ := hcase B₀ hB₀
    exact ⟨B,shift t θ,shift_mem_languageHull (self_mem_languageHull θ) t,
      hB₀B,hclosed,hfaces,hlevel',hagree,hbad⟩

end
end NivatTrial.ColleRegionalBranches
