import NivatTrial.IncrementSupport
import NivatTrial.LatticePolygon
import NivatTrial.IntegerDecomposition
import NivatTrial.KariSzabados
import NivatTrial.ColleOppositeDirections

/-! Integer encoding and decomposition interfaces for the final reduction.

The historical module name is retained for existing imports. Both former
external results are now proved in the project, and their input records have
been removed. Integer components may be unbounded; observed colours lie in
a fixed finite set of positive integers. -/

namespace NivatTrial.ExternalInputs

open NivatTrial.Geometry NivatTrial.Periodicity NivatTrial.Dynamics
open NivatTrial.OneSidedRecurrence NivatTrial.IncrementSupport
open NivatTrial.RegionGeometry NivatTrial.LatticePolygon
open scoped Classical

noncomputable section

def integerCode {M : ℕ} (a : Fin M) : ℤ := (a.val : ℤ)+1
def integerField {M : ℕ} (θ : Lattice → Fin M) : Lattice → ℤ := encode integerCode θ

theorem integerCode_injective (M : ℕ) : Function.Injective (@integerCode M) := by
  intro a b hab
  apply Fin.ext
  dsimp [integerCode] at hab
  omega

structure IntegerDecomposition (θ : Lattice → ℤ) (n : ℕ) where
  component : Fin n → Lattice → ℤ
  period : Fin n → Lattice
  period_ne_zero : ∀ i, period i ≠ 0
  independent : ∀ i j, i ≠ j → det (period i) (period j) ≠ 0
  component_period : ∀ i, IsPeriod (component i) (period i)
  sum_eq : (∑ i, component i)=θ

def HasIntegerDecomposition (θ : Lattice → ℤ) (n : ℕ) : Prop :=
  Nonempty (IntegerDecomposition θ n)

/-- The former Kari--Szabados input is now an internally proved theorem. -/
theorem low_complexity_integer_decomposition (M : ℕ) (θ : Lattice → Fin M)
    (S : Finset Lattice) (hne : S.Nonempty) (hlow : patternComplexity θ S ≤ S.card) :
    ∃ n : ℕ, HasIntegerDecomposition (integerField θ) n := by
  obtain ⟨n,h,F,hn,hpair,hp,hsum⟩ :=
    NivatTrial.KariSzabados.low_complexity_decomposition M θ S hne hlow
  exact ⟨n,⟨⟨F,h,hn,hpair,hp,hsum⟩⟩⟩

def UniformOrder {M : ℕ} (θ : Lattice → Fin M) (m : ℕ) : Prop :=
  ∀ ξ ∈ languageHull θ, ¬IsPeriodic ξ →
    HasIntegerDecomposition (integerField ξ) m ∧
      ∀ n, HasIntegerDecomposition (integerField ξ) n → m ≤ n

/-- The product annihilator passes to the finite-alphabet language hull;
the internally proved integer decomposition gives its order upper bound. -/
theorem decomposition_in_languageHull {M m : ℕ}
    {θ ξ : Lattice → Fin M} (D : IntegerDecomposition (integerField θ) m)
    (hξ : ξ ∈ languageHull θ) : HasIntegerDecomposition (integerField ξ) m := by
  have hann : iteratedIncrement (Finset.univ.toList.map D.period) (integerField θ)=0 := by
    have he := congrArg (iteratedIncrement (Finset.univ.toList.map D.period)) D.sum_eq
    exact he.symm.trans (decomposition_annihilator D.component D.period D.component_period)
  have hlim := iteratedIncrement_passes_to_languageHull _ (integerField θ) (integerField ξ)
    (encode_mem_languageHull integerCode hξ) hann
  obtain ⟨F,hp,he⟩ := NivatTrial.IntegerDecomposition.product_decomposition m D.period
    D.period_ne_zero D.independent _ hlim
  exact ⟨⟨F,D.period,D.period_ne_zero,D.independent,hp,he⟩⟩

/-- Remark 8.3: choose a counterexample of least order, within a fixed alphabet
and fixed window. Its nonperiodic orbit limits have exactly the same order. -/
theorem minimal_counterexample {M : ℕ}
    (θ : Lattice → Fin M) (S : Finset Lattice) (hne : S.Nonempty)
    (hlow : patternComplexity θ S ≤ S.card) (hnot : ¬IsPeriodic θ) :
    ∃ m : ℕ, ∃ ξ : Lattice → Fin M, patternComplexity ξ S ≤ S.card ∧
      ¬IsPeriodic ξ ∧ HasIntegerDecomposition (integerField ξ) m ∧ UniformOrder ξ m := by
  let P : ℕ → Prop := fun n => ∃ ξ : Lattice → Fin M,
    patternComplexity ξ S ≤ S.card ∧ ¬IsPeriodic ξ ∧ HasIntegerDecomposition (integerField ξ) n
  have hex : ∃ n, P n := by
    obtain ⟨n,hD⟩ := low_complexity_integer_decomposition M θ S hne hlow
    exact ⟨n,θ,hlow,hnot,hD⟩
  let m := Nat.find hex
  obtain ⟨ξ,hξlow,hξnot,hD⟩ := Nat.find_spec hex
  refine ⟨m,ξ,hξlow,hξnot,hD,?_⟩
  intro η hη hηnot
  have hηlow : patternComplexity η S ≤ S.card :=
    (patternComplexity_le_of_mem_languageHull hη S).trans hξlow
  obtain ⟨D⟩ := hD
  refine ⟨decomposition_in_languageHull D hη, ?_⟩
  intro n hDn
  exact Nat.find_min' hex ⟨η,hηlow,hηnot,hDn⟩

end
end NivatTrial.ExternalInputs
