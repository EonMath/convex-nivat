import NivatTrial.PeriodicBandCoding
import NivatTrial.RealDirectionGeometry
import NivatTrial.ColleEnvelopeTranslation

/-! Boundary recentering of a periodic reference has only finitely many
phases, even when its period vector is not primitive. A subsequence can
therefore retain one actual reference configuration. -/

namespace NivatTrial.CollePeriodicPhases

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.Nonexpansive
open NivatTrial.Dynamics NivatTrial.Periodicity NivatTrial.PeriodicBandCoding
open NivatTrial.RealDirectionGeometry
open scoped Classical
noncomputable section

theorem finite_boundary_phases {A : Type*} (p : Lattice → A)
    (u : Lattice) (hu : u ≠ 0) (hp : IsPeriod p u) :
    {q : Lattice → A | ∃ c : Lattice, det u c = 0 ∧ q = shift c p}.Finite := by
  have hv : embed u ≠ 0 := by
    intro he
    exact hu (embed_injective (he.trans embed_zero.symm))
  have hs : score (embed u) u = 0 := by simp [score,embed]; ring
  obtain ⟨d,hd⟩ := exists_positive_score hv
  have hdet := independent_of_score (embed u) u d hu hs (ne_of_gt hd)
  obtain ⟨S,hS⟩ := finite_band_representatives u d hdet (embed u) hs hd 0 0
  apply ((S.finite_toSet).image (fun c => shift c p)).subset
  rintro q ⟨c,hc,rfl⟩
  have hsc : score (embed u) c = 0 := by
    have hh : (det u c : ℝ) = 0 := by exact_mod_cast hc
    simpa [score,embed,det] using hh
  obtain ⟨s,hsS,m,hcS⟩ := hS c (by rw [hsc]) (by rw [hsc])
  refine ⟨s,hsS,?_⟩
  funext z
  rw [hcS]
  symm
  simpa [shift,add_assoc,add_left_comm,add_comm] using (hp.zsmul m) (s+z)

theorem constant_subsequence_of_finite_range {B : Type*} (f : ℕ → B)
    (hf : (Set.range f).Finite) :
    ∃ b, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, f (φ n) = b := by
  let : Fintype (Set.range f) := hf.fintype
  let g (n : ℕ) : Set.range f := ⟨f n,⟨n,rfl⟩⟩
  obtain ⟨b,hb⟩ := Finite.exists_infinite_fiber g
  have hi : (g ⁻¹' {b}).Infinite := Set.infinite_coe_iff.mp hb
  obtain ⟨φ,hφ,hconst⟩ := Nat.exists_strictMono_subsequence (P := fun n => g n = b) (by
    intro N
    obtain ⟨n,hn,hN⟩ := hi.exists_gt N
    exact ⟨n,hN,hn⟩)
  exact ⟨b.val,φ,hφ,fun n => congrArg Subtype.val (hconst n)⟩

theorem constant_boundary_phase_subsequence {A : Type*} (p : Lattice → A)
    (u : Lattice) (hu : u ≠ 0) (hp : IsPeriod p u)
    (c : ℕ → Lattice) (hc : ∀ n, det u (c n) = 0) :
    ∃ q : Lattice → A, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ n, shift (c (φ n)) p = q) ∧ IsPeriod q u ∧ q ∈ languageHull p := by
  have hf : (Set.range (fun n => shift (c n) p)).Finite :=
    (finite_boundary_phases p u hu hp).subset (by
      rintro q ⟨n,rfl⟩
      exact ⟨c n,hc n,rfl⟩)
  obtain ⟨q,φ,hφ,hq⟩ := constant_subsequence_of_finite_range _ hf
  refine ⟨q,φ,hφ,hq,?_,?_⟩
  · rw [← hq 0]
    intro z
    simpa [shift,add_assoc] using hp (c (φ 0)+z)
  · rw [← hq 0]
    exact shift_mem_languageHull (self_mem_languageHull p) _

end
end NivatTrial.CollePeriodicPhases
