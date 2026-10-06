import NivatTrial.ColleLongFaces
import NivatTrial.ColleRegionCompactness

/-! Recentered envelopes with a common lattice point have an increasing
subsequence. Their integer support depths form a vector of natural numbers,
so Dickson's lemma supplies simultaneous monotonicity in every direction. -/

namespace NivatTrial.ColleEnvelopeLimits

open NivatTrial.Geometry NivatTrial.RegionGeometry NivatTrial.Dynamics
open NivatTrial.Nonexpansive NivatTrial.NonexpansiveExistence
open NivatTrial.ColleEnvelopeGeometry NivatTrial.ColleMaximalEnvelope
open NivatTrial.ColleLongFaces Filter
open scoped Classical
noncomputable section

theorem exists_monotone_subsequence (D : Finset Lattice) (T : ℕ → Finset Lattice)
    (hzero : ∀ n, 0 ∈ T n) (hT : ∀ n, IsEnvelope D (T n : Set Lattice)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m n, m ≤ n → T (φ m) ⊆ T (φ n) := by
  let depth (n : ℕ) (h : D) : ℕ := (-lowerSupport (T n) h.val).toNat
  have hnonpos (n : ℕ) (h : D) : lowerSupport (T n) h.val ≤ 0 := by
    simpa using lowerSupport_le (hzero n) h.val
  have hdepth (n : ℕ) (h : D) : (depth n h : ℤ) = -lowerSupport (T n) h.val := by
    exact Int.toNat_of_nonneg (by have := hnonpos n h; omega)
  obtain ⟨φ,hφ⟩ := (wellQuasiOrdered_le (α := D → ℕ)).exists_monotone_subseq depth
  refine ⟨φ,φ.strictMono,?_⟩
  intro m n hmn z hz
  have hem := (hT (φ m)).eq_finite_envelope ⟨0,hzero (φ m)⟩
  have hen := (hT (φ n)).eq_finite_envelope ⟨0,hzero (φ n)⟩
  have hbound : ∀ h ∈ D, lowerSupport (T (φ n)) h ≤ lowerSupport (T (φ m)) h := by
    intro h hh
    have hd : depth (φ m) ⟨h,hh⟩ ≤ depth (φ n) ⟨h,hh⟩ := hφ m n hmn ⟨h,hh⟩
    have hc : (depth (φ m) ⟨h,hh⟩ : ℤ) ≤ depth (φ n) ⟨h,hh⟩ := by exact_mod_cast hd
    rw [hdepth,hdepth] at hc
    dsimp at hc
    omega
  have hm : z ∈ envelope D (lowerSupport (T (φ m))) := by rwa [← hem]
  have hn := envelope_antitone D hbound hm
  rwa [← hen] at hn

def increasingRegion (T : ℕ → Finset Lattice) : Set Lattice :=
  {z | ∃ n, z ∈ T n}

theorem increasingRegion_isEnvelope (D : Finset Lattice) (T : ℕ → Finset Lattice)
    (hT : ∀ n, IsEnvelope D (T n : Set Lattice))
    (hmono : ∀ m n, m ≤ n → T m ⊆ T n) : IsEnvelope D (increasingRegion T) := by
  let c : Set (Set Lattice) := Set.range (fun n => (T n : Set Lattice))
  have heq : increasingRegion T = ⋃₀ c := by
    ext z
    simp only [increasingRegion,c,Set.mem_ofPred_eq,Set.mem_sUnion,Set.mem_range]
    constructor
    · rintro ⟨n,hn⟩
      exact ⟨T n,⟨n,rfl⟩,hn⟩
    · rintro ⟨R,⟨n,rfl⟩,hn⟩
      exact ⟨n,hn⟩
  rw [heq]
  apply isEnvelope_sUnion_chain D c
  · rintro R ⟨m,rfl⟩ S ⟨n,rfl⟩ _
    rcases le_total m n with hmn | hnm
    · exact Or.inl (hmono m n hmn)
    · exact Or.inr (hmono n m hnm)
  · exact ⟨T 0,⟨0,rfl⟩⟩
  · rintro R ⟨n,rfl⟩
    exact hT n

theorem increasingRegion_longFaces (D : Finset Lattice) (T : ℕ → Finset Lattice)
    (hT : ∀ n, LongFaces D (T n : Set Lattice)) : LongFaces D (increasingRegion T) := by
  intro d hd z ⟨n,hz⟩ hmin
  obtain ⟨w,hw,hwd,he⟩ := hT n d hd z hz (fun w hw => hmin w ⟨n,hw⟩)
  exact ⟨w,⟨n,hw⟩,⟨n,hwd⟩,he⟩

/-- Configuration compactness and growing envelope agreement produce an
actual hull point agreeing on the entire infinite region. -/
theorem limit_on_increasing_region {A : Type*} [Fintype A]
    (θ p : Lattice → A) (T : ℕ → Finset Lattice)
    (hmono : ∀ m n, m ≤ n → T m ⊆ T n)
    (x : ℕ → Lattice → A) (hx : ∀ n, x n ∈ languageHull θ)
    (hagree : ∀ n, ∀ z ∈ T n, x n z = p z) :
    ∃ y ∈ languageHull θ, AgreeOn y p (increasingRegion T) := by
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  obtain ⟨y,hy,φ,hφ,hlim⟩ := (isCompact_languageHull θ).tendsto_subseq hx
  refine ⟨y,hy,?_⟩
  rintro z ⟨m,hz⟩
  have hlarge : ∀ᶠ n : ℕ in atTop, m ≤ φ n :=
    hφ.tendsto_atTop.eventually (eventually_ge_atTop m)
  obtain ⟨n,hn,heq⟩ := (hlarge.and (eventually_coordinate_eq hlim z)).exists
  exact heq.symm.trans (hagree (φ n) z (hmono m (φ n) hn hz))

theorem finite_subset_in_increasing_region (T : ℕ → Finset Lattice)
    (hmono : ∀ m n, m ≤ n → T m ⊆ T n) (S : Finset Lattice)
    (hS : (S : Set Lattice) ⊆ increasingRegion T) :
    ∃ N : ℕ, S ⊆ T N := by
  choose n hn using fun z : S => hS z.property
  let N := Finset.univ.sup n
  refine ⟨N,?_⟩
  intro z hz
  have hle : n ⟨z,hz⟩ ≤ N := Finset.le_sup (f := n) (Finset.mem_univ (⟨z,hz⟩ : S))
  exact hmono (n ⟨z,hz⟩) N hle (hn ⟨z,hz⟩)

end
end NivatTrial.ColleEnvelopeLimits
