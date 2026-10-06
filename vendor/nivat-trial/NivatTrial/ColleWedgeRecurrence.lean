import NivatTrial.ColleStripRigidity

/-! A product recurrence propagates a zero half-strip into an adjacent
wedge. Orient every factor towards decreasing height; the second supporting
functional guarantees that every required predecessor remains in the wedge.
The proof works over an arbitrary additive group, without bounded values. -/

namespace NivatTrial.ColleWedgeRecurrence

open NivatTrial.Geometry NivatTrial.PeriodicDifference
open NivatTrial.OneSidedRecurrence NivatTrial.IncrementSupport
open NivatTrial.ColleStripRigidity
open scoped Classical
noncomputable section

theorem offsets_nonpositive (π : Lattice →+ ℤ) (hs : List Lattice)
    (hπ : ∀ h ∈ hs, π h ≤ 0) {e : Lattice} (he : e ∈ offsets hs) : π e ≤ 0 := by
  induction hs generalizing e with
  | nil =>
    have he0 : e = 0 := by simpa [offsets] using he
    simp [he0]
  | cons h hs ih =>
    have hh := hπ h (by simp)
    have ht : ∀ k ∈ hs, π k ≤ 0 := fun k hk => hπ k (by simp [hk])
    rcases Finset.mem_union.mp he with he | he
    · exact ih ht he
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
      rw [map_add]
      exact add_nonpos hh (ih ht ha)

theorem nonzero_offset_negative (π : Lattice →+ ℤ) (hs : List Lattice)
    (hπ : ∀ h ∈ hs, π h < 0) {e : Lattice}
    (he : e ∈ offsets hs) (hne : e ≠ 0) : π e < 0 := by
  induction hs generalizing e with
  | nil => exact (hne (by simpa [offsets] using he)).elim
  | cons h hs ih =>
    have hh := hπ h (by simp)
    have ht : ∀ k ∈ hs, π k < 0 := fun k hk => hπ k (by simp [hk])
    rcases Finset.mem_union.mp he with he | he
    · exact ih ht he hne
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
      rw [map_add]
      have hnonpos := offsets_nonpositive π hs (fun k hk => (ht k hk).le) ha
      omega

variable {A : Type*} [AddCommGroup A]

theorem zero_corner_of_negative_factors (π : Lattice →+ ℤ) (hs : List Lattice)
    (hπ : ∀ h ∈ hs, π h < 0) (f : Lattice → A) (z : Lattice)
    (hann : iteratedIncrement hs f z = 0)
    (hzero : ∀ e ∈ offsets hs, e ≠ 0 → f (z+e) = 0) : f z = 0 := by
  induction hs with
  | nil => exact hann
  | cons h hs ih =>
    have hh := hπ h (by simp)
    have ht : ∀ k ∈ hs, π k < 0 := fun k hk => hπ k (by simp [hk])
    have hshift : iteratedIncrement hs f (z+h) = 0 := by
      have heq := iteratedIncrement_congr_at hs f (0 : Lattice → A) (z+h) (by
        intro e he
        have hne : h+e ≠ 0 := by
          intro hz
          have hn := offsets_nonpositive π hs (fun k hk => (ht k hk).le) he
          have hh' := congrArg π hz
          rw [map_add,map_zero] at hh'
          omega
        have hf := hzero (h+e)
          (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e,he,rfl⟩)) hne
        simpa only [add_assoc,Pi.zero_apply] using hf)
      simpa only [iteratedIncrement_zero,Pi.zero_apply] using heq
    have htail : iteratedIncrement hs f z = 0 := by
      change iteratedIncrement hs f (z+h)-iteratedIncrement hs f z = 0 at hann
      rw [hshift,zero_sub,neg_eq_zero] at hann
      exact hann
    exact ih ht htail (fun e he hne => hzero e (Finset.mem_union_left _ he) hne)

theorem zero_on_wedge_of_zero_halfStrip
    (π ψ : Lattice →+ ℤ) (hs : List Lattice) (f : Lattice → A)
    (hπ : ∀ h ∈ hs, π h < 0) (hψ : ∀ h ∈ hs, ψ h ≤ 0)
    (hann : iteratedIncrement hs f = 0) (c : ℤ)
    (hbase : ∀ z, 0 ≤ π z → π z ≤ widthBudget π hs → ψ z ≤ c → f z = 0) :
    ∀ z, 0 ≤ π z → ψ z ≤ c → f z = 0 := by
  have hlevel : ∀ n : ℕ, ∀ z : Lattice, (π z).toNat = n →
      0 ≤ π z → ψ z ≤ c → f z = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro z hzn hz0 hzψ
      by_cases hsmall : π z ≤ widthBudget π hs
      · exact hbase z hz0 hsmall hzψ
      · apply zero_corner_of_negative_factors π hs hπ f z (congrFun hann z)
        intro e he hne
        have hlo : -widthBudget π hs ≤ π e := (abs_le.mp (offset_score_bound π hs e he)).1
        have hneg := nonzero_offset_negative π hs hπ he hne
        have heψ := offsets_nonpositive ψ hs hψ he
        have he0 : 0 ≤ π (z+e) := by rw [map_add]; omega
        have heless : (π (z+e)).toNat < n := by
          rw [← hzn]
          have hwidth := widthBudget_nonneg π hs
          apply (Int.toNat_lt_toNat (by omega : 0 < π z)).mpr
          rw [map_add]
          omega
        exact ih (π (z+e)).toNat heless (z+e) rfl he0 (by rw [map_add]; omega)
  intro z hz0 hzψ
  exact hlevel (π z).toNat z rfl hz0 hzψ

end
end NivatTrial.ColleWedgeRecurrence
