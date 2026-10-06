import NivatTrial.ColleHalfPlanePeriod
import NivatTrial.IncrementSupport
import NivatTrial.FirstHalfPlane

/-! A sufficiently wide strip detects every solution of a product of
transverse difference equations. This gives the many-component version of
periodicity propagation from a complete band. -/

namespace NivatTrial.ColleStripRigidity

open NivatTrial.Geometry NivatTrial.Periodicity NivatTrial.PeriodicDifference
open NivatTrial.OneSidedRecurrence NivatTrial.IncrementSupport
open NivatTrial.FirstHalfPlane NivatTrial.ColleHalfPlanePeriod
open scoped Classical
noncomputable section

def widthBudget (π : Lattice →+ ℤ) : List Lattice → ℤ
  | [] => 0
  | h :: hs => |π h| + widthBudget π hs

theorem widthBudget_nonneg (π : Lattice →+ ℤ) (hs : List Lattice) :
    0 ≤ widthBudget π hs := by
  induction hs with
  | nil => simp [widthBudget]
  | cons h hs ih =>
    simp only [widthBudget]
    have hh := abs_nonneg (π h)
    omega

theorem offset_score_bound (π : Lattice →+ ℤ) (hs : List Lattice)
    (e : Lattice) (he : e ∈ offsets hs) :
    |π e| ≤ widthBudget π hs := by
  induction hs generalizing e with
  | nil =>
    have he0 : e = 0 := by simpa [offsets] using he
    subst e
    simp [widthBudget]
  | cons h hs ih =>
    have htail := widthBudget_nonneg π hs
    rcases Finset.mem_union.mp he with hleft | hright
    · have hbound := ih e hleft
      simp only [widthBudget]
      have hh := abs_nonneg (π h)
      omega
    · obtain ⟨e0,he0,rfl⟩ := Finset.mem_image.mp hright
      have hbound := ih e0 he0
      rw [map_add]
      have htri := abs_add_le (π h) (π e0)
      simp only [widthBudget]
      omega

variable {A : Type*} [AddCommGroup A]

/-- If all annihilating factors cross the strip, a wide zero band forces
global vanishing. The factor 2 leaves room for all finite difference
offsets on both sides of the central band. -/
theorem zero_of_transverse_product_on_strip (π : Lattice →+ ℤ)
    (hs : List Lattice) (f : Lattice → A)
    (htrans : ∀ h ∈ hs, π h ≠ 0)
    (hann : iteratedIncrement hs f = 0)
    (a b : ℤ) (hwidth : 2 * widthBudget π hs ≤ b-a)
    (hzero : ∀ z ∈ coordinateStrip π a b, f z = 0) : f = 0 := by
  induction hs generalizing a b with
  | nil => simpa using hann
  | cons h hs ih =>
    let M := widthBudget π hs
    let g := iteratedIncrement hs f
    have htransh : π h ≠ 0 := htrans h (by simp)
    have htransTail : ∀ k ∈ hs, π k ≠ 0 := by
      intro k hk
      exact htrans k (by simp [hk])
    have hzeroG : ∀ z ∈ coordinateStrip π (a+M) (b-M), g z = 0 := by
      intro z hz
      have hlocal : ∀ e ∈ offsets hs, f (z+e) = (0 : Lattice → A) (z+e) := by
        intro e he
        have hbound := offset_score_bound π hs e he
        have hlow : -M ≤ π e := (abs_le.mp hbound).1
        have hhigh : π e ≤ M := (abs_le.mp hbound).2
        have hz' : z+e ∈ coordinateStrip π a b := by
          change a ≤ π (z+e) ∧ π (z+e) ≤ b
          rw [map_add]
          change a+M ≤ π z ∧ π z ≤ b-M at hz
          constructor <;> omega
        exact hzero _ hz'
      have heq := iteratedIncrement_congr_at hs f (fun _ => 0) z hlocal
      change g z = iteratedIncrement hs (0 : Lattice → A) z at heq
      simpa only [iteratedIncrement_zero, Pi.zero_apply] using heq
    have hgper : IsPeriod g h := by
      intro z
      have heq := congrFun hann z
      change g (z+h)-g z = 0 at heq
      exact sub_eq_zero.mp heq
    have hwidthG : |π h| ≤ (b-M)-(a+M) := by
      change 2 * (|π h| + M) ≤ b-a at hwidth
      have hh := abs_nonneg (π h)
      omega
    have hgzero : g = 0 := by
      by_cases hp : 0 < π h
      · apply period_of_zero_on_transverse_strip g π h hgper hp
          (a+M) (b-M) (by simpa [abs_of_pos hp] using hwidthG) hzeroG
      · have hn : 0 < π (-h) := by simp; omega
        have hneg : π h < 0 := by omega
        have hwidthneg : π (-h) ≤ (b-M)-(a+M) := by
          rw [map_neg]
          rw [abs_of_neg hneg] at hwidthG
          exact hwidthG
        apply period_of_zero_on_transverse_strip g π (-h) hgper.neg hn
          (a+M) (b-M) hwidthneg hzeroG
    apply ih htransTail hgzero a b
    · change 2 * M ≤ b-a
      change 2 * (|π h| + M) ≤ b-a at hwidth
      have hh := abs_nonneg (π h)
      omega
    · exact hzero

variable {ι : Type*} [Fintype ι]

/-- The exact band threshold for a fixed finite periodic decomposition. -/
def transverseStripWidth (u : Lattice) (h : ι → Lattice) : ℤ :=
  2 * widthBudget (height u)
    ((Finset.univ.filter (fun i => height u (h i) ≠ 0)).toList.map h)

theorem transverseStripWidth_nonneg (u : Lattice) (h : ι → Lattice) :
    0 ≤ transverseStripWidth u h := by
  unfold transverseStripWidth
  exact mul_nonneg (by omega) (widthBudget_nonneg _ _)

/-- General many-component strip rigidity: any positive period along the
strip direction extends, after a fixed positive multiple, to the entire
configuration. No bound on the values of the periodic components is needed. -/
theorem period_of_wide_strip (F : ι → Lattice → A) (h : ι → Lattice)
    (hper : ∀ i, IsPeriod (F i) (h i)) (hzero : ∀ i, h i ≠ 0)
    (u : Lattice) (q : ℕ) (hq : 0 < q) (a b : ℤ)
    (hwidth : transverseStripWidth u h ≤ b-a)
    (hstrip : ∀ z ∈ coordinateStrip (height u) a b,
      (∑ i, F i) (z+q•u) = (∑ i, F i) z) :
    ∃ Q : ℕ, 0 < Q ∧ IsPeriod (∑ i, F i) (Q•u) := by
  let π := height u
  have hchosen (i : ι) :
      ∃ m : ℕ, 0 < m ∧ (π (h i) = 0 → IsPeriod (F i) (m•u)) := by
    by_cases hi : π (h i) = 0
    · have hdet : det (h i) u = 0 := by
        rw [det_swap]
        simpa [π] using congrArg Neg.neg hi
      obtain ⟨m,hm,hpm⟩ := parallel_direction_period (hper i) (hzero i) u hdet
      exact ⟨m,hm,fun _ => hpm⟩
    · exact ⟨1,by omega,fun hbad => (hi hbad).elim⟩
  let m (i : ι) : ℕ := Classical.choose (hchosen i)
  have hm (i : ι) : 0 < m i ∧ (π (h i) = 0 → IsPeriod (F i) (m i•u)) :=
    Classical.choose_spec (hchosen i)
  let M : ℕ := ∏ i, m i
  have hM : 0 < M := Finset.prod_pos (fun i _ => (hm i).1)
  have hMper (i : ι) (hi : π (h i) = 0) : IsPeriod (F i) (M•u) := by
    obtain ⟨k,hk⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
    dsimp only [M]
    rw [hk]
    simpa only [mul_comm (m i) k,mul_smul] using ((hm i).2 hi).nsmul k
  let Q : ℕ := q*M
  have hQ : 0 < Q := Nat.mul_pos hq hM
  have hQper (i : ι) (hi : π (h i) = 0) : IsPeriod (F i) (Q•u) := by
    simpa only [Q,mul_smul] using (hMper i hi).nsmul q
  have hπqu : π (q•u) = 0 := by
    change det u (q•u) = 0
    rw [det_nsmul_right,det_self,mul_zero]
  have hlocal : PeriodicOn (∑ i, F i) (coordinateStrip π a b) (q•u) :=
    ⟨strip_invariant_under_kernel π a b _ hπqu,hstrip⟩
  have hlocalQ : PeriodicOn (∑ i, F i) (coordinateStrip π a b) (Q•u) := by
    simpa only [Q,mul_comm q M,mul_smul] using hlocal.nsmul M
  let hs : List Lattice :=
    ((Finset.univ.filter (fun i => π (h i) ≠ 0)).toList.map h)
  have htrans : ∀ k ∈ hs, π k ≠ 0 := by
    intro k hk
    obtain ⟨i,hi,hik⟩ := List.mem_map.mp hk
    have hi' := (Finset.mem_filter.mp (Finset.mem_toList.mp hi)).2
    simpa [hik] using hi'
  let g : Lattice → A := increment (∑ i, F i) (Q•u)
  have hann : iteratedIncrement hs g = 0 := by
    rw [show iteratedIncrement hs g =
      increment (iteratedIncrement hs (∑ i,F i)) (Q•u) from
        iteratedIncrement_commute hs (∑ i,F i) (Q•u)]
    rw [iteratedIncrement_sum]
    funext z
    simp only [increment, Finset.sum_apply, Pi.zero_apply]
    change (∑ i, iteratedIncrement hs (F i) (z+Q•u)) -
      (∑ i, iteratedIncrement hs (F i) z) = 0
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : π (h i) = 0
    · exact sub_eq_zero.mpr ((iteratedIncrement_period hs (hQper i hi)) z)
    · have himem : h i ∈ hs := by
        apply List.mem_map.mpr
        exact ⟨i,Finset.mem_toList.mpr
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩),rfl⟩
      have hkill := factor_kills_of_mem hs (h i) himem (F i) (hper i)
      rw [congrFun hkill (z+Q•u),congrFun hkill z]
      simp
  have hgzero : ∀ z ∈ coordinateStrip π a b, g z = 0 := by
    intro z hz
    exact sub_eq_zero.mpr (hlocalQ.2 z hz)
  have hglobal := zero_of_transverse_product_on_strip π hs g htrans hann
    a b hwidth hgzero
  refine ⟨Q,hQ,?_⟩
  intro z
  exact sub_eq_zero.mp (congrFun hglobal z)

end
end NivatTrial.ColleStripRigidity
