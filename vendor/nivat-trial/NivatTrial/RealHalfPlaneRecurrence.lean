import NivatTrial.Nonexpansive
import NivatTrial.IncrementSupport

/-! Transverse products of differences are determined by any real half-plane.
The coefficients may be unbounded; only the translation recurrence is used. -/

namespace NivatTrial.RealHalfPlaneRecurrence

open NivatTrial.Nonexpansive NivatTrial.Periodicity NivatTrial.PeriodicDifference
open NivatTrial.OneSidedRecurrence NivatTrial.IncrementSupport NivatTrial.Dynamics
open scoped Classical
noncomputable section

variable {B : Type*} [AddCommGroup B]

theorem eq_zero_of_positive_period (f : Lattice → B) (v : Plane) (b : ℝ)
    (h : Lattice) (hh : 0 < score v h) (hp : IsPeriod f h)
    (hf : ∀ z, b ≤ score v z → f z = 0) : f = 0 := by
  funext z
  obtain ⟨n,hn⟩ := exists_nat_gt ((b-score v z) / score v h)
  have hbound : b ≤ score v (z+n•h) := by
    rw [score_add,score_nsmul]
    have he := (div_lt_iff₀ hh).mp hn
    linarith
  have heq := (hp.nsmul n) z
  exact heq.symm.trans (hf _ hbound)

theorem eq_zero_of_transverse_period (f : Lattice → B) (v : Plane) (b : ℝ)
    (h : Lattice) (hh : score v h ≠ 0) (hp : IsPeriod f h)
    (hf : ∀ z, b ≤ score v z → f z = 0) : f = 0 := by
  rcases lt_or_gt_of_ne hh with hn | hp'
  · apply eq_zero_of_positive_period f v b (-h) _ hp.neg hf
    rw [score_neg]
    linarith
  · exact eq_zero_of_positive_period f v b h hp' hp hf

theorem increment_zero_on_halfPlane (f : Lattice → B) (v : Plane)
    (b : ℝ) (h : Lattice) (hf : ∀ z, b ≤ score v z → f z = 0) :
    ∀ z, max b (b-score v h) ≤ score v z → increment f h z = 0 := by
  intro z hz
  have h1 : b ≤ score v z := (le_max_left _ _).trans hz
  have h2 : b ≤ score v (z+h) := by
    rw [score_add]
    have ht := (le_max_right b (b-score v h)).trans hz
    linarith
  simp only [increment,hf z h1,hf (z+h) h2,sub_self]

theorem iterated_zero_on_halfPlane (hs : List Lattice) (f : Lattice → B)
    (v : Plane) (b : ℝ) (hf : ∀ z, b ≤ score v z → f z = 0) :
    ∃ c : ℝ, ∀ z, c ≤ score v z → iteratedIncrement hs f z = 0 := by
  induction hs with
  | nil => exact ⟨b,hf⟩
  | cons h hs ih =>
    obtain ⟨c,hc⟩ := ih
    exact ⟨max c (c-score v h),increment_zero_on_halfPlane _ v c h hc⟩

/-- A product of transverse difference operators has no nonzero solution
supported on the opposite side of a line. -/
theorem eq_zero_of_transverse_product (hs : List Lattice) (f : Lattice → B)
    (v : Plane) (b : ℝ) (htrans : ∀ h ∈ hs, score v h ≠ 0)
    (hann : iteratedIncrement hs f = 0)
    (hf : ∀ z, b ≤ score v z → f z = 0) : f = 0 := by
  induction hs generalizing f with
  | nil => exact hann
  | cons h hs ih =>
    have hp : IsPeriod (iteratedIncrement hs f) h := by
      intro z
      exact sub_eq_zero.mp (congrFun hann z)
    obtain ⟨c,hc⟩ := iterated_zero_on_halfPlane hs f v b hf
    have hzero := eq_zero_of_transverse_period _ v c h (htrans h (by simp)) hp hc
    exact ih f (fun k hk => htrans k (by simp [hk])) hzero hf

theorem eq_of_transverse_product (hs : List Lattice) (x y : Lattice → B)
    (v : Plane) (b : ℝ) (htrans : ∀ h ∈ hs, score v h ≠ 0)
    (hx : iteratedIncrement hs x = 0) (hy : iteratedIncrement hs y = 0)
    (hagree : ∀ z, b ≤ score v z → x z = y z) : x = y := by
  have hann : iteratedIncrement hs (x-y) = 0 := by
    rw [iteratedIncrement_sub,hx,hy,sub_self]
  have hz := eq_zero_of_transverse_product hs (x-y) v b htrans hann (by
    intro z hz
    exact sub_eq_zero.mpr (hagree z hz))
  exact sub_eq_zero.mp hz

theorem oneSidedExpansive_of_transverse_product {A : Type*} [Fintype A]
    (θ : Lattice → A) (w : A → ℤ) (hw : Function.Injective w)
    (hs : List Lattice) (v : Plane) (htrans : ∀ h ∈ hs, score v h ≠ 0)
    (hann : iteratedIncrement hs (encode w θ) = 0) : OneSidedExpansive θ v := by
  rintro ⟨x,hx,y,hy,hne,hagree⟩
  have hxa := iteratedIncrement_passes_to_languageHull hs (encode w θ) (encode w x)
    (encode_mem_languageHull w hx) hann
  have hya := iteratedIncrement_passes_to_languageHull hs (encode w θ) (encode w y)
    (encode_mem_languageHull w hy) hann
  have he := eq_of_transverse_product hs (encode w x) (encode w y) v 0 htrans hxa hya (by
    intro z hz
    exact congrArg w (hagree z hz))
  apply hne
  funext z
  exact hw (congrFun he z)

end
end NivatTrial.RealHalfPlaneRecurrence
