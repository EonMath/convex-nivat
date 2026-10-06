import NivatTrial.Isolation

/-! Extremal half-plane support and the nonvanishing step of Lemma 4.1. -/

namespace NivatTrial.HalfPlane

open NivatTrial.Algebra NivatTrial.Geometry NivatTrial.Differences
open NivatTrial.Periodicity NivatTrial.Isolation
open Filter

noncomputable section

def UpperSupport (v : G) (J : G → ℂ) : Prop :=
  ∃ c : ℤ, ∀ z, c < det v z → J z = 0

def LowerSupport (v : G) (J : G → ℂ) : Prop :=
  ∃ c : ℤ, ∀ z, det v z < c → J z = 0

theorem upperSupport_zero (v : G) : UpperSupport v 0 := ⟨0, fun _ _ => rfl⟩

theorem lowerSupport_zero (v : G) : LowerSupport v 0 := ⟨0, fun _ _ => rfl⟩

theorem upperSupport_add (v : G) {J K : G → ℂ}
    (hJ : UpperSupport v J) (hK : UpperSupport v K) : UpperSupport v (J + K) := by
  obtain ⟨a, ha⟩ := hJ
  obtain ⟨b, hb⟩ := hK
  refine ⟨max a b, ?_⟩
  intro z hz
  have hz₁ : a < det v z := lt_of_le_of_lt (le_max_left _ _) hz
  have hz₂ : b < det v z := lt_of_le_of_lt (le_max_right _ _) hz
  simp [ha z hz₁, hb z hz₂]

theorem upperSupport_neg (v : G) {J : G → ℂ} (hJ : UpperSupport v J) :
    UpperSupport v (-J) := by
  obtain ⟨a, ha⟩ := hJ
  exact ⟨a, fun z hz => by simp [ha z hz]⟩

theorem upperSupport_sub (v : G) {J K : G → ℂ}
    (hJ : UpperSupport v J) (hK : UpperSupport v K) : UpperSupport v (J - K) := by
  simpa only [sub_eq_add_neg] using upperSupport_add v hJ (upperSupport_neg v hK)

theorem upperSupport_translate (v h : G) {J : G → ℂ} (hJ : UpperSupport v J) :
    UpperSupport v (fun z => J (z + h)) := by
  obtain ⟨a, ha⟩ := hJ
  refine ⟨a - det v h, ?_⟩
  intro z hz
  apply ha
  rw [det_add_right]
  omega

theorem lowerSupport_iff_upperSupport_neg (v : G) (J : G → ℂ) :
    LowerSupport v J ↔ UpperSupport (-v) J := by
  have hn (z : G) : det (-v) z = -det v z := by simp [det]; ring
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    intro z hz
    apply ha
    rw [hn] at hz
    omega
  · rintro ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    intro z hz
    apply ha
    rw [hn]
    omega

/-- A transverse period and one-sided vanishing force the whole field to vanish. -/
theorem eq_zero_of_upperSupport_period (v h : G) (J : G → ℂ)
    (hJ : UpperSupport v J) (hperiod : IsPeriod J h) (htransverse : det v h ≠ 0) :
    J = 0 := by
  obtain ⟨c, hc⟩ := hJ
  funext z
  by_cases hpos : 0 < det v h
  · obtain ⟨n, hn⟩ := (eventually_det_gt v h z c hpos).exists
    have hzero := hc (z + n • h) hn
    rw [hperiod.nsmul n z] at hzero
    exact hzero
  · have hneg : 0 < det v (-h) := by rw [det_neg_right]; omega
    obtain ⟨n, hn⟩ := (eventually_det_gt v (-h) z c hneg).exists
    have hzero := hc (z + n • (-h)) hn
    rw [hperiod.neg.nsmul n z] at hzero
    exact hzero

theorem eq_zero_of_lowerSupport_period (v h : G) (J : G → ℂ)
    (hJ : LowerSupport v J) (hperiod : IsPeriod J h) (htransverse : det v h ≠ 0) :
    J = 0 := by
  apply eq_zero_of_upperSupport_period (-v) h J
    ((lowerSupport_iff_upperSupport_neg v J).mp hJ) hperiod
  have hn : det (-v) h = -det v h := by simp [det]; ring
  rw [hn]
  exact neg_ne_zero.mpr htransverse

theorem upperSupport_difference (v h : G) {J : G → ℂ} (hJ : UpperSupport v J) :
    UpperSupport v (act (difference h) J) := by
  have heq : act (difference h) J = (fun z => J (z + h)) - J := by
    funext z
    simp
  rw [heq]
  exact upperSupport_sub v (upperSupport_translate v h hJ) hJ

theorem difference_ne_zero_of_upperSupport (v h : G) {J : G → ℂ}
    (hJ : UpperSupport v J) (hne : J ≠ 0) (htransverse : det v h ≠ 0) :
    act (difference h) J ≠ 0 := by
  intro heq
  exact hne (eq_zero_of_upperSupport_period v h J hJ
    (period_of_difference_eq_zero h J heq) htransverse)

theorem upperSupport_product {ι : Type*} (s : Finset ι) (H : ι → G)
    (v : G) {J : G → ℂ} (hJ : UpperSupport v J) :
    UpperSupport v (act (differenceProduct s H) J) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hJ
  | @insert i s hi ih =>
    rw [differenceProduct_insert s H hi, act_mul]
    exact upperSupport_difference v (H i) ih

/-- The product of transverse differences is injective on one-sided fields. -/
theorem product_ne_zero_of_upperSupport {ι : Type*} (s : Finset ι) (H : ι → G)
    (v : G) {J : G → ℂ} (hJ : UpperSupport v J) (hne : J ≠ 0)
    (htransverse : ∀ i ∈ s, det v (H i) ≠ 0) :
    act (differenceProduct s H) J ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hne
  | @insert i s hi ih =>
    rw [differenceProduct_insert s H hi, act_mul]
    exact difference_ne_zero_of_upperSupport v (H i)
      (upperSupport_product s H v hJ)
      (ih (fun j hj => htransverse j (Finset.mem_insert_of_mem hj)))
      (htransverse i (Finset.mem_insert_self i s))

theorem product_ne_zero_of_lowerSupport {ι : Type*} (s : Finset ι) (H : ι → G)
    (v : G) {J : G → ℂ} (hJ : LowerSupport v J) (hne : J ≠ 0)
    (htransverse : ∀ i ∈ s, det v (H i) ≠ 0) :
    act (differenceProduct s H) J ≠ 0 := by
  apply product_ne_zero_of_upperSupport s H (-v)
    ((lowerSupport_iff_upperSupport_neg v J).mp hJ) hne
  intro i hi
  have hn : det (-v) (H i) = -det v (H i) := by simp [det]; ring
  rw [hn]
  exact neg_ne_zero.mpr (htransverse i hi)

theorem lowerSupport_product {ι : Type*} (s : Finset ι) (H : ι → G)
    (v : G) {J : G → ℂ} (hJ : LowerSupport v J) :
    LowerSupport v (act (differenceProduct s H) J) := by
  rw [lowerSupport_iff_upperSupport_neg] at hJ ⊢
  exact upperSupport_product s H (-v) hJ

end

end NivatTrial.HalfPlane
