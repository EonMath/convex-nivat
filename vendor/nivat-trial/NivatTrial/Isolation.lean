import NivatTrial.Strips
import NivatTrial.Periodicity

/-! The isolating configurations and pure tails of §2.1. -/

namespace NivatTrial.Isolation

open NivatTrial.Algebra NivatTrial.Geometry NivatTrial.Dynamics NivatTrial.Periodicity
open Filter
open scoped Classical

noncomputable section

theorem eventually_det_gt (v h z : Lattice) (b : ℤ) (hh : 0 < det v h) :
    ∀ᶠ n : ℕ in atTop, b < det v (z + n • h) := by
  refine Filter.eventually_atTop.mpr ⟨(b - det v z).toNat + 1, ?_⟩
  intro n hn
  have h₁ : b - det v z ≤ ((b - det v z).toNat : ℤ) := by omega
  have h₂ : ((b - det v z).toNat : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hn
  have hn₀ : (0 : ℤ) ≤ n := Nat.cast_nonneg _
  rw [det_add_right, det_nsmul_right]
  nlinarith

theorem eventually_det_lt (v h z : Lattice) (a : ℤ) (hh : det v h < 0) :
    ∀ᶠ n : ℕ in atTop, det v (z + n • h) < a := by
  refine Filter.eventually_atTop.mpr ⟨(det v z - a).toNat + 1, ?_⟩
  intro n hn
  have h₁ : det v z - a ≤ ((det v z - a).toNat : ℤ) := by omega
  have h₂ : ((det v z - a).toNat : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hn
  have hn₀ : (0 : ℤ) ≤ n := Nat.cast_nonneg _
  rw [det_add_right, det_nsmul_right]
  nlinarith

/-- Eventual agreement on each site yields membership in the finite-window hull. -/
theorem mem_languageHull_of_eventually_shift {A : Type*} (θ ξ : Lattice → A) (h : Lattice)
    (hevent : ∀ z, ∀ᶠ n : ℕ in atTop, θ (z + n • h) = ξ z) :
    ξ ∈ languageHull θ := by
  intro S
  have hall : ∀ᶠ n : ℕ in atTop, ∀ z : S, θ ((z : Lattice) + n • h) = ξ z :=
    Filter.eventually_all.mpr (fun z => hevent z)
  obtain ⟨n, hn⟩ := hall.exists
  refine ⟨n • h, ?_⟩
  intro z hz
  simpa only [add_comm] using hn ⟨z, hz⟩

/-- A periodic field that is exactly a half-plane tail is a genuine orbit limit. -/
theorem right_tail_mem_languageHull {A : Type*} (θ R : Lattice → A)
    (v h : Lattice) (b : ℤ) (hp : IsPeriod R h) (hh : 0 < det v h)
    (hagree : ∀ z, b < det v z → θ z = R z) : R ∈ languageHull θ := by
  apply mem_languageHull_of_eventually_shift θ R h
  intro z
  filter_upwards [eventually_det_gt v h z b hh] with n hn
  rw [hagree _ hn, hp.nsmul n z]

theorem left_tail_mem_languageHull {A : Type*} (θ L : Lattice → A)
    (v h : Lattice) (a : ℤ) (hp : IsPeriod L h) (hh : det v h < 0)
    (hagree : ∀ z, det v z < a → θ z = L z) : L ∈ languageHull θ := by
  apply mem_languageHull_of_eventually_shift θ L h
  intro z
  filter_upwards [eventually_det_lt v h z a hh] with n hn
  rw [hagree _ hn, hp.nsmul n z]

variable {ι A : Type*} [Fintype ι] [AddCommGroup A]

def tailFor (T : Strips.StripSystem ι A) (h : Lattice) (j : ι) : Lattice → A :=
  if 0 < det (T.direction j) h then T.rightTail j else T.leftTail j

def background (T : Strips.StripSystem ι A) (i : ι) (h : Lattice) : Lattice → A :=
  fun z => ∑ j ∈ Finset.univ.erase i, tailFor T h j z

def isolated (T : Strips.StripSystem ι A) (i : ι) (h : Lattice) : Lattice → A :=
  fun z => T.component i z + background T i h z

theorem tailFor_period (T : Strips.StripSystem ι A) (h : Lattice) (j : ι)
    (hL : IsPeriod (T.leftTail j) h) (hR : IsPeriod (T.rightTail j) h) :
    IsPeriod (tailFor T h j) h := by
  unfold tailFor
  split_ifs <;> assumption

theorem background_period (T : Strips.StripSystem ι A) (i : ι) (h : Lattice)
    (hL : ∀ j, IsPeriod (T.leftTail j) h) (hR : ∀ j, IsPeriod (T.rightTail j) h) :
    IsPeriod (background T i h) h := by
  intro z
  apply Finset.sum_congr rfl
  intro j _
  exact tailFor_period T h j (hL j) (hR j) z

theorem isolated_period (T : Strips.StripSystem ι A) (i : ι) (h : Lattice)
    (hF : IsPeriod (T.component i) h)
    (hL : ∀ j, IsPeriod (T.leftTail j) h) (hR : ∀ j, IsPeriod (T.rightTail j) h) :
    IsPeriod (isolated T i h) h := by
  intro z
  simp only [isolated, hF z, background_period T i h hL hR z]

theorem component_eventually_tail (T : Strips.StripSystem ι A) (h z : Lattice) (j : ι)
    (htransverse : det (T.direction j) h ≠ 0)
    (hL : IsPeriod (T.leftTail j) h) (hR : IsPeriod (T.rightTail j) h) :
    ∀ᶠ n : ℕ in atTop, T.component j (z + n • h) = tailFor T h j z := by
  by_cases hpos : 0 < det (T.direction j) h
  · filter_upwards [eventually_det_gt (T.direction j) h z (T.upper j) hpos] with n hn
    rw [T.right_agreement j _ hn, hR.nsmul n z]
    simp [tailFor, hpos]
  · have hneg : det (T.direction j) h < 0 := lt_of_le_of_ne (le_of_not_gt hpos) htransverse
    filter_upwards [eventually_det_lt (T.direction j) h z (T.lower j) hneg] with n hn
    rw [T.left_agreement j _ hn, hL.nsmul n z]
    simp [tailFor, hpos]

theorem total_eventually_isolated (T : Strips.StripSystem ι A) (i : ι) (h z : Lattice)
    (hF : IsPeriod (T.component i) h)
    (hL : ∀ j, IsPeriod (T.leftTail j) h) (hR : ∀ j, IsPeriod (T.rightTail j) h)
    (htransverse : ∀ j, j ≠ i → det (T.direction j) h ≠ 0) :
    ∀ᶠ n : ℕ in atTop, T.total (z + n • h) = isolated T i h z := by
  have heach (j : ι) : ∀ᶠ n : ℕ in atTop,
      T.component j (z + n • h) = if j = i then T.component i z else tailFor T h j z := by
    by_cases hji : j = i
    · subst j
      exact Filter.Eventually.of_forall (fun n => by
        rw [if_pos rfl]
        exact hF.nsmul n z)
    · simpa only [if_neg hji] using
        component_eventually_tail T h z j (htransverse j hji) (hL j) (hR j)
  have hall := Filter.eventually_all.mpr heach
  filter_upwards [hall] with n hn
  unfold Strips.StripSystem.total isolated background
  rw [← Finset.sum_erase_add Finset.univ (fun j => T.component j (z + n • h))
    (Finset.mem_univ i)]
  rw [hn i, if_pos rfl, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [hn j, if_neg (Finset.ne_of_mem_erase hj)]

/-- The two signs of §2.1 are obtained by choosing `h = Hᵢ` or `h = -Hᵢ`. -/
theorem isolated_mem_languageHull (T : Strips.StripSystem ι A) (i : ι) (h : Lattice)
    (hF : IsPeriod (T.component i) h)
    (hL : ∀ j, IsPeriod (T.leftTail j) h) (hR : ∀ j, IsPeriod (T.rightTail j) h)
    (htransverse : ∀ j, j ≠ i → det (T.direction j) h ≠ 0) :
    isolated T i h ∈ languageHull T.total := by
  exact mem_languageHull_of_eventually_shift T.total (isolated T i h) h
    (fun z => total_eventually_isolated T i h z hF hL hR htransverse)

theorem isolated_positive_mem_languageHull (T : Strips.StripSystem ι A) (i : ι)
    (htransverse : ∀ j, j ≠ i → det (T.direction j) (T.period i) ≠ 0) :
    isolated T i (T.period i) ∈ languageHull T.total := by
  exact isolated_mem_languageHull T i (T.period i) (T.component_period i)
    (fun j => T.left_period j i) (fun j => T.right_period j i) htransverse

theorem isolated_negative_mem_languageHull (T : Strips.StripSystem ι A) (i : ι)
    (htransverse : ∀ j, j ≠ i → det (T.direction j) (T.period i) ≠ 0) :
    isolated T i (-T.period i) ∈ languageHull T.total := by
  apply isolated_mem_languageHull T i (-T.period i)
    (IsPeriod.neg (T.component_period i))
    (fun j => IsPeriod.neg (T.left_period j i))
    (fun j => IsPeriod.neg (T.right_period j i))
  intro j hji
  simpa only [det_neg_right, neg_ne_zero] using htransverse j hji

theorem transverse_of_parallel_period (T : Strips.StripSystem ι A) (i : ι)
    (k : ℤ) (hk : k ≠ 0) (hperiod : T.period i = k • T.direction i) :
    ∀ j, j ≠ i → det (T.direction j) (T.period i) ≠ 0 := by
  intro j hji
  rw [hperiod, det_zsmul_right]
  exact mul_ne_zero hk (T.independent j i hji)

theorem isolated_left_agreement (T : Strips.StripSystem ι A) (i : ι) (h z : Lattice)
    (hz : det (T.direction i) z < T.lower i) :
    isolated T i h z = T.leftTail i z + background T i h z := by
  rw [isolated, T.left_agreement i z hz]

theorem isolated_right_agreement (T : Strips.StripSystem ι A) (i : ι) (h z : Lattice)
    (hz : T.upper i < det (T.direction i) z) :
    isolated T i h z = T.rightTail i z + background T i h z := by
  rw [isolated, T.right_agreement i z hz]

end

end NivatTrial.Isolation
