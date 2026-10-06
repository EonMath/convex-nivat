import NivatTrial.Differences
import NivatTrial.Geometry
import NivatTrial.FirstCase

/-! Lemma 1.1 and the first-case bound for configurations with periodic tails.

The common period vectors have already been chosen: each preserves its own
component and every pure tail. These are exactly the properties used in §1.
Primitive directions and non-double-periodicity are unnecessary for this case.
-/

namespace NivatTrial.Strips

open NivatTrial.Algebra NivatTrial.Differences NivatTrial.Geometry
open scoped Classical

noncomputable section

variable {ι A : Type*} [Fintype ι] [AddCommGroup A]

/-- The periodic-tail data used by the first case of the paper. -/
structure StripSystem (ι A : Type*) [Fintype ι] [AddCommGroup A] where
  direction : ι → G
  period : ι → G
  lower : ι → ℤ
  upper : ι → ℤ
  component : ι → G → A
  leftTail : ι → G → A
  rightTail : ι → G → A
  component_period : ∀ i z, component i (z + period i) = component i z
  left_period : ∀ i j z, leftTail i (z + period j) = leftTail i z
  right_period : ∀ i j z, rightTail i (z + period j) = rightTail i z
  left_agreement : ∀ i z, det (direction i) z < lower i → component i z = leftTail i z
  right_agreement : ∀ i z, upper i < det (direction i) z → component i z = rightTail i z
  independent : ∀ i j, i ≠ j → det (direction i) (direction j) ≠ 0

namespace StripSystem

variable (T : StripSystem ι A)

def total (z : G) : A := ∑ i, T.component i z

def operator : Laurent := differenceProduct Finset.univ T.period

def cofactor (i : ι) : Laurent :=
  differenceProduct (Finset.univ.erase i) T.period

theorem operator_factor (i : ι) : T.operator = T.cofactor i * difference (T.period i) := by
  classical
  exact differenceProduct_factor _ _ (Finset.mem_univ i)

theorem operator_const [Nonempty ι] (b : ℂ) : act T.operator (fun _ => b) = 0 := by
  exact differenceProduct_const _ _ Finset.univ_nonempty b

theorem operator_ne_zero (h : ∀ i, T.period i ≠ 0) : T.operator ≠ 0 := by
  exact differenceProduct_ne_zero _ _ (fun i _ => h i)

/-- All offsets whose values can be inspected while cancelling any factor. -/
def footprint (W : Finset G) : Finset G :=
  Finset.univ.biUnion fun i => (T.cofactor i).coeff.support.biUnion fun u =>
    (W.image fun w => u + w) ∪ (W.image fun w => u + T.period i + w)

theorem mem_footprint_left (W : Finset G) (i : ι) (u : G)
    (hu : u ∈ (T.cofactor i).coeff.support) (w : W) :
    u + w ∈ T.footprint W := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨u, hu, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨w, w.property, rfl⟩)⟩

theorem mem_footprint_right (W : Finset G) (i : ι) (u : G)
    (hu : u ∈ (T.cofactor i).coeff.support) (w : W) :
    u + T.period i + w ∈ T.footprint W := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨u, hu, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, w.property, rfl⟩)⟩

/-- A convenient finite upper bound, rather than the smallest possible radius. -/
def radius (W : Finset G) (i : ι) : ℤ :=
  ∑ u ∈ T.footprint W, |det (T.direction i) u|

theorem radius_nonneg (W : Finset G) (i : ι) : 0 ≤ T.radius W i := by
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem abs_det_le_radius (W : Finset G) (i : ι) {u : G}
    (hu : u ∈ T.footprint W) : |det (T.direction i) u| ≤ T.radius W i := by
  exact Finset.single_le_sum (f := fun u => |det (T.direction i) u|)
    (fun _ _ => abs_nonneg _) hu

def active (W : Finset G) (i : ι) (z : G) : Prop :=
  T.lower i - T.radius W i ≤ det (T.direction i) z ∧
    det (T.direction i) z ≤ T.upper i + T.radius W i

theorem outside_active (W : Finset G) (i : ι) (z : G) (h : ¬T.active W i z) :
    det (T.direction i) z < T.lower i - T.radius W i ∨
      T.upper i + T.radius W i < det (T.direction i) z := by
  unfold active at h
  omega

theorem below_on_footprint (W : Finset G) (i : ι) (z : G)
    (hz : det (T.direction i) z < T.lower i - T.radius W i)
    {u : G} (hu : u ∈ T.footprint W) : det (T.direction i) (z + u) < T.lower i := by
  have hbound := (abs_le.mp (T.abs_det_le_radius W i hu)).2
  rw [det_add_right]
  omega

theorem above_on_footprint (W : Finset G) (i : ι) (z : G)
    (hz : T.upper i + T.radius W i < det (T.direction i) z)
    {u : G} (hu : u ∈ T.footprint W) : T.upper i < det (T.direction i) (z + u) := by
  have hbound := (abs_le.mp (T.abs_det_le_radius W i hu)).1
  rw [det_add_right]
  omega

/-- An inactive component is the same pure tail throughout the whole footprint. -/
theorem inactive_component_period (W : Finset G) (i j : ι) (z u : G)
    (hinactive : ¬T.active W i z)
    (hu : u ∈ T.footprint W) (hup : u + T.period j ∈ T.footprint W) :
    T.component i (z + u + T.period j) = T.component i (z + u) := by
  rcases T.outside_active W i z hinactive with hleft | hright
  · have h₁ := T.below_on_footprint W i z hleft hu
    have h₂ := T.below_on_footprint W i z hleft hup
    rw [add_assoc]
    rw [T.left_agreement i _ h₂, T.left_agreement i _ h₁]
    simpa only [add_assoc] using T.left_period i j (z + u)
  · have h₁ := T.above_on_footprint W i z hright hu
    have h₂ := T.above_on_footprint W i z hright hup
    rw [add_assoc]
    rw [T.right_agreement i _ h₂, T.right_agreement i _ h₁]
    simpa only [add_assoc] using T.right_period i j (z + u)

def localObservation (W : Finset G) (φ : (W → A) → ℂ) (z : G) : ℂ :=
  φ (fun w => T.total (z + w))

/-- At most one active direction means that some factor cancels every local term. -/
theorem localObservation_period_on_cofactor (W : Finset G) (φ : (W → A) → ℂ)
    (z : G) (j : ι) (hinactive : ∀ i, i ≠ j → ¬T.active W i z)
    (u : G) (hu : u ∈ (T.cofactor j).coeff.support) :
    T.localObservation W φ (z + u + T.period j) = T.localObservation W φ (z + u) := by
  apply congrArg φ
  funext w
  unfold total
  apply Finset.sum_congr rfl
  intro i _
  by_cases hij : i = j
  · subst i
    simpa only [add_assoc, add_comm, add_left_comm] using
      T.component_period j (z + u + w)
  · have hleft := T.mem_footprint_left W j u hu w
    have hright := T.mem_footprint_right W j u hu w
    have hright' : (u + w) + T.period j ∈ T.footprint W := by
      simpa only [add_assoc, add_comm, add_left_comm] using hright
    simpa only [add_assoc, add_comm, add_left_comm] using
      T.inactive_component_period W i j z (u + w) (hinactive i hij) hleft hright'

def badSet (W : Finset G) : Set G :=
  {z | ∃ i j : ι, i ≠ j ∧ T.active W i z ∧ T.active W j z}

theorem finite_badSet (W : Finset G) : (T.badSet W).Finite := by
  have hpair (i j : ι) : {z : G | i ≠ j ∧ T.active W i z ∧ T.active W j z}.Finite := by
    by_cases hij : i = j
    · simp [hij]
    · apply (finite_strip_intersection (T.direction i) (T.direction j)
        (T.independent i j hij) (T.lower i - T.radius W i)
        (T.upper i + T.radius W i) (T.lower j - T.radius W j)
        (T.upper j + T.radius W j)).subset
      intro z hz
      exact ⟨hz.2.1, hz.2.2⟩
  have hunion := Set.finite_iUnion (fun i => Set.finite_iUnion (hpair i))
  apply hunion.subset
  rintro z ⟨i, j, hij, hi, hj⟩
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hij, hi, hj⟩⟩

theorem exists_only_active [Nonempty ι] (W : Finset G) (z : G)
    (h : z ∉ T.badSet W) : ∃ j : ι, ∀ i, i ≠ j → ¬T.active W i z := by
  classical
  by_cases hex : ∃ j, T.active W j z
  · obtain ⟨j, hj⟩ := hex
    refine ⟨j, ?_⟩
    intro i hij hi
    exact h ⟨i, j, hij, hi, hj⟩
  · exact ⟨Classical.arbitrary ι, fun i _ hi => hex ⟨i, hi⟩⟩

theorem difference_zero_outside_badSet [Nonempty ι]
    (W : Finset G) (φ : (W → A) → ℂ) (z : G) (hz : z ∉ T.badSet W) :
    act T.operator (T.localObservation W φ) z = 0 := by
  obtain ⟨j, hj⟩ := T.exists_only_active W z hz
  rw [T.operator_factor j]
  apply act_mul_difference_eq_zero_at
  exact fun u hu => T.localObservation_period_on_cofactor W φ z j hj u hu

/-- Lemma 1.1: every finite-window observation has a finitely supported difference. -/
theorem finite_support_local_difference [Nonempty ι]
    (W : Finset G) (φ : (W → A) → ℂ) :
    (Function.support (act T.operator (T.localObservation W φ))).Finite := by
  apply (T.finite_badSet W).subset
  intro z hz
  by_contra hbad
  exact hz (T.difference_zero_outside_badSet W φ z hbad)

theorem finite_support_single_site_difference [Nonempty ι] (w : A → ℂ) :
    (Function.support (act T.operator (fun z => w (T.total z)))).Finite := by
  let W : Finset G := {0}
  let φ : (W → A) → ℂ := fun p => w (p ⟨0, by simp [W]⟩)
  have h := T.finite_support_local_difference W φ
  have heq : T.localObservation W φ = fun z => w (T.total z) := by
    funext z
    simp [localObservation, φ]
  rw [heq] at h
  exact h

/-- Proposition 1.3 for the periodic-tail hypotheses actually used in its proof. -/
theorem first_case_complexity [Nonempty ι] [Fintype A] (w : A → ℂ)
    (hnonzero : act T.operator (fun z => w (T.total z)) ≠ 0) (S : Finset G) :
    S.card + 1 ≤ patternComplexity T.total S := by
  exact complexity_lower_bound_of_finite_difference T.total w T.operator
    T.operator_const (T.finite_support_single_site_difference w) hnonzero S

end StripSystem

end

end NivatTrial.Strips
