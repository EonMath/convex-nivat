import NivatTrial.Star
import NivatTrial.Background

/-! The periodic background of §3 without ordering the realized sectors.
On a widened strip, the longitudinal coordinate is bounded at every exceptional
site where neither isolating configuration gives the local pattern. The
remaining sites have a genuine common period, up to a finite defect.
-/

namespace NivatTrial.SectorBackground

open NivatTrial.Algebra NivatTrial.Geometry NivatTrial.Periodicity
open NivatTrial.Isolation NivatTrial.Components
open scoped Classical

noncomputable section

variable {ι A : Type*} [Fintype ι] [AddCommGroup A]

variable (T : Star.Data ι A)

def complement (j : ι) : G :=
  Classical.choose (exists_unimodular_complement (T.direction j) (T.primitive j))

theorem complement_spec (j : ι) : det (T.direction j) (complement T j) = 1 :=
  Classical.choose_spec (exists_unimodular_complement (T.direction j) (T.primitive j))

def longitudinal (j : ι) (z : G) : ℤ := det z (complement T j)

def offsetRadius (W : Finset G) (j : ι) : ℤ :=
  ∑ u ∈ W, |det (T.direction j) u|

theorem offsetRadius_nonneg (W : Finset G) (j : ι) : 0 ≤ offsetRadius T W j :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem offset_det_bound (W : Finset G) (j : ι) (u : G) (hu : u ∈ W) :
    |det (T.direction j) u| ≤ offsetRadius T W j :=
  Finset.single_le_sum (f := fun x => |det (T.direction j) x|)
    (fun _ _ => abs_nonneg _) hu

def active (W : Finset G) (j : ι) (z : G) : Prop :=
  T.lower j - offsetRadius T W j ≤ det (T.direction j) z ∧
    det (T.direction j) z ≤ T.upper j + offsetRadius T W j

def stripWidth (W : Finset G) (j : ι) : ℤ :=
  |T.lower j| + |T.upper j| + offsetRadius T W j

theorem stripWidth_nonneg (W : Finset G) (j : ι) : 0 ≤ stripWidth T W j := by
  dsimp [stripWidth]
  exact add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (offsetRadius_nonneg T W j)

theorem active_det_bound (W : Finset G) (j : ι) (z : G) (hz : active T W j z) :
    |det (T.direction j) z| ≤ stripWidth T W j := by
  apply abs_le.mpr
  dsimp [active, stripWidth] at *
  have hR := offsetRadius_nonneg T W j
  have hL := neg_abs_le (T.lower j)
  have hU := le_abs_self (T.upper j)
  have hL0 := abs_nonneg (T.lower j)
  have hU0 := abs_nonneg (T.upper j)
  constructor <;> omega

def errorBound (W : Finset G) (j l : ι) : ℤ :=
  stripWidth T W j * |det (T.direction l) (complement T j)| + offsetRadius T W l

theorem errorBound_nonneg (W : Finset G) (j l : ι) : 0 ≤ errorBound T W j l := by
  dsimp [errorBound]
  exact add_nonneg (mul_nonneg (stripWidth_nonneg T W j) (abs_nonneg _))
    (offsetRadius_nonneg T W l)

def longBound (W : Finset G) (j : ι) : ℤ :=
  ∑ l, (|T.lower l| + |T.upper l| + errorBound T W j l + 1)

theorem longBound_nonneg (W : Finset G) (j : ι) : 0 ≤ longBound T W j := by
  apply Finset.sum_nonneg
  intro l _
  have h := errorBound_nonneg T W j l
  positivity

theorem longBound_term (W : Finset G) (j l : ι) :
    |T.lower l| + |T.upper l| + errorBound T W j l + 1 ≤ longBound T W j := by
  apply Finset.single_le_sum (fun k _ => ?_) (Finset.mem_univ l)
  have h := errorBound_nonneg T W j k
  positivity

theorem det_longitudinal_error (W : Finset G) (j l : ι) (z u : G)
    (hz : active T W j z) (hu : u ∈ W) :
    |det (T.direction l) (z + u) - longitudinal T j z * det (T.direction l) (T.direction j)|
      ≤ errorBound T W j l := by
  have hcoords := unimodular_coordinates (T.direction j) (complement T j) z
    (complement_spec T j)
  have hid := congrArg (det (T.direction l)) hcoords
  simp only [det_add_right, det_zsmul_right] at hid
  have heq : det (T.direction l) (z + u) -
      longitudinal T j z * det (T.direction l) (T.direction j) =
      det (T.direction j) z * det (T.direction l) (complement T j) +
        det (T.direction l) u := by
    rw [det_add_right, ← hid]
    simp only [longitudinal]
    ring
  rw [heq]
  calc
    _ ≤ |det (T.direction j) z * det (T.direction l) (complement T j)| +
        |det (T.direction l) u| := abs_add_le _ _
    _ = |det (T.direction j) z| * |det (T.direction l) (complement T j)| +
        |det (T.direction l) u| := by rw [abs_mul]
    _ ≤ errorBound T W j l :=
      add_le_add (mul_le_mul_of_nonneg_right (active_det_bound T W j z hz)
        (abs_nonneg _)) (offset_det_bound T W l u hu)

theorem positive_period_sign (j l : ι) :
    0 < det (T.direction l) (T.normalized.period j) ↔
      0 < det (T.direction l) (T.direction j) := by
  change 0 < det (T.direction l) (T.commonMultiplier j • T.direction j) ↔ _
  rw [det_nsmul_right]
  have hk : (0 : ℤ) < T.commonMultiplier j := by
    exact_mod_cast (T.commonMultiplier_spec j).1
  exact mul_pos_iff_of_pos_left hk

theorem positive_tail_on_long_strip (W : Finset G) (j l : ι) (hjl : l ≠ j)
    (z u : G) (hz : active T W j z) (hu : u ∈ W)
    (ha : longBound T W j < longitudinal T j z) :
    T.component l (z + u) = tailFor T.normalized (T.normalized.period j) l (z + u) := by
  have herr := abs_le.mp (det_longitudinal_error T W j l z u hz hu)
  have hb := longBound_term T W j l
  have ha0 : 0 ≤ longitudinal T j z := by
    have h := longBound_nonneg T W j
    omega
  have hc := T.independent l j hjl
  unfold tailFor
  change T.component l (z + u) =
    (if 0 < det (T.direction l) (T.normalized.period j) then T.rightTail l else T.leftTail l) (z + u)
  by_cases hp : 0 < det (T.direction l) (T.direction j)
  · rw [if_pos ((positive_period_sign T j l).mpr hp)]
    apply T.right_agreement
    have hc1 : 1 ≤ det (T.direction l) (T.direction j) := by omega
    have hlead := mul_le_mul_of_nonneg_left hc1 ha0
    have hupp := le_abs_self (T.upper l)
    have hlow := abs_nonneg (T.lower l)
    nlinarith
  · rw [if_neg (fun h => hp ((positive_period_sign T j l).mp h))]
    apply T.left_agreement
    have hc1 : det (T.direction l) (T.direction j) ≤ -1 := by omega
    have hlead := mul_le_mul_of_nonneg_left hc1 ha0
    have hlow := neg_abs_le (T.lower l)
    have hupp := abs_nonneg (T.upper l)
    nlinarith

theorem negative_tail_on_long_strip (W : Finset G) (j l : ι) (hjl : l ≠ j)
    (z u : G) (hz : active T W j z) (hu : u ∈ W)
    (ha : longitudinal T j z < -longBound T W j) :
    T.component l (z + u) = tailFor T.normalized (-T.normalized.period j) l (z + u) := by
  have herr := abs_le.mp (det_longitudinal_error T W j l z u hz hu)
  have hb := longBound_term T W j l
  have ha0 : longitudinal T j z ≤ 0 := by
    have h := longBound_nonneg T W j
    omega
  have hc := T.independent l j hjl
  have hsign : 0 < det (T.direction l) (-T.normalized.period j) ↔
      det (T.direction l) (T.direction j) < 0 := by
    rw [det_neg_right]
    change 0 < -(det (T.direction l) (T.commonMultiplier j • T.direction j)) ↔ _
    rw [det_nsmul_right]
    have hk : (0 : ℤ) < T.commonMultiplier j := by
      exact_mod_cast (T.commonMultiplier_spec j).1
    constructor <;> intro h <;> nlinarith
  unfold tailFor
  change T.component l (z + u) =
    (if 0 < det (T.direction l) (-T.normalized.period j) then T.rightTail l else T.leftTail l) (z + u)
  by_cases hp : det (T.direction l) (T.direction j) < 0
  · rw [if_pos (hsign.mpr hp)]
    apply T.right_agreement
    have hc1 : 1 ≤ -det (T.direction l) (T.direction j) := by omega
    have hlead := mul_le_mul_of_nonneg_left hc1 (neg_nonneg.mpr ha0)
    have hupp := le_abs_self (T.upper l)
    have hlow := abs_nonneg (T.lower l)
    nlinarith
  · rw [if_neg (fun h => hp (hsign.mp h))]
    apply T.left_agreement
    have hc1 : 1 ≤ det (T.direction l) (T.direction j) := by omega
    have hlead := mul_le_mul_of_nonneg_left hc1 (neg_nonneg.mpr ha0)
    have hlow := neg_abs_le (T.lower l)
    have hupp := abs_nonneg (T.upper l)
    nlinarith

theorem total_eq_isolated_of_tails (j : ι) (h z : G)
    (htails : ∀ l, l ≠ j → T.component l z = tailFor T.normalized h l z) :
    T.total z = isolated T.normalized j h z := by
  unfold Star.Data.total isolated background
  rw [← Finset.sum_erase_add Finset.univ (fun l => T.component l z) (Finset.mem_univ j)]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  exact htails l (Finset.ne_of_mem_erase hl)

theorem positive_isolated_on_long_strip (W : Finset G) (j : ι) (z : G)
    (hz : active T W j z) (ha : longBound T W j < longitudinal T j z) :
    ∀ u ∈ W, T.total (z + u) = isolated T.normalized j (T.normalized.period j) (z + u) := by
  intro u hu
  apply total_eq_isolated_of_tails
  intro l hlj
  exact positive_tail_on_long_strip T W j l hlj z u hz hu ha

theorem negative_isolated_on_long_strip (W : Finset G) (j : ι) (z : G)
    (hz : active T W j z) (ha : longitudinal T j z < -longBound T W j) :
    ∀ u ∈ W, T.total (z + u) = isolated T.normalized j (-T.normalized.period j) (z + u) := by
  intro u hu
  apply total_eq_isolated_of_tails
  intro l hlj
  exact negative_tail_on_long_strip T W j l hlj z u hz hu ha

def exceptionalBox (W : Finset G) (j : ι) : Set G :=
  {z | active T W j z ∧ |longitudinal T j z| ≤ longBound T W j}

theorem exceptionalBox_finite (W : Finset G) (j : ι) :
    (exceptionalBox T W j).Finite := by
  apply (finite_strip_intersection (T.direction j) (complement T j)
    (by rw [complement_spec]; norm_num)
    (T.lower j - offsetRadius T W j) (T.upper j + offsetRadius T W j)
    (-longBound T W j) (longBound T W j)).subset
  rintro z ⟨hz, hl⟩
  refine ⟨hz, ?_⟩
  have hswap := det_swap z (complement T j)
  have ha := abs_le.mp hl
  dsimp [longitudinal] at ha
  constructor <;> omega

def exceptionalSet (W : Finset G) : Set G := ⋃ j, exceptionalBox T W j

theorem exceptionalSet_finite (W : Finset G) : (exceptionalSet T W).Finite :=
  Set.finite_iUnion (exceptionalBox_finite T W)

theorem inactive_component_period (W : Finset G) (j i : ι) (z u : G)
    (hz : ¬active T W j z) (hu : u ∈ W) (hup : u + T.normalized.period i ∈ W) :
    T.component j (z + u + T.normalized.period i) = T.component j (z + u) := by
  have houtside : det (T.direction j) z < T.lower j - offsetRadius T W j ∨
      T.upper j + offsetRadius T W j < det (T.direction j) z := by
    dsimp [active] at hz
    omega
  have h₁ := abs_le.mp (offset_det_bound T W j u hu)
  have h₂ := abs_le.mp (offset_det_bound T W j (u + T.normalized.period i) hup)
  rcases houtside with hleft | hright
  · have hl₁ : det (T.direction j) (z + u) < T.lower j := by
      rw [det_add_right]
      omega
    have hl₂ : det (T.direction j) (z + u + T.normalized.period i) < T.lower j := by
      rw [add_assoc, det_add_right]
      omega
    rw [T.left_agreement j _ hl₂, T.left_agreement j _ hl₁]
    exact T.normalized.left_period j i (z + u)
  · have hr₁ : T.upper j < det (T.direction j) (z + u) := by
      rw [det_add_right]
      omega
    have hr₂ : T.upper j < det (T.direction j) (z + u + T.normalized.period i) := by
      rw [add_assoc, det_add_right]
      omega
    rw [T.right_agreement j _ hr₂, T.right_agreement j _ hr₁]
    exact T.normalized.right_period j i (z + u)

theorem inactive_total_period (W : Finset G) (i : ι) (z u : G)
    (hz : ∀ j, ¬active T W j z) (hu : u ∈ W) (hup : u + T.normalized.period i ∈ W) :
    T.total (z + u + T.normalized.period i) = T.total (z + u) := by
  unfold Star.Data.total
  apply Finset.sum_congr rfl
  intro j _
  exact inactive_component_period T W j i z u (hz j) hu hup

theorem act_eq_on_support (P : Laurent) (η ξ : G → ℂ) (z : G)
    (h : ∀ u ∈ P.coeff.support, η (z + u) = ξ (z + u)) : act P η z = act P ξ z := by
  change ∑ u ∈ P.coeff.support, P.coeff u * η (z + u) =
    ∑ u ∈ P.coeff.support, P.coeff u * ξ (z + u)
  apply Finset.sum_congr rfl
  intro u hu
  rw [h u hu]

theorem act_preserves_period (P : Laurent) (η : G → ℂ) (h : G)
    (hp : IsPeriod η h) : IsPeriod (act P η) h := by
  intro z
  change ∑ u ∈ P.coeff.support, P.coeff u * η (z + h + u) =
    ∑ u ∈ P.coeff.support, P.coeff u * η (z + u)
  apply Finset.sum_congr rfl
  intro u _
  rw [show z + h + u = z + u + h by abel, hp (z + u)]

theorem act_isolated_eq_pureRight (P : Laurent) (w : A → ℂ) (j : ι) (h : G)
    (hkill : act P (rightDefect T.normalized j h w) = 0) :
    act P (fun z => w (isolated T.normalized j h z)) =
      act P (fun z => w (pureRight T.normalized j h z)) := by
  have heq : rightDefect T.normalized j h w =
      (fun z => w (isolated T.normalized j h z)) -
      (fun z => w (pureRight T.normalized j h z)) := rfl
  rw [heq, act_sub_config] at hkill
  exact sub_eq_zero.mp hkill

def observationFootprint (P : Laurent) (h : G) : Finset G :=
  P.coeff.support ∪ P.coeff.support.image (fun u => u + h)

theorem mem_observationFootprint (P : Laurent) (h u : G) (hu : u ∈ P.coeff.support) :
    u ∈ observationFootprint P h := Finset.mem_union_left _ hu

theorem add_mem_observationFootprint (P : Laurent) (h u : G) (hu : u ∈ P.coeff.support) :
    u + h ∈ observationFootprint P h :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)

theorem period_at_of_isolated_match (P : Laurent) (w : A → ℂ) (i j : ι) (h z : G)
    (hkill : act P (rightDefect T.normalized j h w) = 0)
    (hmatch : ∀ u ∈ observationFootprint P (T.normalized.period i),
      T.total (z + u) = isolated T.normalized j h (z + u)) :
    act P (fun x => w (T.total x)) (z + T.normalized.period i) =
      act P (fun x => w (T.total x)) z := by
  have h₀ := act_eq_on_support P (fun x => w (T.total x))
    (fun x => w (isolated T.normalized j h x)) z
    (fun u hu => congrArg w (hmatch u (mem_observationFootprint P _ u hu)))
  have h₁ := act_eq_on_support P (fun x => w (T.total x))
    (fun x => w (isolated T.normalized j h x)) (z + T.normalized.period i) (by
      intro u hu
      have hlocal := hmatch (u + T.normalized.period i) (add_mem_observationFootprint P _ u hu)
      exact congrArg w (by simpa only [add_assoc, add_comm, add_left_comm] using hlocal))
  have hiso := act_isolated_eq_pureRight T P w j h hkill
  have hpure := act_preserves_period P (fun x => w (pureRight T.normalized j h x))
    (T.normalized.period i) ((pureRight_common_period T.normalized j i h).encode w)
  rw [h₁, h₀, hiso]
  exact hpure z

/-- The two signs are the actual isolating configurations; the spectrum module
will supply these annihilation equations from its construction of `P`. -/
def KillsIsolatedDefects (P : Laurent) (w : A → ℂ) : Prop :=
  ∀ j, act P (rightDefect T.normalized j (T.normalized.period j) w) = 0 ∧
    act P (rightDefect T.normalized j (-T.normalized.period j) w) = 0

theorem period_outside_exceptionalSet (P : Laurent) (w : A → ℂ)
    (hkill : KillsIsolatedDefects T P w) (i : ι) (z : G)
    (hz : z ∉ exceptionalSet T (observationFootprint P (T.normalized.period i))) :
    act P (fun x => w (T.total x)) (z + T.normalized.period i) =
      act P (fun x => w (T.total x)) z := by
  let W := observationFootprint P (T.normalized.period i)
  by_cases hex : ∃ j, active T W j z
  · obtain ⟨j, hj⟩ := hex
    have hnot : ¬ |longitudinal T j z| ≤ longBound T W j := by
      intro h
      exact hz (Set.mem_iUnion.mpr ⟨j, hj, h⟩)
    have hlong : longBound T W j < longitudinal T j z ∨
        longitudinal T j z < -longBound T W j := by
      have habs : |longitudinal T j z| ≤ longBound T W j ↔
        -longBound T W j ≤ longitudinal T j z ∧ longitudinal T j z ≤ longBound T W j := abs_le
      omega
    rcases hlong with hpos | hneg
    · exact period_at_of_isolated_match T P w i j (T.normalized.period j) z (hkill j).1
        (positive_isolated_on_long_strip T W j z hj hpos)
    · exact period_at_of_isolated_match T P w i j (-T.normalized.period j) z (hkill j).2
        (negative_isolated_on_long_strip T W j z hj hneg)
  · have hnone : ∀ j, ¬active T W j z := by
      intro j hj
      exact hex ⟨j, hj⟩
    change ∑ u ∈ P.coeff.support, P.coeff u * w (T.total (z + T.normalized.period i + u)) =
      ∑ u ∈ P.coeff.support, P.coeff u * w (T.total (z + u))
    apply Finset.sum_congr rfl
    intro u hu
    have hlocal := inactive_total_period T W i z u hnone
      (mem_observationFootprint P _ u hu) (add_mem_observationFootprint P _ u hu)
    rw [show z + T.normalized.period i + u = z + u + T.normalized.period i by abel, hlocal]

/-- Proposition 3.3's required common-period conclusion. There is no finite
exceptional-set or realized-sector hypothesis in this statement. -/
theorem polynomial_background_periods (P : Laurent) (w : A → ℂ)
    (hD : act T.normalized.operator (fun z => w (T.total z)) = 0)
    (hkill : KillsIsolatedDefects T P w) :
    ∀ i, IsPeriod (act P (fun z => w (T.total z))) (T.normalized.period i) := by
  intro i
  apply Background.period_of_period_outside_finite T.normalized.operator
    (T.normalized.operator_ne_zero T.normalized_period_nonzero)
    (act P (fun z => w (T.total z))) (Background.act_annihilated _ _ _ hD)
    (T.normalized.period i)
    (exceptionalSet T (observationFootprint P (T.normalized.period i)))
    (exceptionalSet_finite T _)
  exact period_outside_exceptionalSet T P w hkill i

theorem normalized_period_independent (i j : ι) (hij : i ≠ j) :
    det (T.normalized.period i) (T.normalized.period j) ≠ 0 := by
  have heq : det (T.normalized.period i) (T.normalized.period j) =
      (T.commonMultiplier i : ℤ) * (T.commonMultiplier j : ℤ) *
        det (T.direction i) (T.direction j) := by
    change det (T.commonMultiplier i • T.direction i) (T.commonMultiplier j • T.direction j) = _
    simp [det]
    ring
  rw [heq]
  exact mul_ne_zero (mul_ne_zero
    (by exact_mod_cast Nat.ne_of_gt (T.commonMultiplier_spec i).1)
    (by exact_mod_cast Nat.ne_of_gt (T.commonMultiplier_spec j).1)) (T.independent i j hij)

theorem polynomial_background_doublyPeriodic [Nontrivial ι] (P : Laurent) (w : A → ℂ)
    (hD : act T.normalized.operator (fun z => w (T.total z)) = 0)
    (hkill : KillsIsolatedDefects T P w) :
    IsDoublyPeriodic (act P (fun z => w (T.total z))) := by
  let i : ι := Classical.arbitrary ι
  obtain ⟨j, hji⟩ := exists_ne i
  exact ⟨T.normalized.period i, T.normalized.period j,
    normalized_period_independent T i j hji.symm,
    polynomial_background_periods T P w hD hkill i,
    polynomial_background_periods T P w hD hkill j⟩

end

end NivatTrial.SectorBackground
