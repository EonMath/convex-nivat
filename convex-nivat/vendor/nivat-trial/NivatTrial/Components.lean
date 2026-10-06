import NivatTrial.HalfPlane
import NivatTrial.Witness

/-! The strip-supported, nonzero cofactor fields of Lemma 4.1. -/

namespace NivatTrial.Components

open NivatTrial.Algebra NivatTrial.Geometry NivatTrial.Differences
open NivatTrial.Periodicity NivatTrial.Isolation NivatTrial.HalfPlane
open Filter
open scoped Classical

noncomputable section

/-- A finite polynomial observation that is periodic along an escaping sequence
equals the same observation of its local limit. -/
theorem act_eq_of_period_and_eventual (Q : Laurent) (η ξ : G → ℂ) (h : G)
    (hp : IsPeriod (act Q η) h)
    (hevent : ∀ z, ∀ᶠ n : ℕ in atTop, η (z + n • h) = ξ z) :
    act Q η = act Q ξ := by
  funext z
  have hall : ∀ᶠ n : ℕ in atTop, ∀ u : Q.coeff.support,
      η (z + u + n • h) = ξ (z + u) :=
    Filter.eventually_all.mpr (fun u => hevent (z + u))
  obtain ⟨n, hn⟩ := hall.exists
  rw [← hp.nsmul n z]
  change ∑ u ∈ Q.coeff.support, Q.coeff u * η (z + n • h + u) =
    ∑ u ∈ Q.coeff.support, Q.coeff u * ξ (z + u)
  apply Finset.sum_congr rfl
  intro u hu
  have hη := hn ⟨u, hu⟩
  have hz : z + n • h + u = z + u + n • h := by abel
  rw [hz, hη]

variable {ι A : Type*} [Fintype ι] [AddCommGroup A]

def pureLeft (T : Strips.StripSystem ι A) (i : ι) (h : G) : G → A :=
  fun z => T.leftTail i z + background T i h z

def pureRight (T : Strips.StripSystem ι A) (i : ι) (h : G) : G → A :=
  fun z => T.rightTail i z + background T i h z

theorem tailFor_common_period (T : Strips.StripSystem ι A) (h : G) (j k : ι) :
    IsPeriod (tailFor T h j) (T.period k) := by
  unfold tailFor
  split_ifs
  · exact T.right_period j k
  · exact T.left_period j k

theorem background_common_period (T : Strips.StripSystem ι A) (i k : ι) (h : G) :
    IsPeriod (background T i h) (T.period k) := by
  intro z
  apply Finset.sum_congr rfl
  intro j _
  exact tailFor_common_period T h j k z

theorem pureLeft_common_period (T : Strips.StripSystem ι A) (i k : ι) (h : G) :
    IsPeriod (pureLeft T i h) (T.period k) := by
  intro z
  simp only [pureLeft, T.left_period i k z, background_common_period T i k h z]

theorem pureRight_common_period (T : Strips.StripSystem ι A) (i k : ι) (h : G) :
    IsPeriod (pureRight T i h) (T.period k) := by
  intro z
  simp only [pureRight, T.right_period i k z, background_common_period T i k h z]

theorem cofactor_period (T : Strips.StripSystem ι A) (i : ι) (η : G → ℂ)
    (hD : act T.operator η = 0) : IsPeriod (act (T.cofactor i) η) (T.period i) := by
  apply period_of_difference_eq_zero
  rw [← act_mul, mul_comm, ← T.operator_factor]
  exact hD

theorem cofactor_eq_isolated (T : Strips.StripSystem ι A) (i : ι) (w : A → ℂ)
    (hD : act T.operator (fun z => w (T.total z)) = 0)
    (htransverse : ∀ j, j ≠ i → det (T.direction j) (T.period i) ≠ 0) :
    act (T.cofactor i) (fun z => w (T.total z)) =
      act (T.cofactor i) (fun z => w (isolated T i (T.period i) z)) := by
  apply act_eq_of_period_and_eventual _ _ _ (T.period i)
    (cofactor_period T i _ hD)
  intro z
  filter_upwards [total_eventually_isolated T i (T.period i) z
    (T.component_period i) (fun j => T.left_period j i)
    (fun j => T.right_period j i) htransverse] with n hn
  rw [hn]

theorem cofactor_pureLeft_zero [Nontrivial ι] (T : Strips.StripSystem ι A)
    (i : ι) (h : G) (w : A → ℂ) :
    act (T.cofactor i) (fun z => w (pureLeft T i h z)) = 0 := by
  obtain ⟨j, hji⟩ := exists_ne i
  apply differenceProduct_eq_zero_of_period (Finset.univ.erase i) T.period
    (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
  exact (pureLeft_common_period T i j h).encode w

theorem cofactor_pureRight_zero [Nontrivial ι] (T : Strips.StripSystem ι A)
    (i : ι) (h : G) (w : A → ℂ) :
    act (T.cofactor i) (fun z => w (pureRight T i h z)) = 0 := by
  obtain ⟨j, hji⟩ := exists_ne i
  apply differenceProduct_eq_zero_of_period (Finset.univ.erase i) T.period
    (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
  exact (pureRight_common_period T i j h).encode w

def rightDefect (T : Strips.StripSystem ι A) (i : ι) (h : G) (w : A → ℂ) : G → ℂ :=
  fun z => w (isolated T i h z) - w (pureRight T i h z)

def leftDefect (T : Strips.StripSystem ι A) (i : ι) (h : G) (w : A → ℂ) : G → ℂ :=
  fun z => w (isolated T i h z) - w (pureLeft T i h z)

theorem rightDefect_upperSupport (T : Strips.StripSystem ι A) (i : ι) (h : G) (w : A → ℂ) :
    UpperSupport (T.direction i) (rightDefect T i h w) := by
  refine ⟨T.upper i, ?_⟩
  intro z hz
  unfold rightDefect pureRight
  rw [isolated_right_agreement T i h z hz, sub_self]

theorem leftDefect_lowerSupport (T : Strips.StripSystem ι A) (i : ι) (h : G) (w : A → ℂ) :
    LowerSupport (T.direction i) (leftDefect T i h w) := by
  refine ⟨T.lower i, ?_⟩
  intro z hz
  unfold leftDefect pureLeft
  rw [isolated_left_agreement T i h z hz, sub_self]

theorem rightDefect_ne_zero (T : Strips.StripSystem ι A) (i : ι) (h : G) (w : A → ℂ)
    (hw : Function.Injective w) (hneq : T.component i ≠ T.rightTail i) :
    rightDefect T i h w ≠ 0 := by
  intro heq
  apply hneq
  funext z
  have hz := congrFun heq z
  have hobs : w (isolated T i h z) = w (pureRight T i h z) := sub_eq_zero.mp hz
  have heq' := hw hobs
  exact add_right_cancel heq'

theorem cofactor_eq_rightDefect [Nontrivial ι] (T : Strips.StripSystem ι A)
    (i : ι) (w : A → ℂ) (hD : act T.operator (fun z => w (T.total z)) = 0)
    (htransverse : ∀ j, j ≠ i → det (T.direction j) (T.period i) ≠ 0) :
    act (T.cofactor i) (fun z => w (T.total z)) =
      act (T.cofactor i) (rightDefect T i (T.period i) w) := by
  have heq : rightDefect T i (T.period i) w =
      (fun z => w (isolated T i (T.period i) z)) -
      (fun z => w (pureRight T i (T.period i) z)) := rfl
  rw [heq, act_sub_config, cofactor_pureRight_zero, sub_zero]
  exact cofactor_eq_isolated T i w hD htransverse

theorem cofactor_eq_leftDefect [Nontrivial ι] (T : Strips.StripSystem ι A)
    (i : ι) (w : A → ℂ) (hD : act T.operator (fun z => w (T.total z)) = 0)
    (htransverse : ∀ j, j ≠ i → det (T.direction j) (T.period i) ≠ 0) :
    act (T.cofactor i) (fun z => w (T.total z)) =
      act (T.cofactor i) (leftDefect T i (T.period i) w) := by
  have heq : leftDefect T i (T.period i) w =
      (fun z => w (isolated T i (T.period i) z)) -
      (fun z => w (pureLeft T i (T.period i) z)) := rfl
  rw [heq, act_sub_config, cofactor_pureLeft_zero, sub_zero]
  exact cofactor_eq_isolated T i w hD htransverse

/-- The cofactor field is confined to a bounded-width strip, with both bounds
obtained from actual pure-tail identities. -/
theorem cofactor_supportedInStrip [Nontrivial ι] (T : Strips.StripSystem ι A)
    (i : ι) (w : A → ℂ) (hD : act T.operator (fun z => w (T.total z)) = 0)
    (htransverse : ∀ j, j ≠ i → det (T.direction j) (T.period i) ≠ 0) :
    ∃ a b : ℤ, Witness.SupportedInStrip
      (act (T.cofactor i) (fun z => w (T.total z))) (T.direction i) a b := by
  have hup : UpperSupport (T.direction i) (act (T.cofactor i) (fun z => w (T.total z))) := by
    rw [cofactor_eq_rightDefect T i w hD htransverse]
    exact upperSupport_product _ _ _ (rightDefect_upperSupport T i (T.period i) w)
  have hlo : LowerSupport (T.direction i) (act (T.cofactor i) (fun z => w (T.total z))) := by
    rw [cofactor_eq_leftDefect T i w hD htransverse]
    exact lowerSupport_product _ _ _ (leftDefect_lowerSupport T i (T.period i) w)
  obtain ⟨a, ha⟩ := hlo
  obtain ⟨b, hb⟩ := hup
  refine ⟨a, b, ?_⟩
  intro z hz
  constructor
  · by_contra h
    exact hz (ha z (lt_of_not_ge h))
  · by_contra h
    exact hz (hb z (lt_of_not_ge h))

/-- The nonzero part of Lemma 4.1, proved by one-sided injectivity of transverse
differences. The hypothesis `component ≠ rightTail` follows from (S2). -/
theorem cofactor_ne_zero [Nontrivial ι] (T : Strips.StripSystem ι A)
    (i : ι) (w : A → ℂ) (hw : Function.Injective w)
    (hneq : T.component i ≠ T.rightTail i)
    (hD : act T.operator (fun z => w (T.total z)) = 0)
    (htransverse₁ : ∀ j, j ≠ i → det (T.direction j) (T.period i) ≠ 0)
    (htransverse₂ : ∀ j, j ≠ i → det (T.direction i) (T.period j) ≠ 0) :
    act (T.cofactor i) (fun z => w (T.total z)) ≠ 0 := by
  rw [cofactor_eq_rightDefect T i w hD htransverse₁]
  apply product_ne_zero_of_upperSupport (Finset.univ.erase i) T.period (T.direction i)
    (rightDefect_upperSupport T i (T.period i) w)
    (rightDefect_ne_zero T i (T.period i) w hw hneq)
  intro j hj
  exact htransverse₂ j (Finset.ne_of_mem_erase hj)

end

end NivatTrial.Components
