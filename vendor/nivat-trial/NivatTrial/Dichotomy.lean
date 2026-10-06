import NivatTrial.Components
import NivatTrial.BiRecursion

/-! A closed first-case/second-case witness theorem for the paper's periodic-tail
data. This stops before the exceptional zonotope and does not assert Theorem A.
-/

namespace NivatTrial.Dichotomy

open NivatTrial.Algebra NivatTrial.Geometry NivatTrial.Quadratic
open NivatTrial.Components NivatTrial.Witness
open scoped Classical

noncomputable section

def indicator {A : Type*} (θ : G → A) (a : A) : G → ℂ :=
  fun z => if θ z = a then 1 else 0

theorem observation_eq_sum_indicators {A : Type*} [Fintype A]
    (θ : G → A) (w : A → ℂ) :
    (fun z => w (θ z)) = ∑ a : A, w a • indicator θ a := by
  funext z
  simp [indicator, smul_eq_mul]

/-- The second case annihilates every scalar encoding, not only the indicators. -/
theorem annihilate_all_observations {A : Type*} [Fintype A]
    (θ : G → A) (D : Laurent) (h : ∀ a : A, act D (indicator θ a) = 0) :
    ∀ w : A → ℂ, act D (fun z => w (θ z)) = 0 := by
  intro w
  change actLinear D (fun z => w (θ z)) = 0
  rw [observation_eq_sum_indicators]
  simp only [map_sum, map_smul, actLinear_apply, h, smul_zero, Finset.sum_const_zero]

variable {ι A : Type*} [Fintype ι] [Nontrivial ι] [AddCommGroup A] [Fintype A]

theorem periods_ne_zero_of_transverse (T : Strips.StripSystem ι A)
    (htransverse : ∀ i j, i ≠ j → det (T.direction i) (T.period j) ≠ 0) :
    ∀ i, T.period i ≠ 0 := by
  intro i hi
  obtain ⟨j, hji⟩ := exists_ne i
  have h := htransverse j i hji
  rw [hi, det_zero_right] at h
  exact h rfl

/-- Lemmas 4.1 and 4.2 combined: the second case has a nonzero, finite-support
two-point difference at a nonzero displacement. -/
theorem second_case_witness (T : Strips.StripSystem ι A) (w : A → ℂ)
    (hw : Function.Injective w)
    (hneq : ∀ i, T.component i ≠ T.rightTail i)
    (htransverse : ∀ i j, i ≠ j → det (T.direction i) (T.period j) ≠ 0)
    (hcase : ∀ a : A, act T.operator (indicator T.total a) = 0) :
    ∃ d : G, d ≠ 0 ∧
      (Function.support (act T.operator (twoPoint (fun z => w (T.total z)) 0 d))).Finite ∧
      act T.operator (twoPoint (fun z => w (T.total z)) 0 d) ≠ 0 := by
  have hall := annihilate_all_observations T.total T.operator hcase
  have hD := hall w
  obtain ⟨i, j, hij⟩ : ∃ i j : ι, i ≠ j := exists_pair_ne ι
  have hnonzero (k : ι) : act (T.cofactor k) (fun z => w (T.total z)) ≠ 0 :=
    cofactor_ne_zero T k w hw (hneq k) hD
      (fun l hl => htransverse l k hl) (fun l hl => htransverse k l hl.symm)
  have hbounded (k : ι) := cofactor_supportedInStrip T k w hD
    (fun l hl => htransverse l k hl)
  obtain ⟨a, b, hi⟩ := hbounded i
  obtain ⟨c, e, hj⟩ := hbounded j
  obtain ⟨d, hd⟩ := exists_twoPoint_witness T.operator (T.cofactor i) (T.cofactor j)
    (fun z => w (T.total z)) (T.operator_ne_zero (periods_ne_zero_of_transverse T htransverse))
    (T.direction i) (T.direction j) a b c e (T.independent i j hij)
    (hnonzero i) (hnonzero j) hi hj
  exact ⟨d, witness_ne_zero_of_all_single_site_annihilated T.total w T.operator hall hd,
    finite_support_twoPoint_difference T w 0 d, hd⟩

/-- The first case gives the desired complexity bound. Otherwise the second
case supplies the quadratic witness required by the subsequent zonotope argument. -/
theorem first_case_or_quadratic_witness (T : Strips.StripSystem ι A) (w : A → ℂ)
    (hw : Function.Injective w)
    (hneq : ∀ i, T.component i ≠ T.rightTail i)
    (htransverse : ∀ i j, i ≠ j → det (T.direction i) (T.period j) ≠ 0) :
    (∀ S : Finset G, S.card + 1 ≤ patternComplexity T.total S) ∨
    (∃ d : G, d ≠ 0 ∧
      (Function.support (act T.operator (twoPoint (fun z => w (T.total z)) 0 d))).Finite ∧
      act T.operator (twoPoint (fun z => w (T.total z)) 0 d) ≠ 0) := by
  by_cases hfirst : ∃ a : A, act T.operator (indicator T.total a) ≠ 0
  · obtain ⟨a, ha⟩ := hfirst
    left
    intro S
    exact T.first_case_complexity (fun x => if x = a then 1 else 0) ha S
  · right
    apply second_case_witness T w hw hneq htransverse
    simpa only [not_exists, not_not] using hfirst

end

end NivatTrial.Dichotomy
