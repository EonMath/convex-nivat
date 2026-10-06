import ConvexNivat.SectorSpectralDefinitions
import ConvexNivat.ExceptionalAnnihilation
import ConvexNivat.OperatorDifferences

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators

namespace ConvexNivat.FullAWitness
noncomputable section

def direction : Fin 3 → Lattice := ![(1, 0), (0, -1), (1, -1)]
def transverse : Fin 3 → Lattice := ![(0, 1), (1, 0), (1, 0)]
def px (z : Lattice) : ZMod 2 := z.1
def py (z : Lattice) : ZMod 2 := z.2
def leftTail (i : Fin 3) (z : Lattice) : ZMod 2 :=
  ![0, (1 - px z) * py z, 1 + px z * (1 - py z)] i
def rightTail (i : Fin 3) (z : Lattice) : ZMod 2 :=
  ![1 - py z, (1 - px z) * (1 - py z), (1 - px z) * py z] i
def field (i : Fin 3) (z : Lattice) : ZMod 2 :=
  if 0 ≤ height (direction i) z then rightTail i z else leftTail i z

lemma phase_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> first | exact Or.inl rfl | exact Or.inr rfl

lemma two_zero : (2 : ZMod 2) = 0 := by decide
lemma three_one : (3 : ZMod 2) = 1 := by decide
lemma minus_one : (-1 : ZMod 2) = 1 := by decide

lemma grid_left (i : Fin 3) (v : Lattice) : HasPeriod (leftTail i) ((2 : ℤ) • v) := by
  intro z
  simp [leftTail, px, py, Prod.fst_add, Prod.snd_add, Int.cast_add,
    Int.cast_mul, smul_eq_mul, two_zero]

lemma grid_right (i : Fin 3) (v : Lattice) : HasPeriod (rightTail i) ((2 : ℤ) • v) := by
  intro z
  simp [rightTail, px, py, Prod.fst_add, Prod.snd_add, Int.cast_add,
    Int.cast_mul, smul_eq_mul, two_zero]

lemma field_period (i : Fin 3) : HasPeriod (field i) ((2 : ℤ) • direction i) := by
  intro z
  simp only [field, height_add, height_zsmul, height_self, mul_zero, add_zero]
  rw [grid_left i (direction i) z, grid_right i (direction i) z]

lemma left_doubly (i : Fin 3) : DoublyPeriodic (leftTail i) := by
  exact (doublyPeriodic_iff_grid _).mpr ⟨2, by norm_num, grid_left i⟩

lemma right_doubly (i : Fin 3) : DoublyPeriodic (rightTail i) := by
  exact (doublyPeriodic_iff_grid _).mpr ⟨2, by norm_num, grid_right i⟩

lemma field_not_doubly (i : Fin 3) : ¬ DoublyPeriodic (field i) := by
  intro h
  obtain ⟨N, hN, hp⟩ := (doublyPeriodic_iff_grid _).mp h
  have hh := hasPeriod_zsmul _ _ (hp (-transverse i)) 2 (0, 0)
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have hheight : height (direction i) ((2 : ℤ) • ((N : ℤ) • (-transverse i))) < 0 := by
    fin_cases i <;> norm_num [height, det, direction, transverse, smul_eq_mul] <;> omega
  have hphase : px ((2 : ℤ) • ((N : ℤ) • (-transverse i))) = 0 ∧
      py ((2 : ℤ) • ((N : ℤ) • (-transverse i))) = 0 := by
    simp [px, py, smul_eq_mul, Int.cast_mul, two_zero]
  have hh' : field i ((2 : ℤ) • ((N : ℤ) • (-transverse i))) = field i (0, 0) := by
    have hz : ((0,0) : Lattice) + (2 : ℤ) • ((N : ℤ) • (-transverse i)) =
        (2 : ℤ) • ((N : ℤ) • (-transverse i)) := zero_add _
    rwa [hz] at hh
  rw [field, if_neg (by omega), field] at hh'
  fin_cases i <;> norm_num [leftTail, rightTail, px, py, height, det,
    direction, hphase.1, hphase.2] at hh'
  all_goals simp [two_zero] at hh'

lemma nonparallel (i j : Fin 3) (hij : i ≠ j) :
    Nonparallel (direction i) (direction j) := by
  fin_cases i <;> fin_cases j <;> norm_num [direction, Nonparallel, det] at *

def component (i : Fin 3) : StarComponent 2 where
  direction := direction i
  primitive := by fin_cases i <;> norm_num [direction, Primitive]
  field := field i
  tangential_period := ⟨2, by norm_num, field_period i⟩
  not_doubly_periodic := field_not_doubly i
  leftTail := leftTail i
  rightTail := rightTail i
  left_doubly_periodic := left_doubly i
  right_doubly_periodic := right_doubly i
  lower := 0
  upper := -1
  bounds := by norm_num
  left_agreement := by intro z hz; exact if_neg (by change height (direction i) z < 0 at hz; omega)
  right_agreement := by intro z hz; exact if_pos (by change (-1 : ℤ) < height (direction i) z at hz; omega)

def star : StarData 2 where
  prime := by norm_num
  m := 3
  two_le := by norm_num
  component := component
  pairwise_nonparallel := nonparallel

def periods : StarCommonPeriods star where
  multiplier := fun _ => 2
  positive := by intro i; norm_num
  component_period := field_period
  left_period := fun i j => grid_left j (direction i)
  right_period := fun i j => grid_right j (direction i)

lemma px_add (z v : Lattice) : px (z + v) = px z + (v.1 : ZMod 2) := by
  simp [px]
lemma py_add (z v : Lattice) : py (z + v) = py z + (v.2 : ZMod 2) := by
  simp [py]

@[simp] lemma star_component (i : Fin 3) : star.component i = component i := rfl
@[simp] lemma component_direction (i : Fin 3) : (component i).direction = direction i := rfl
@[simp] lemma component_field (i : Fin 3) : (component i).field = field i := rfl
@[simp] lemma component_left (i : Fin 3) : (component i).leftTail = leftTail i := rfl
@[simp] lemma component_right (i : Fin 3) : (component i).rightTail = rightTail i := rfl

lemma configuration_formula (z : Lattice) :
    star.configuration z = field 0 z + field 1 z + field 2 z := by
  change (∑ i : Fin 3, field i z) = _
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [add_assoc]

def rayB (i : Fin 3) (σ : RayOrientation) (z : Lattice) : ZMod 2 :=
  match σ with
  | .positive => ![rightTail 1 z + rightTail 2 z,
      leftTail 0 z + leftTail 2 z, leftTail 0 z + rightTail 1 z] i
  | .negative => ![leftTail 1 z + leftTail 2 z,
      rightTail 0 z + rightTail 2 z, rightTail 0 z + leftTail 1 z] i

lemma rayB_formula (i : Fin 3) (σ : RayOrientation) (z : Lattice) :
    rayBackground star i σ z = rayB i σ z := by
  classical
  unfold rayBackground rayTail
  simp only [star_component, component_direction, component_left, component_right]
  change (∑ j ∈ (Finset.univ : Finset (Fin 3)).erase i,
    (if 0 < σ.sign * det (direction j) (direction i) then rightTail j else leftTail j) z) = _
  simp only [ite_apply]
  rw [Finset.sum_erase_eq_sub (s := Finset.univ) (a := i)
    (f := fun j => if 0 < σ.sign * det (direction j) (direction i)
      then rightTail j z else leftTail j z) (Finset.mem_univ i)]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  fin_cases i <;> cases σ <;> norm_num [rayB, direction, det, RayOrientation.sign]
  all_goals abel

lemma exceptional_antiperiod (i : Fin 3) (σ : RayOrientation)
    (side : TailSide) (a : ZMod 2) (z : Lattice) :
    exceptionalDifference star i σ side a (z + direction i) =
      -exceptionalDifference star i σ side a z := by
  classical
  have hh : height (direction i) (z + direction i) = height (direction i) z := by
    simp [height_add, height_self]
  rcases phase_cases (px z) with hx | hx <;>
    rcases phase_cases (py z) with hy | hy <;>
    rcases phase_cases a with rfl | rfl
  all_goals
    fin_cases i <;> cases σ <;> cases side
  all_goals
    simp only [exceptionalDifference, colorIndicator, Pi.sub_apply, isolatingConfiguration,
      pureRayBackground, Pi.add_apply,
      componentTail, star_component, component_direction, component_field,
      component_left, component_right]
  all_goals
    norm_num [rayB_formula, rayB, star_component, component_direction,
      component_left, component_right,
      direction, RayOrientation.sign, field, height_add, height_self, height, det,
      leftTail, rightTail, px_add, py_add, hx, hy, two_zero, three_one, minus_one]
  all_goals split_ifs <;> norm_num [two_zero, three_one, minus_one] at *
  all_goals norm_num [two_zero, three_one, minus_one] at *
  all_goals try omega
  all_goals try decide
  all_goals try exact (show (2 : ZMod 2) ≠ 1 by decide) (by assumption)
  all_goals try exact (show (3 : ZMod 2) = 1 by decide) |> fun h => (by contradiction)
  all_goals try exact (show (2 : ZMod 2) = 0 by decide) |> fun h => (by contradiction)
  all_goals have h30 : (3 : ZMod 2) ≠ 0 := by decide
  all_goals have h21 : (2 : ZMod 2) ≠ 1 := by decide
  all_goals try omega
  all_goals try (apply h30; apply_assumption; omega)
  all_goals have h20 : (2 : ZMod 2) = 0 := by decide
  all_goals simp_all only [not_true_eq_false, and_false, h20]

def b0 (z : Lattice) : ℂ := if px z = py z then 1 else 0
def b1 (z : Lattice) : ℂ :=
  if py z = 0 then (if px z = 0 then -1 else 1) * (if 0 ≤ z.2 then 1 else 0) else 0
def b2 (z : Lattice) : ℂ :=
  if px z = 0 then (if py z = 0 then -1 else 1) * (if 0 ≤ z.1 then 1 else 0) else 0
def b3 (z : Lattice) : ℂ :=
  if px z = py z then (if px z = 0 then 1 else -1) *
    (if 0 ≤ z.1 + z.2 then 1 else 0) else 0

lemma indicator_decomposition : colorIndicator star.configuration 1 = b0 + b1 + b2 + b3 := by
  funext z
  rcases phase_cases (px z) with hx | hx <;> rcases phase_cases (py z) with hy | hy
  all_goals
    simp only [colorIndicator, configuration_formula, Pi.add_apply]
  all_goals
    norm_num [field, direction, height, det, leftTail, rightTail, hx, hy,
      b0, b1, b2, b3, two_zero]
  all_goals split_ifs <;> norm_num [two_zero, three_one, minus_one] at * <;> try omega
  all_goals norm_num [two_zero, three_one, minus_one] at *
  all_goals try decide
  all_goals try exact (show (2 : ZMod 2) ≠ 1 by decide) (by assumption)
  all_goals try exact (show (3 : ZMod 2) = 1 by decide) |> fun h => (by contradiction)
  all_goals try exact (show (2 : ZMod 2) = 0 by decide) |> fun h => (by contradiction)

lemma b0_period : HasPeriod b0 (periods.vector (0 : Fin 3)) := by
  intro z
  simp [b0, periods, StarCommonPeriods.vector, star_component, component_direction,
    direction, px_add, py_add, two_zero]

lemma b1_period : HasPeriod b1 (periods.vector (0 : Fin 3)) := by
  intro z
  simp [b1, periods, StarCommonPeriods.vector, star_component, component_direction,
    direction, px_add, py_add, two_zero]

lemma b2_period : HasPeriod b2 (periods.vector (1 : Fin 3)) := by
  intro z
  simp [b2, periods, StarCommonPeriods.vector, star_component, component_direction,
    direction, px_add, py_add, two_zero]

lemma b3_period : HasPeriod b3 (periods.vector (2 : Fin 3)) := by
  intro z
  have hh : (z + periods.vector (2 : Fin 3)).1 + (z + periods.vector (2 : Fin 3)).2 = z.1 + z.2 := by
    norm_num [periods, StarCommonPeriods.vector, star_component, component_direction, direction]
    ring
  simp only [b3, hh]
  simp [periods, StarCommonPeriods.vector, star_component, component_direction,
    direction, px_add, py_add, two_zero]

lemma caseB : InCaseB star periods := by
  have hk (i : Fin 3) (f : ScalarField) (hf : HasPeriod f (periods.vector i)) :
      applyLaurent (starDifferencePolynomial star periods) f = 0 := by
    exact differenceProduct_kills_period Finset.univ periods.vector i (Finset.mem_univ i) f hf
  have h1 : applyLaurent (starDifferencePolynomial star periods) (colorIndicator star.configuration 1) = 0 := by
    rw [indicator_decomposition]
    simp only [applyLaurent_add_field, hk 0 b0 b0_period, hk 0 b1 b1_period,
      hk 1 b2 b2_period, hk 2 b3 b3_period, add_zero]
  intro a
  rcases phase_cases a with rfl | rfl
  · have hc : colorIndicator star.configuration 0 + colorIndicator star.configuration 1 =
        (fun _ => (1 : ℂ)) := by
      funext z
      rcases phase_cases (star.configuration z) with h | h <;> simp [colorIndicator, h]
    have hz : applyLaurent (starDifferencePolynomial star periods) (fun _ => (1 : ℂ)) = 0 :=
      hk 0 _ (fun _ => rfl)
    rw [← hc, applyLaurent_add_field, h1, add_zero] at hz
    exact hz
  · exact h1

lemma spectra (i : Fin 3) : exceptionalSpectrum star periods i = {-1} := by
  classical
  have hsubset : exceptionalSpectrum star periods i ⊆ {-1} := by
    intro ζ hζ
    obtain ⟨hr, σ, side, a, hocc⟩ := Finset.mem_filter.mp hζ
    have hroot : ζ ^ 2 = 1 :=
      (Polynomial.mem_nthRootsFinset (by norm_num) 1).mp hr
    rcases sq_eq_one_iff.mp hroot with rfl | rfl
    · exfalso
      apply hocc
      funext z
      norm_num [spectralProjection, periods, star_component, component_direction,
        Finset.sum_range_succ, exceptional_antiperiod]
    · simp
  exact Finset.Subset.antisymm hsubset (by
    intro ζ hζ
    have he : ζ = -1 := Finset.mem_singleton.mp hζ
    subst ζ
    obtain ⟨w, hw⟩ := exceptional_spectrum_nonempty star periods i
    have hw' : w = -1 := Finset.mem_singleton.mp (hsubset hw)
    simpa [hw'] using hw)

lemma least_periods (i : Fin 3) (κ : ℕ) (hk : 0 < κ) (_ : 2 ∣ κ)
    (_ : ∀ j, HasPeriod (star.component j).leftTail ((κ : ℤ) • direction i) ∧
      HasPeriod (star.component j).rightTail ((κ : ℤ) • direction i)) :
    periods.multiplier i ≤ κ := by
  simpa [periods] using Nat.le_of_dvd hk ‹2 ∣ κ›

def signs0 : SectorSigns star := ![.left, .left, .right]
def signs1 : SectorSigns star := ![.right, .right, .left]

lemma choice0 : sectorBackground star signs0 = fun _ => (0 : ZMod 2) := by
  funext z
  change (∑ i : Fin 3, componentTail star i (signs0 i) z) = 0
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  rcases phase_cases (px z) with hx | hx <;> rcases phase_cases (py z) with hy | hy
  all_goals norm_num [sectorBackground, signs0, componentTail, star_component,
    component_left, component_right, Fin.sum_univ_succ, leftTail, rightTail, hx, hy,
    two_zero, three_one]
  all_goals try decide

lemma choice1 : sectorBackground star signs1 = fun _ => (1 : ZMod 2) := by
  funext z
  change (∑ i : Fin 3, componentTail star i (signs1 i) z) = 1
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  rcases phase_cases (px z) with hx | hx <;> rcases phase_cases (py z) with hy | hy
  all_goals norm_num [sectorBackground, signs1, componentTail, star_component,
    component_left, component_right, Fin.sum_univ_succ, leftTail, rightTail, hx, hy,
    two_zero, three_one]
  all_goals try decide

lemma signs0_unrealised : ¬ RealisedSector star signs0 := by
  rintro ⟨z, hz⟩
  have h0 := hz (0 : Fin 3)
  have h1 := hz (1 : Fin 3)
  have h2 := hz (2 : Fin 3)
  norm_num [sectorCone, signs0, realHeight, star_component, component_direction,
    direction] at h0 h1 h2
  linarith

lemma fullA_constant (c : ℂ) :
    applyLaurent (exceptionalPolynomial star periods) (fun _ => c) = fun _ => 8 * c := by
  have hs (i : Fin 3) (d : ℂ) :
      applyLaurent (translationMonomial (direction i) - AddMonoidAlgebra.single 0 (-1))
        (fun _ => d) = fun _ => 2 * d := by
    funext z
    rw [applyLaurent_sub]
    change applyLaurent (translationMonomial (direction i)) (fun _ => d) z -
      applyLaurent (AddMonoidAlgebra.single 0 (-1)) (fun _ => d) z = 2 * d
    rw [show translationMonomial (direction i) = AddMonoidAlgebra.single (direction i) 1 from rfl]
    rw [applyLaurent_single, applyLaurent_single]
    ring
  unfold exceptionalPolynomial exceptionalDirectionPolynomial
  simp_rw [spectra, Finset.prod_singleton]
  change applyLaurent (∏ i : Fin 3,
    (translationMonomial (direction i) - AddMonoidAlgebra.single 0 (-1))) (fun _ => c) = _
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.prod_univ_zero, mul_one]
  change applyLaurent ((translationMonomial (direction 0) - AddMonoidAlgebra.single 0 (-1)) *
    ((translationMonomial (direction 1) - AddMonoidAlgebra.single 0 (-1)) *
    (translationMonomial (direction 2) - AddMonoidAlgebra.single 0 (-1)))) (fun _ => c) = _
  rw [applyLaurent_mul, applyLaurent_mul, hs 2 c, hs 1 (2 * c), hs 0 (2 * (2 * c))]
  funext z
  ring

lemma failure : appliedSectorBackground star periods signs0 0 ≠
    appliedSectorBackground star periods signs1 0 := by
  simp only [appliedSectorBackground, choice0, choice1]
  have h0 : colorIndicator (fun _ => (0 : ZMod 2)) 0 = fun _ => (1 : ℂ) := by
    funext z; simp [colorIndicator]
  have h1 : colorIndicator (fun _ => (1 : ZMod 2)) 0 = fun _ => (0 : ℂ) := by
    funext z; norm_num [colorIndicator]
  rw [h0, h1, fullA_constant, fullA_constant]
  intro h
  have hz := congrFun h (0, 0)
  norm_num at hz

end
end ConvexNivat.FullAWitness
