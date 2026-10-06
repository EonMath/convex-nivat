import NivatTrial.Divisibility
import Mathlib.Analysis.Fourier.ZMod

/-!
# Row spectra and one-sided divisibility

The Fourier transform is taken in the first coordinate, which is finite
cyclic; the transverse row index remains an unrestricted integer.
-/

namespace NivatTrial.Spectral

open NivatTrial.Algebra NivatTrial.Divisibility

noncomputable section

def mode (lam : ℂˣ) (c : ℤ → ℂ) (z : G) : ℂ :=
  ((lam ^ z.1 : ℂˣ) : ℂ) * c z.2

@[simp] theorem mode_at_zero (lam : ℂˣ) (c : ℤ → ℂ) (t : ℤ) :
    mode lam c (0, t) = c t := by simp [mode]

theorem mode_injective (lam : ℂˣ) : Function.Injective (mode lam) := by
  intro c d h
  funext t
  simpa using congrArg (fun J : G → ℂ => J (0, t)) h

@[simp] theorem mode_zero (lam : ℂˣ) : mode lam 0 = 0 := by
  funext z
  simp [mode]

@[simp] theorem mode_eq_zero_iff (lam : ℂˣ) (c : ℤ → ℂ) : mode lam c = 0 ↔ c = 0 := by
  rw [← mode_zero lam]
  exact mode_injective lam |>.eq_iff

theorem mode_add (lam : ℂˣ) (c d : ℤ → ℂ) :
    mode lam (c + d) = mode lam c + mode lam d := by
  funext z
  simp [mode, mul_add]

theorem mode_sub (lam : ℂˣ) (c d : ℤ → ℂ) :
    mode lam (c - d) = mode lam c - mode lam d := by
  funext z
  simp [mode, mul_sub]

theorem mode_smul (lam : ℂˣ) (a : ℂ) (c : ℤ → ℂ) :
    mode lam (a • c) = a • mode lam c := by
  funext z
  simp [mode, mul_left_comm]

theorem mode_shift (lam : ℂˣ) (c : ℤ → ℂ) (z u : G) :
    mode lam c (z + u) = ((lam ^ u.1 : ℂˣ) : ℂ) * mode lam (fun t => c (t + u.2)) z := by
  simp [mode, zpow_add, mul_comm, mul_assoc]

theorem mode_eigen (lam : ℂˣ) (c : ℤ → ℂ) (z : G) :
    mode lam c (z + (1, 0)) = (lam : ℂ) * mode lam c z := by
  simpa using mode_shift lam c z (1, 0)

/-- Lemma 2.0(4): action on an eigenmode evaluates the longitudinal variable. -/
theorem act_mode (lam : ℂˣ) (f : Laurent) (c : ℤ → ℂ) (z : G) :
    Algebra.act f (mode lam c) z =
      ((lam ^ z.1 : ℂˣ) : ℂ) * OneSided.act (evalX lam f) c z.2 := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp [Algebra.act_add, OneSided.act_add, hf, hg, mul_add]
  | single u a =>
    simp [Algebra.act_single, evalX_single, OneSided.act_single, mode,
      zpow_add, mul_comm, mul_left_comm, mul_assoc,
      -LaurentPolynomial.single_eq_C_mul_T]

theorem act_mode_eq_zero_iff (lam : ℂˣ) (f : Laurent) (c : ℤ → ℂ) :
    Algebra.act f (mode lam c) = 0 ↔ OneSided.act (evalX lam f) c = 0 := by
  have hmode : Algebra.act f (mode lam c) = mode lam (OneSided.act (evalX lam f) c) := by
    funext z
    exact act_mode lam f c z
  rw [hmode, mode_eq_zero_iff]

/-- The one-sided factor theorem in standard lattice coordinates. -/
theorem binomial_dvd_of_annihilates_mode (lam : ℂˣ) (f : Laurent) (c : ℤ → ℂ)
    (hc : c ≠ 0) (hside : OneSided.UpperSupport c ∨ OneSided.LowerSupport c)
    (hannihilates : Algebra.act f (mode lam c) = 0) :
    binomial (1, 0) (lam : ℂ) ∣ f := by
  apply (evalX_eq_zero_iff_dvd lam f).mp
  have hact := (act_mode_eq_zero_iff lam f c).mp hannihilates
  rcases hside with hupper | hlower
  · exact OneSided.eq_zero_of_annihilates_upperSupport hc hupper hact
  · exact OneSided.eq_zero_of_annihilates_lowerSupport hc hlower hact

abbrev Rows (n : ℕ) := ZMod n → ℤ → ℂ

def liftRows {n : ℕ} (d : Rows n) (z : G) : ℂ := d (z.1 : ZMod n) z.2

def rowCoeff (n : ℕ) [NeZero n] (d : Rows n) (k : ZMod n) (t : ℤ) : ℂ :=
  (n : ℂ)⁻¹ * ZMod.dft (fun j => d j t) k

theorem char_ne_zero {n : ℕ} [NeZero n] (k : ZMod n) : ZMod.stdAddChar k ≠ 0 := by
  have hmul : ZMod.stdAddChar k * ZMod.stdAddChar (-k) = (1 : ℂ) := by
    rw [← AddChar.map_add_eq_mul]
    simp
  intro h
  rw [h, zero_mul] at hmul
  exact zero_ne_one hmul

def eigenvalue {n : ℕ} [NeZero n] (k : ZMod n) : ℂˣ :=
  Units.mk0 (ZMod.stdAddChar k) (char_ne_zero k)

@[simp] theorem eigenvalue_val {n : ℕ} [NeZero n] (k : ZMod n) :
    (eigenvalue k : ℂ) = ZMod.stdAddChar k := rfl

theorem eigenvalue_pow {n : ℕ} [NeZero n] (k : ZMod n) : eigenvalue k ^ n = 1 := by
  ext
  simp only [Units.val_pow_eq_pow_val, eigenvalue_val, Units.val_one]
  rw [← AddChar.map_nsmul_eq_pow]
  simp [nsmul_eq_mul]

theorem eigenvalue_injective {n : ℕ} [NeZero n] :
    Function.Injective (eigenvalue (n := n)) := by
  intro k l h
  apply ZMod.injective_stdAddChar
  exact congrArg (fun u : ℂˣ => (u : ℂ)) h

theorem char_int_mul {n : ℕ} [NeZero n] (s : ℤ) (k : ZMod n) :
    ZMod.stdAddChar ((s : ZMod n) * k) = ((eigenvalue k ^ s : ℂˣ) : ℂ) := by
  rw [Units.val_zpow_eq_zpow_val, eigenvalue_val, ← AddChar.map_zsmul_eq_zpow]
  congr 1
  simp [zsmul_eq_mul]

def projectionPolynomial (n : ℕ) [NeZero n] (k : ZMod n) : Laurent :=
  ∑ j : ZMod n, AddMonoidAlgebra.single ((j.val : ℤ), 0)
    ((n : ℂ)⁻¹ * ZMod.stdAddChar (-(j * k)))

def project (n : ℕ) [NeZero n] (k : ZMod n) (J : G → ℂ) : G → ℂ :=
  Algebra.act (projectionPolynomial n k) J

/-- The Fourier transform of a cyclic shift acquires its character factor. -/
theorem dft_shift {n : ℕ} [NeZero n] (d : ZMod n → ℂ) (a k : ZMod n) :
    ZMod.dft (fun j => d (a + j)) k = ZMod.stdAddChar (a * k) * ZMod.dft d k := by
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.mul_sum]
  apply Fintype.sum_equiv (Equiv.addLeft a)
  intro j
  change ZMod.stdAddChar (-(j * k)) * d (a + j) =
    ZMod.stdAddChar (a * k) * (ZMod.stdAddChar (-((a + j) * k)) * d (a + j))
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

/-- Lemma 2.0(1): a projection separates into a longitudinal character and a row coefficient. -/
theorem project_liftRows {n : ℕ} [NeZero n] (d : Rows n) (k : ZMod n) (z : G) :
    project n k (liftRows d) z = mode (eigenvalue k) (rowCoeff n d k) z := by
  have hshift := dft_shift (fun j => d j z.2) (z.1 : ZMod n) k
  calc
    project n k (liftRows d) z =
        (n : ℂ)⁻¹ * ZMod.dft (fun j => d ((z.1 : ZMod n) + j) z.2) k := by
      simp [project, projectionPolynomial, Algebra.act_sum, Algebra.act_single,
        liftRows, ZMod.dft_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    _ = mode (eigenvalue k) (rowCoeff n d k) z := by
      rw [hshift, char_int_mul]
      simp [mode, rowCoeff, mul_left_comm]

theorem project_liftRows_fun {n : ℕ} [NeZero n] (d : Rows n) (k : ZMod n) :
    project n k (liftRows d) = mode (eigenvalue k) (rowCoeff n d k) := by
  funext z
  exact project_liftRows d k z

/-- Completeness of the row Fourier decomposition. -/
theorem sum_project_liftRows {n : ℕ} [NeZero n] (d : Rows n) :
    (∑ k : ZMod n, project n k (liftRows d)) = liftRows d := by
  funext z
  have h := congrFun ((ZMod.dft (N := n)).symm_apply_apply (fun j => d j z.2))
    (z.1 : ZMod n)
  rw [ZMod.invDFT_apply] at h
  have hchar (k : ZMod n) : ZMod.stdAddChar (k * (z.1 : ZMod n)) =
      ((eigenvalue k ^ z.1 : ℂˣ) : ℂ) := by rw [mul_comm, char_int_mul]
  simp_rw [hchar] at h
  simpa [project_liftRows, mode, rowCoeff, liftRows,
    Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using h

/-- Lemma 2.0(2): every projected field is an eigenfield for the unit shift. -/
theorem project_eigen {n : ℕ} [NeZero n] (d : Rows n) (k : ZMod n) (z : G) :
    project n k (liftRows d) (z + (1, 0)) =
      (eigenvalue k : ℂ) * project n k (liftRows d) z := by
  simp only [project_liftRows]
  exact mode_eigen _ _ _

/-- Lemma 2.0(3): a spectral projection commutes with every Laurent action. -/
theorem project_act {n : ℕ} [NeZero n] (k : ZMod n) (f : Laurent) (J : G → ℂ) :
    project n k (Algebra.act f J) = Algebra.act f (project n k J) := by
  exact Algebra.act_comm _ _ _

theorem project_add {n : ℕ} [NeZero n] (k : ZMod n) (J K : G → ℂ) :
    project n k (J + K) = project n k J + project n k K := by
  exact Algebra.act_add_config _ _ _

theorem project_sub {n : ℕ} [NeZero n] (k : ZMod n) (J K : G → ℂ) :
    project n k (J - K) = project n k J - project n k K := by
  exact Algebra.act_sub_config _ _ _

@[simp] theorem project_zero {n : ℕ} [NeZero n] (k : ZMod n) :
    project n k 0 = 0 := by
  exact Algebra.act_zero_config _

theorem rowCoeff_add {n : ℕ} [NeZero n] (d e : Rows n) (k : ZMod n) :
    rowCoeff n (d + e) k = rowCoeff n d k + rowCoeff n e k := by
  funext t
  simp [rowCoeff, ZMod.dft_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]

theorem rowCoeff_sub {n : ℕ} [NeZero n] (d e : Rows n) (k : ZMod n) :
    rowCoeff n (d - e) k = rowCoeff n d k - rowCoeff n e k := by
  funext t
  simp [rowCoeff, ZMod.dft_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]

theorem rowCoeff_smul {n : ℕ} [NeZero n] (a : ℂ) (d : Rows n) (k : ZMod n) :
    rowCoeff n (a • d) k = a • rowCoeff n d k := by
  funext t
  simp [rowCoeff, ZMod.dft_apply, smul_eq_mul, mul_left_comm, ← Finset.mul_sum]

theorem rowCoeff_eq_zero_of_row_zero {n : ℕ} [NeZero n]
    (d : Rows n) (k : ZMod n) (t : ℤ) (ht : ∀ j, d j t = 0) : rowCoeff n d k t = 0 := by
  simp [rowCoeff, ZMod.dft_apply, ht]

theorem rowCoeff_upperSupport {n : ℕ} [NeZero n] (d : Rows n) (k : ZMod n)
    (c : ℤ) (hzero : ∀ j t, c < t → d j t = 0) :
    OneSided.UpperSupport (rowCoeff n d k) := by
  refine ⟨c, fun t ht => rowCoeff_eq_zero_of_row_zero d k t ?_⟩
  exact fun j => hzero j t ht

theorem rowCoeff_lowerSupport {n : ℕ} [NeZero n] (d : Rows n) (k : ZMod n)
    (c : ℤ) (hzero : ∀ j t, t < c → d j t = 0) :
    OneSided.LowerSupport (rowCoeff n d k) := by
  refine ⟨c, fun t ht => rowCoeff_eq_zero_of_row_zero d k t ?_⟩
  exact fun j => hzero j t ht

theorem occurs_iff_rowCoeff_ne_zero {n : ℕ} [NeZero n] (d : Rows n) (k : ZMod n) :
    project n k (liftRows d) ≠ 0 ↔ rowCoeff n d k ≠ 0 := by
  rw [project_liftRows_fun, ne_eq, mode_eq_zero_iff]

/-- A nonzero cyclic field has a nonempty row spectrum. -/
theorem exists_occurring_frequency {n : ℕ} [NeZero n] (d : Rows n)
    (hd : liftRows d ≠ 0) : ∃ k : ZMod n, project n k (liftRows d) ≠ 0 := by
  by_contra h
  have hz : ∀ k : ZMod n, project n k (liftRows d) = 0 := by
    simpa using h
  apply hd
  rw [← sum_project_liftRows d]
  simp [hz]

/-- Lemma 2.3 for a field already represented in cyclic rows. -/
theorem lemma2_3_rows {n : ℕ} [NeZero n] (d : Rows n) (k : ZMod n) (f : Laurent)
    (hoccurs : project n k (liftRows d) ≠ 0)
    (hside : (∃ c : ℤ, ∀ j t, c < t → d j t = 0) ∨
      (∃ c : ℤ, ∀ j t, t < c → d j t = 0))
    (hannihilates : Algebra.act f (liftRows d) = 0) :
    binomial (1, 0) (eigenvalue k : ℂ) ∣ f := by
  apply binomial_dvd_of_annihilates_mode
  · exact (occurs_iff_rowCoeff_ne_zero d k).mp hoccurs
  · rcases hside with ⟨c, hc⟩ | ⟨c, hc⟩
    · exact Or.inl (rowCoeff_upperSupport d k c hc)
    · exact Or.inr (rowCoeff_lowerSupport d k c hc)
  · rw [← project_liftRows_fun, ← project_act, hannihilates, project_zero]

/-- Periodicity along the longitudinal coordinate. -/
def LongitudinalPeriodic (n : ℕ) (J : G → ℂ) : Prop :=
  ∀ s t : ℤ, J (s + n, t) = J (s, t)

def rowsOfConfig (n : ℕ) (J : G → ℂ) : Rows n :=
  fun j t => J (j.val, t)

theorem liftRows_periodic {n : ℕ} (d : Rows n) : LongitudinalPeriodic n (liftRows d) := by
  intro s t
  simp [liftRows, Int.cast_add]

/-- An integer-periodic configuration factors through the finite cyclic coordinate. -/
theorem liftRows_rowsOfConfig {n : ℕ} [NeZero n] (J : G → ℂ)
    (hperiodic : LongitudinalPeriodic n J) : liftRows (rowsOfConfig n J) = J := by
  funext z
  let r : ℤ := (z.1 : ZMod n).val
  have hcast : (r : ZMod n) = (z.1 : ZMod n) := by simp [r]
  have hdiv : (n : ℤ) ∣ z.1 - r :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub r z.1 n).mp hcast
  obtain ⟨k, hk⟩ := hdiv
  have hperiod : Function.Periodic (fun s : ℤ => J (s, z.2)) (n : ℤ) :=
    fun s => hperiodic s z.2
  have hshift := (hperiod.int_mul k) r
  have hs : r + k * n = z.1 := by
    rw [mul_comm] at hk
    omega
  change J (r, z.2) = J z
  simpa [hs] using hshift.symm

/-- Completeness for an arbitrary periodic field, without a chosen row representation. -/
theorem sum_project {n : ℕ} [NeZero n] (J : G → ℂ)
    (hperiodic : LongitudinalPeriodic n J) : (∑ k : ZMod n, project n k J) = J := by
  simpa [liftRows_rowsOfConfig J hperiodic] using sum_project_liftRows (rowsOfConfig n J)

theorem project_eq_mode {n : ℕ} [NeZero n] (J : G → ℂ) (k : ZMod n)
    (hperiodic : LongitudinalPeriodic n J) :
    project n k J = mode (eigenvalue k) (rowCoeff n (rowsOfConfig n J) k) := by
  simpa [liftRows_rowsOfConfig J hperiodic] using project_liftRows_fun (rowsOfConfig n J) k

theorem exists_occurs {n : ℕ} [NeZero n] (J : G → ℂ)
    (hperiodic : LongitudinalPeriodic n J) (hJ : J ≠ 0) :
    ∃ k : ZMod n, project n k J ≠ 0 := by
  have hrows : liftRows (rowsOfConfig n J) ≠ 0 := by
    simpa [liftRows_rowsOfConfig J hperiodic] using hJ
  simpa [liftRows_rowsOfConfig J hperiodic] using exists_occurring_frequency (rowsOfConfig n J) hrows

theorem project_eigen_of_periodic {n : ℕ} [NeZero n] (J : G → ℂ)
    (hperiodic : LongitudinalPeriodic n J) (k : ZMod n) (z : G) :
    project n k J (z + (1, 0)) = (eigenvalue k : ℂ) * project n k J z := by
  simpa [liftRows_rowsOfConfig J hperiodic] using project_eigen (rowsOfConfig n J) k z

theorem lemma2_3_standard {n : ℕ} [NeZero n] (J : G → ℂ) (k : ZMod n) (f : Laurent)
    (hperiodic : LongitudinalPeriodic n J) (hoccurs : project n k J ≠ 0)
    (hside : (∃ c : ℤ, ∀ z : G, c < z.2 → J z = 0) ∨
      (∃ c : ℤ, ∀ z : G, z.2 < c → J z = 0))
    (hannihilates : Algebra.act f J = 0) : binomial (1, 0) (eigenvalue k : ℂ) ∣ f := by
  apply lemma2_3_rows (rowsOfConfig n J) k f
  · simpa [liftRows_rowsOfConfig J hperiodic] using hoccurs
  · rcases hside with ⟨c, hc⟩ | ⟨c, hc⟩
    · exact Or.inl ⟨c, fun j t ht => hc (j.val, t) ht⟩
    · exact Or.inr ⟨c, fun j t ht => hc (j.val, t) ht⟩
  · simpa [liftRows_rowsOfConfig J hperiodic] using hannihilates

def inCoordinates (e : G ≃+ G) (J : G → ℂ) (z : G) : ℂ := J (e z)

def AlongPeriodic (e : G ≃+ G) (n : ℕ) (J : G → ℂ) : Prop :=
  LongitudinalPeriodic n (inCoordinates e J)

def projectAlong (e : G ≃+ G) (n : ℕ) [NeZero n] (k : ZMod n) (J : G → ℂ) : G → ℂ :=
  Algebra.act (changeCoordinates e (projectionPolynomial n k)) J

theorem projectAlong_apply {n : ℕ} [NeZero n] (e : G ≃+ G)
    (k : ZMod n) (J : G → ℂ) (z : G) :
    projectAlong e n k J (e z) = project n k (inCoordinates e J) z := by
  exact changeCoordinates_act e _ J z

theorem projectAlong_eq_zero_iff {n : ℕ} [NeZero n] (e : G ≃+ G)
    (k : ZMod n) (J : G → ℂ) :
    projectAlong e n k J = 0 ↔ project n k (inCoordinates e J) = 0 := by
  constructor
  · intro h
    funext z
    simpa [projectAlong_apply] using congrArg (fun K : G → ℂ => K (e z)) h
  · intro h
    funext z
    have hz := congrArg (fun K : G → ℂ => K (e.symm z)) h
    simpa [← projectAlong_apply] using hz

theorem projectAlong_act {n : ℕ} [NeZero n] (e : G ≃+ G)
    (k : ZMod n) (f : Laurent) (J : G → ℂ) :
    projectAlong e n k (Algebra.act f J) = Algebra.act f (projectAlong e n k J) := by
  exact Algebra.act_comm _ _ _

theorem sum_projectAlong {n : ℕ} [NeZero n] (e : G ≃+ G) (J : G → ℂ)
    (hperiodic : AlongPeriodic e n J) : (∑ k : ZMod n, projectAlong e n k J) = J := by
  funext z
  have h := congrArg (fun K : G → ℂ => K (e.symm z)) (sum_project (inCoordinates e J) hperiodic)
  simpa [Finset.sum_apply, ← projectAlong_apply, inCoordinates] using h

/-- Lemma 2.3, including the integral coordinate change from the paper. -/
theorem lemma2_3 {n : ℕ} [NeZero n] (e : G ≃+ G) (J : G → ℂ)
    (k : ZMod n) (f : Laurent) (hperiodic : AlongPeriodic e n J)
    (hoccurs : projectAlong e n k J ≠ 0)
    (hside : (∃ c : ℤ, ∀ z : G, c < (e.symm z).2 → J z = 0) ∨
      (∃ c : ℤ, ∀ z : G, (e.symm z).2 < c → J z = 0))
    (hannihilates : Algebra.act f J = 0) : binomial (e (1, 0)) (eigenvalue k : ℂ) ∣ f := by
  apply (evalAlong_eq_zero_iff_dvd e (eigenvalue k) f).mp
  apply (evalX_eq_zero_iff_dvd (eigenvalue k) (changeCoordinates e.symm f)).mpr
  apply lemma2_3_standard (inCoordinates e J) k (changeCoordinates e.symm f) hperiodic
  · exact (projectAlong_eq_zero_iff e k J).not.mp hoccurs
  · rcases hside with ⟨c, hc⟩ | ⟨c, hc⟩
    · exact Or.inl ⟨c, fun z hz => hc (e z) (by simpa using hz)⟩
    · exact Or.inr ⟨c, fun z hz => hc (e z) (by simpa using hz)⟩
  · funext z
    have h := changeCoordinates_act e (changeCoordinates e.symm f) J z
    rw [changeCoordinates_apply_symm] at h
    change Algebra.act (changeCoordinates e.symm f) (fun w => J (e w)) z = 0
    rw [← h, hannihilates]
    rfl

/-- Local membership in the translation orbit closure, phrased through finite patches. -/
def LocalOrbitLimit (J K : G → ℂ) : Prop :=
  ∀ S : Finset G, ∃ u : G, ∀ z ∈ S, J (u + z) = K z

theorem LocalOrbitLimit.refl (J : G → ℂ) : LocalOrbitLimit J J := by
  intro S
  exact ⟨0, by simp⟩

theorem LocalOrbitLimit.translate (J : G → ℂ) (v : G) :
    LocalOrbitLimit J (fun z => J (v + z)) := by
  intro S
  exact ⟨v, fun _ _ => rfl⟩

/-- Lemma 2.4(a): a finite Laurent relation passes to local orbit limits. -/
theorem act_const_of_localOrbitLimit (f : Laurent) (J K : G → ℂ) (c : ℂ)
    (hlimit : LocalOrbitLimit J K) (hrelation : Algebra.act f J = fun _ => c) :
    Algebra.act f K = fun _ => c := by
  classical
  funext z
  obtain ⟨u, hu⟩ := hlimit (f.coeff.support.image fun v => z + v)
  calc
    Algebra.act f K z = Algebra.act f J (u + z) := by
      unfold Algebra.act
      apply Finsupp.sum_congr
      intro v hv
      have hlocal := hu (z + v) (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
      rw [← hlocal, add_assoc]
    _ = c := congrFun hrelation (u + z)

/-- Lemma 2.4(b): subtracting two constant relations gives an annihilator. -/
theorem annihilates_difference_of_localOrbitLimits (f : Laurent) (J K L : G → ℂ) (c : ℂ)
    (hK : LocalOrbitLimit J K) (hL : LocalOrbitLimit J L)
    (hrelation : Algebra.act f J = fun _ => c) : Algebra.act f (K - L) = 0 := by
  rw [Algebra.act_sub_config, act_const_of_localOrbitLimit f J K c hK hrelation,
    act_const_of_localOrbitLimit f J L c hL hrelation, sub_self]

/-- Lemma 2.4(c,d): the spectral factors of finitely many one-sided witnesses
divide every common annihilator. Separation is given either by a nonzero
transverse coordinate or by distinct eigenvalues in the same coordinates. -/
theorem lemma2_4_product {ι : Type*} (s : Finset ι)
    (n : ι → ℕ) [∀ i, NeZero (n i)] (e : ι → G ≃+ G)
    (k : ∀ i, ZMod (n i)) (d : ι → G → ℂ) (f : Laurent)
    (hperiodic : ∀ i ∈ s, AlongPeriodic (e i) (n i) (d i))
    (hoccurs : ∀ i ∈ s, projectAlong (e i) (n i) (k i) (d i) ≠ 0)
    (hside : ∀ i ∈ s,
      (∃ c : ℤ, ∀ z : G, c < ((e i).symm z).2 → d i z = 0) ∨
      (∃ c : ℤ, ∀ z : G, ((e i).symm z).2 < c → d i z = 0))
    (hseparate : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ((e i).symm (e j (1, 0))).2 ≠ 0 ∨
      (e i = e j ∧ (eigenvalue (k i) : ℂ) ≠ (eigenvalue (k j) : ℂ)))
    (hannihilates : ∀ i ∈ s, Algebra.act f (d i) = 0) :
    (∏ i ∈ s, binomial (e i (1, 0)) (eigenvalue (k i) : ℂ)) ∣ f := by
  apply prod_dvd_of_prime_factors
  · intro i _
    exact binomial_along_prime (e i) (eigenvalue (k i))
  · intro i hi j hj hne
    rcases hseparate i hi j hj hne with htransverse | ⟨he, hvalues⟩
    · exact binomial_not_dvd_of_transverse_ne_zero (e i) (eigenvalue (k i))
        (e j (1, 0)) (eigenvalue (k j) : ℂ) htransverse
    · rw [← he]
      exact binomial_not_dvd_of_values_ne (e i) (eigenvalue (k i)) (eigenvalue (k j)) hvalues
  · intro i hi
    exact lemma2_3 (e i) (d i) (k i) f (hperiodic i hi) (hoccurs i hi)
      (hside i hi) (hannihilates i hi)

/-- Nonzero complex polynomials cannot vanish at every sufficiently large integer. -/
theorem exists_large_nat_eval_ne_zero (p : Polynomial ℂ) (hp : p ≠ 0) (B : ℕ) :
    ∃ N : ℕ, B ≤ N ∧ p.eval (N : ℂ) ≠ 0 := by
  by_contra! h
  apply hp
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hinj : Function.Injective (fun m : ℕ => ((m + B : ℕ) : ℂ)) := by
    intro a b hab
    exact Nat.add_right_cancel (Nat.cast_injective hab)
  have hinfinite := Set.infinite_range_of_injective hinj
  apply hinfinite.mono
  rintro z ⟨m, rfl⟩
  exact h (m + B) (by omega)

def encodingPolynomial {α : Type*} [Fintype α] (rank : α → ℕ) (c : α → ℂ) : Polynomial ℂ :=
  ∑ a : α, Polynomial.monomial (rank a) (c a)

theorem encodingPolynomial_coeff {α : Type*} [Fintype α]
    (rank : α → ℕ) (hrank : Function.Injective rank) (c : α → ℂ) (a : α) :
    (encodingPolynomial rank c).coeff (rank a) = c a := by
  classical
  simp [encodingPolynomial, Polynomial.coeff_monomial, hrank.eq_iff]

theorem encodingPolynomial_ne_zero {α : Type*} [Fintype α]
    (rank : α → ℕ) (hrank : Function.Injective rank) (c : α → ℂ) (hc : c ≠ 0) :
    encodingPolynomial rank c ≠ 0 := by
  intro h
  apply hc
  funext a
  have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff (rank a)) h
  simpa only [encodingPolynomial_coeff rank hrank, Polynomial.coeff_zero, Pi.zero_apply] using hcoeff

theorem encodingPolynomial_eval {α : Type*} [Fintype α]
    (rank : α → ℕ) (c : α → ℂ) (x : ℂ) :
    (encodingPolynomial rank c).eval x = ∑ a : α, c a * x ^ rank a := by
  simp [encodingPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

/-- Lemma 2.2 in its finite-linear-form formulation. A single integer-valued
injection avoids the zeros of all the selected nonzero spectral forms. -/
theorem exists_integer_encoding {α ι : Type*} [Fintype α] (s : Finset ι)
    (c : ι → α → ℂ) (hc : ∀ i ∈ s, c i ≠ 0) :
    ∃ w : α → ℤ, Function.Injective w ∧ ∀ i ∈ s, (∑ a : α, (w a : ℂ) * c i a) ≠ 0 := by
  classical
  let rank : α → ℕ := fun a => (Fintype.equivFin α a).val
  have hrank : Function.Injective rank := by
    intro a b h
    exact (Fintype.equivFin α).injective (Fin.ext h)
  let p : Polynomial ℂ := ∏ i ∈ s, encodingPolynomial rank (c i)
  have hp : p ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact encodingPolynomial_ne_zero rank hrank (c i) (hc i hi)
  obtain ⟨N, hN, heval⟩ := exists_large_nat_eval_ne_zero p hp 2
  let w : α → ℤ := fun a => (N : ℤ) ^ rank a
  have hbase : (1 : ℤ) < N := by omega
  refine ⟨w, (pow_right_strictMono₀ hbase).injective.comp hrank, ?_⟩
  intro i hi hzero
  have hfactorzero : (encodingPolynomial rank (c i)).eval (N : ℂ) = 0 := by
    rw [encodingPolynomial_eval]
    simpa [w, mul_comm] using hzero
  apply heval
  change (∏ j ∈ s, encodingPolynomial rank (c j)).eval (N : ℂ) = 0
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero_iff.mpr ⟨i, hi, hfactorzero⟩

def encodedDifference {α : Type*} (w : α → ℤ) (Xi Gtail : G → α) (z : G) : ℂ :=
  (w (Xi z) : ℂ) - (w (Gtail z) : ℂ)

def colourDifference {α : Type*} [DecidableEq α] (Xi Gtail : G → α) (a : α) (z : G) : ℂ :=
  (if Xi z = a then 1 else 0) - (if Gtail z = a then 1 else 0)

/-- The encoded difference is the integer-weighted sum of colour indicator differences. -/
theorem encodedDifference_eq_sum {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℤ) (Xi Gtail : G → α) :
    encodedDifference w Xi Gtail =
      ∑ a : α, (w a : ℂ) • colourDifference Xi Gtail a := by
  funext z
  simp [encodedDifference, colourDifference, Finset.sum_apply, mul_sub,
    Finset.sum_sub_distrib]

theorem encodedDifference_eq_zero_iff {α : Type*} (w : α → ℤ)
    (hw : Function.Injective w) (Xi Gtail : G → α) :
    encodedDifference w Xi Gtail = 0 ↔ Xi = Gtail := by
  constructor
  · intro h
    funext z
    have hz := congrArg (fun J : G → ℂ => J z) h
    have hcast : (w (Xi z) : ℂ) = (w (Gtail z) : ℂ) := sub_eq_zero.mp hz
    exact hw (Int.cast_injective hcast)
  · rintro rfl
    funext z
    simp [encodedDifference]

theorem project_smul {n : ℕ} [NeZero n] (k : ZMod n) (a : ℂ) (J : G → ℂ) :
    project n k (a • J) = a • project n k J := by
  exact Algebra.act_smul_config _ _ _

theorem project_sum {n : ℕ} [NeZero n] {ι : Type*}
    (k : ZMod n) (s : Finset ι) (J : ι → G → ℂ) :
    project n k (∑ i ∈ s, J i) = ∑ i ∈ s, project n k (J i) := by
  exact Algebra.act_sum_config _ _ _

theorem projectAlong_smul {n : ℕ} [NeZero n] (e : G ≃+ G)
    (k : ZMod n) (a : ℂ) (J : G → ℂ) :
    projectAlong e n k (a • J) = a • projectAlong e n k J := by
  exact Algebra.act_smul_config _ _ _

theorem projectAlong_sum {n : ℕ} [NeZero n] {ι : Type*} (e : G ≃+ G)
    (k : ZMod n) (s : Finset ι) (J : ι → G → ℂ) :
    projectAlong e n k (∑ i ∈ s, J i) = ∑ i ∈ s, projectAlong e n k (J i) := by
  exact Algebra.act_sum_config _ _ _

theorem projectAlong_encodedDifference {n : ℕ} [NeZero n]
    {α : Type*} [Fintype α] [DecidableEq α]
    (e : G ≃+ G) (k : ZMod n) (w : α → ℤ) (Xi Gtail : G → α) (z : G) :
    projectAlong e n k (encodedDifference w Xi Gtail) z =
      ∑ a : α, (w a : ℂ) * projectAlong e n k (colourDifference Xi Gtail a) z := by
  rw [encodedDifference_eq_sum, projectAlong_sum]
  simp only [Finset.sum_apply, projectAlong_smul, Pi.smul_apply, smul_eq_mul]

/-- The selected colour frequencies survive in a single integer encoding. -/
theorem exists_spectrum_preserving_encoding {α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι]
    (n : ι → ℕ) [∀ i, NeZero (n i)] (e : ι → G ≃+ G)
    (k : ∀ i, ZMod (n i)) (Xi Gtail : ι → G → α)
    (hoccurs : ∀ i, ∃ z : G, ∃ a : α,
      projectAlong (e i) (n i) (k i) (colourDifference (Xi i) (Gtail i) a) z ≠ 0) :
    ∃ w : α → ℤ, Function.Injective w ∧ ∀ i,
      projectAlong (e i) (n i) (k i) (encodedDifference w (Xi i) (Gtail i)) ≠ 0 := by
  classical
  choose z a hza using hoccurs
  let c : ι → α → ℂ := fun i b =>
    projectAlong (e i) (n i) (k i) (colourDifference (Xi i) (Gtail i) b) (z i)
  have hc : ∀ i ∈ (Finset.univ : Finset ι), c i ≠ 0 := by
    intro i _ h
    exact hza i (congrFun h (a i))
  obtain ⟨w, hw, hnonzero⟩ := exists_integer_encoding Finset.univ c hc
  refine ⟨w, hw, fun i h => ?_⟩
  apply hnonzero i (Finset.mem_univ i)
  have hz := congrArg (fun J : G → ℂ => J (z i)) h
  simpa only [projectAlong_encodedDifference, Pi.zero_apply] using hz

theorem colourDifference_zero_of_equal {α : Type*} [DecidableEq α]
    (Xi Gtail : G → α) (a : α) (z : G) (hz : Xi z = Gtail z) :
    colourDifference Xi Gtail a z = 0 := by
  simp [colourDifference, hz]

theorem encodedDifference_zero_of_equal {α : Type*}
    (w : α → ℤ) (Xi Gtail : G → α) (z : G) (hz : Xi z = Gtail z) :
    encodedDifference w Xi Gtail z = 0 := by
  simp [encodedDifference, hz]

theorem colourDifference_periodic {α : Type*} [DecidableEq α]
    (n : ℕ) (e : G ≃+ G) (Xi Gtail : G → α) (a : α)
    (hXi : ∀ s t : ℤ, Xi (e (s + n, t)) = Xi (e (s, t)))
    (hGtail : ∀ s t : ℤ, Gtail (e (s + n, t)) = Gtail (e (s, t))) :
    AlongPeriodic e n (colourDifference Xi Gtail a) := by
  intro s t
  simp [inCoordinates, colourDifference, hXi, hGtail]

theorem encodedDifference_periodic {α : Type*} (n : ℕ)
    (e : G ≃+ G) (w : α → ℤ) (Xi Gtail : G → α)
    (hXi : ∀ s t : ℤ, Xi (e (s + n, t)) = Xi (e (s, t)))
    (hGtail : ∀ s t : ℤ, Gtail (e (s + n, t)) = Gtail (e (s, t))) :
    AlongPeriodic e n (encodedDifference w Xi Gtail) := by
  intro s t
  simp [inCoordinates, encodedDifference, hXi, hGtail]

theorem binomial_annihilates_mode (lam : ℂˣ) (c : ℤ → ℂ) :
    Algebra.act (binomial (1, 0) (lam : ℂ)) (mode lam c) = 0 := by
  rw [binomial, Algebra.act_sub]
  funext z
  simp [monomial, mode_eigen, Algebra.act_single, scalar_apply]

def spectralAnnihilator (n : ℕ) [NeZero n] (s : Finset (ZMod n)) : Laurent :=
  ∏ k ∈ s, binomial (1, 0) (eigenvalue k : ℂ)

theorem spectralAnnihilator_ne_zero {n : ℕ} [NeZero n] (s : Finset (ZMod n)) :
    spectralAnnihilator n s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k _
  exact binomial_x_ne_zero _

theorem factor_dvd_spectralAnnihilator {n : ℕ} [NeZero n] (s : Finset (ZMod n))
    (k : ZMod n) (hk : k ∈ s) : binomial (1, 0) (eigenvalue k : ℂ) ∣ spectralAnnihilator n s := by
  exact Finset.dvd_prod_of_mem _ hk

/-- Property (P3): the product of the occurring spectral factors annihilates the field. -/
theorem spectralAnnihilator_annihilates {n : ℕ} [NeZero n] (s : Finset (ZMod n))
    (J : G → ℂ) (hperiodic : LongitudinalPeriodic n J)
    (hspectrum : ∀ k : ZMod n, k ∉ s → project n k J = 0) :
    Algebra.act (spectralAnnihilator n s) J = 0 := by
  rw [← sum_project J hperiodic, Algebra.act_sum_config]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k ∈ s
  · apply Algebra.act_eq_zero_of_dvd (factor_dvd_spectralAnnihilator s k hk)
    rw [project_eq_mode J k hperiodic]
    exact binomial_annihilates_mode _ _
  · rw [hspectrum k hk, Algebra.act_zero_config]

end

end NivatTrial.Spectral
