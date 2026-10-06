import Mathlib

open scoped BigOperators

namespace ConvexNivat

/-! Standalone declarations for source Lemma 2.0 and the finite linear-algebra
step behind Lemma 2.2. The literal lattice type avoids redeclaring shared Core. -/

noncomputable section

/-- The distinct κ-th roots of unity in ℂ. -/
def rootSpectrum (κ : ℕ) : Finset ℂ := Polynomial.nthRootsFinset κ 1

/-- Source §2.2: the actual finite Fourier projection along v. -/
def spectralProjection (v : ℤ × ℤ) (κ : ℕ) (ζ : ℂ)
    (d : (ℤ × ℤ) → ℂ) : (ℤ × ℤ) → ℂ :=
  fun z => (κ : ℂ)⁻¹ * ∑ k ∈ Finset.range κ,
    ζ ^ (-(k : ℤ)) * d (z + (k : ℤ) • v)

/-- The Fourier coefficient on the row indexed by t, relative to v,u. -/
def spectralRowCoefficient (v u : ℤ × ℤ) (κ : ℕ) (ζ : ℂ)
    (d : (ℤ × ℤ) → ℂ) (t : ℤ) : ℂ :=
  (κ : ℂ)⁻¹ * ∑ k ∈ Finset.range κ,
    ζ ^ (-(k : ℤ)) * d ((k : ℤ) • v + t • u)

/-- A root occurs exactly when its projection is not the zero field. -/
def spectralOccurs (v : ℤ × ℤ) (κ : ℕ) (ζ : ℂ)
    (d : (ℤ × ℤ) → ℂ) : Prop :=
  spectralProjection v κ ζ d ≠ 0

private lemma spectrum_nonzero (κ : ℕ) (hκ : 0 < κ) (ζ : ℂ)
    (hζ : ζ ^ κ = 1) : ζ ≠ 0 := by
  intro hz
  simp [hz, Nat.ne_of_gt hκ] at hζ

private lemma projection_step (v : ℤ × ℤ) (κ : ℕ) (hκ : 0 < κ)
    (ζ : ℂ) (hζ : ζ ^ κ = 1) (d : (ℤ × ℤ) → ℂ)
    (hd : ∀ z, d (z + (κ : ℤ) • v) = d z) (z : ℤ × ℤ) :
    spectralProjection v κ ζ d (z + v) = ζ * spectralProjection v κ ζ d z := by
  have hζ0 := spectrum_nonzero κ hκ ζ hζ
  let f : ℕ → ℂ := fun k => ζ ^ (-(k : ℤ)) * d (z + (k : ℤ) • v)
  have hf : f κ = f 0 := by
    simp only [f, Nat.cast_zero, zero_smul, add_zero,
      zpow_neg, zpow_natCast, hζ, pow_zero, inv_one, one_mul]
    exact hd z
  have hsum : (∑ k ∈ Finset.range κ, f (k + 1)) = ∑ k ∈ Finset.range κ, f k := by
    have hh := (Finset.sum_range_succ' f κ).symm.trans (Finset.sum_range_succ f κ)
    rw [hf] at hh
    exact add_right_cancel hh
  have hterm (k : ℕ) :
      ζ ^ (-(k : ℤ)) * d (z + v + (k : ℤ) • v) = ζ * f (k + 1) := by
    have hz : z + v + (k : ℤ) • v = z + ((k + 1 : ℕ) : ℤ) • v := by
      simp [add_smul, add_assoc, add_comm, add_left_comm]
    rw [hz]
    dsimp [f]
    have hp : ζ ^ (-(k : ℤ)) = ζ * ζ ^ (-((k + 1 : ℕ) : ℤ)) := by
      calc
        ζ ^ (-(k : ℤ)) = ζ ^ (1 + -((k + 1 : ℕ) : ℤ)) := by
          congr 1
          push_cast
          ring
        _ = ζ * ζ ^ (-((k + 1 : ℕ) : ℤ)) := by
          rw [zpow_add₀ hζ0, zpow_one]
    rw [hp]
    simp only [Nat.cast_add, Nat.cast_one, mul_assoc]
  simp only [spectralProjection]
  simp_rw [hterm]
  rw [← Finset.mul_sum, hsum]
  ring

private lemma projection_integer_shift (v : ℤ × ℤ) (κ : ℕ) (hκ : 0 < κ)
    (ζ : ℂ) (hζ : ζ ^ κ = 1) (d : (ℤ × ℤ) → ℂ)
    (hd : ∀ z, d (z + (κ : ℤ) • v) = d z) (z : ℤ × ℤ) (s : ℤ) :
    spectralProjection v κ ζ d (z + s • v) = ζ ^ s * spectralProjection v κ ζ d z := by
  have hζ0 := spectrum_nonzero κ hκ ζ hζ
  induction s using Int.induction_on with
  | zero => simp
  | succ s hs =>
      have hz : z + ((s : ℤ) + 1) • v = (z + (s : ℤ) • v) + v := by
        simp [add_smul, add_assoc]
      rw [hz, projection_step v κ hκ ζ hζ d hd, hs, zpow_add₀ hζ0]
      simp [mul_comm, mul_left_comm]
  | pred s hs =>
      have hz : (z + (-(s : ℤ) - 1) • v) + v = z + (-(s : ℤ)) • v := by
        simp only [sub_smul, one_smul]
        abel
      have hh := projection_step v κ hκ ζ hζ d hd (z + (-(s : ℤ) - 1) • v)
      rw [hz, hs] at hh
      have hp : ζ * ζ ^ (-(s : ℤ) - 1) = ζ ^ (-(s : ℤ)) := by
        calc
          _ = ζ ^ (1 + (-(s : ℤ) - 1)) := by rw [zpow_add₀ hζ0, zpow_one]
          _ = _ := by congr 1; omega
      apply (mul_left_cancel₀ hζ0)
      rw [← mul_assoc, hp, ← hh]

/-- Lemma 2.0(1), rowwise formula. No basis condition is needed for this identity. -/
theorem spectral_projection_row_formula (v u : ℤ × ℤ) (κ : ℕ)
    (hκ : 0 < κ) (ζ : ℂ) (hζ : ζ ^ κ = 1) (d : (ℤ × ℤ) → ℂ)
    (hd : ∀ z, d (z + (κ : ℤ) • v) = d z) (s t : ℤ) :
    spectralProjection v κ ζ d (s • v + t • u) =
      ζ ^ s * spectralRowCoefficient v u κ ζ d t := by
  simpa [spectralProjection, spectralRowCoefficient, add_comm] using
    projection_integer_shift v κ hκ ζ hζ d hd (t • u) s

private lemma spectrum_sum (κ : ℕ) (hκ : 0 < κ) (k : ℕ) (hk : k < κ) :
    (∑ ζ ∈ rootSpectrum κ, ζ ^ (-(k : ℤ))) = if k = 0 then (κ : ℂ) else 0 := by
  classical
  let : NeZero κ := ⟨Nat.ne_of_gt hκ⟩
  let α : ℂ := Complex.exp (2 * Real.pi * Complex.I / κ)
  have hα : IsPrimitiveRoot α κ := Complex.isPrimitiveRoot_exp κ (Nat.ne_of_gt hκ)
  by_cases hk0 : k = 0
  · simp [hk0, rootSpectrum, hα.card_nthRootsFinset]
  rw [ite_eq_right hk0]
  have hspectrum : rootSpectrum κ = (Finset.range κ).image (fun j => α ^ j) := by
    ext ζ
    rw [rootSpectrum, Polynomial.mem_nthRootsFinset hκ, Finset.mem_image]
    constructor
    · intro hζ
      obtain ⟨j, hj, hjζ⟩ := hα.eq_pow_of_pow_eq_one hζ
      exact ⟨j, Finset.mem_range.mpr hj, hjζ⟩
    · rintro ⟨j, hj, rfl⟩
      rw [← pow_mul, Nat.mul_comm, pow_mul, hα.pow_eq_one, one_pow]
  rw [hspectrum, Finset.sum_image (fun a ha b hb hab =>
    hα.pow_inj (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hab)]
  have hcomm (j : ℕ) : (α ^ j) ^ (-(k : ℤ)) = (α ^ (-(k : ℤ))) ^ j := by
    rw [← zpow_natCast α j, ← zpow_mul, Int.mul_comm, zpow_mul, zpow_natCast]
  simp_rw [hcomm]
  have hpower : (α ^ (-(k : ℤ))) ^ κ = 1 := by
    rw [← zpow_natCast, ← zpow_mul, Int.mul_comm, zpow_mul, zpow_natCast,
      hα.pow_eq_one, one_zpow]
  have hne : α ^ (-(k : ℤ)) ≠ 1 := by
    rw [zpow_neg, zpow_natCast]
    intro hh
    apply hα.pow_ne_one_of_pos_of_lt hk0 hk
    simpa using congrArg (fun c : ℂ => c⁻¹) hh
  have hh := mul_geom_sum (α ^ (-(k : ℤ))) κ
  rw [hpower, sub_self] at hh
  exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hne)

/-- Lemma 2.0(1), completeness over all κ-th roots, with no multiplicities. -/
theorem spectral_projection_complete (v : ℤ × ℤ) (κ : ℕ)
    (hκ : 0 < κ) (d : (ℤ × ℤ) → ℂ)
    (hd : ∀ z, d (z + (κ : ℤ) • v) = d z) :
    ∑ ζ ∈ rootSpectrum κ, spectralProjection v κ ζ d = d := by
  classical
  funext z
  simp only [Finset.sum_apply, spectralProjection]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  have hs (k : ℕ) (hk : k ∈ Finset.range κ) := spectrum_sum κ hκ k (Finset.mem_range.mp hk)
  rw [Finset.sum_congr rfl (fun (k : ℕ) hk => congrArg (fun c => c * d (z + (k : ℤ) • v)) (hs k hk))]
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_eq_single 0]
  · simp only [ite_true, Nat.cast_zero, zero_smul, add_zero]
    rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hκ)), one_mul]
  · intro k hk hk0
    rw [ite_eq_right hk0]
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr hκ))

/-- Lemma 2.0(2), translation by v acts with eigenvalue ζ. -/
theorem spectral_projection_eigen (v : ℤ × ℤ) (κ : ℕ)
    (hκ : 0 < κ) (ζ : ℂ) (hζ : ζ ^ κ = 1) (d : (ℤ × ℤ) → ℂ)
    (hd : ∀ z, d (z + (κ : ℤ) • v) = d z) :
    (fun z => spectralProjection v κ ζ d (z + v)) =
      (fun z => ζ * spectralProjection v κ ζ d z) := by
  funext z
  exact projection_step v κ hκ ζ hζ d hd z

/-- Lemma 2.0(3), commutation with arbitrary translations. -/
theorem spectral_projection_translate (v : ℤ × ℤ) (κ : ℕ) (ζ : ℂ)
    (d : (ℤ × ℤ) → ℂ) (q : ℤ × ℤ) :
    spectralProjection v κ ζ (fun z => d (z + q)) =
      (fun z => spectralProjection v κ ζ d (z + q)) := by
  funext z
  simp [spectralProjection, add_assoc, add_comm]

/-- Occurrence equals a nonzero row Fourier coefficient when v,u is an integral basis. -/
theorem spectral_occurs_iff_row (v u : ℤ × ℤ) (κ : ℕ)
    (hbasis : v.1 * u.2 - v.2 * u.1 = 1) (hκ : 0 < κ)
    (ζ : ℂ) (hζ : ζ ^ κ = 1) (d : (ℤ × ℤ) → ℂ)
    (hd : ∀ z, d (z + (κ : ℤ) • v) = d z) :
    spectralOccurs v κ ζ d ↔
      ∃ t : ℤ, spectralRowCoefficient v u κ ζ d t ≠ 0 := by
  classical
  constructor
  · intro h
    by_contra hn
    push Not at hn
    apply h
    funext z
    let s : ℤ := z.1 * u.2 - z.2 * u.1
    let t : ℤ := v.1 * z.2 - v.2 * z.1
    have hz : z = s • v + t • u := by
      ext <;> simp [s, t]
      · linear_combination -z.1 * hbasis
      · linear_combination -z.2 * hbasis
    rw [hz, spectral_projection_row_formula v u κ hκ ζ hζ d hd s t, hn t]
    simp
  · rintro ⟨t, ht⟩ he
    have hh := congrFun he (t • u)
    have hf := spectral_projection_row_formula v u κ hκ ζ hζ d hd 0 t
    simp only [zero_smul, zero_add, zpow_zero, one_mul] at hf
    apply ht
    exact hf.symm.trans hh

end
end ConvexNivat
