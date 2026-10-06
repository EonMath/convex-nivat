import NivatTrial.BalancedPropagation
import NivatTrial.Divisibility
import NivatTrial.HorizontalCoordinates

/-! Appendix D.1: a sum of two configurations periodic in independent
directions cannot have low finite lattice-convex pattern complexity unless
the sum is periodic. -/

namespace NivatTrial.TwoComponent

open NivatTrial.Dynamics NivatTrial.Periodicity NivatTrial.LatticePolygon
open NivatTrial.BalancedWindows NivatTrial.BalancedPropagation NivatTrial.RowDetermination
open NivatTrial.LatticeCoordinates
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ

def representativeBlock (c : ℕ) (δ : ℤ) : Finset G :=
  (Finset.Ico (0 : ℤ) (c : ℤ)) ×ˢ (Finset.Ico (0 : ℤ) δ)

/-- A finite rectangular block represents a whole strip modulo the first
period. The representative is an actual integer point. -/
theorem strip_representative (c : ℕ) (hc : 0 < c) (h : G) (hh : 0 < h.2)
    (t : ℤ) (z : G) (hz : z ∈ strip (t * h.2) ((t + 1) * h.2 - 1)) :
    ∃ r ∈ representativeBlock c h.2, ∃ m : ℤ,
      z = t • h + r + m • (c • horizontal) := by
  let w := z - t • h
  let r : G := (w.1 % c, w.2)
  let m := w.1 / c
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  have hr : r ∈ representativeBlock c h.2 := by
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ (ne_of_gt hc'), Int.emod_lt_of_pos _ hc'⟩
    · have hlo := hz.1
      have hhi := hz.2
      dsimp [r, w]
      apply Finset.mem_Ico.mpr
      constructor <;> nlinarith
  refine ⟨r, hr, m, ?_⟩
  have hid := Int.emod_add_mul_ediv w.1 (c : ℤ)
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, nsmul_horizontal, step, smul_eq_mul]
    dsimp [r, m] at *
    change z.1 = t * h.1 + w.1 % c + (w.1 / c) * c
    have hw : w.1 = z.1 - t * h.1 := by simp [w, smul_eq_mul]
    nlinarith [hid]
  · simp [r, w, horizontal, smul_eq_mul]

variable {A : Type*} [Fintype A]

theorem pigeonhole_patterns (θ : G → A) (D : Finset G) (k : ℤ) (h : G) :
    ∃ i j : ℕ, i < j ∧ j ≤ patternComplexity θ D ∧
      patternAt θ D ((k + (i : ℤ)) • h) = patternAt θ D ((k + (j : ℤ)) • h) := by
  let N := patternComplexity θ D
  let f : Fin (N + 1) → patternSet θ D := fun i =>
    ⟨patternAt θ D ((k + (i.val : ℤ)) • h), ⟨_, rfl⟩⟩
  have hcard : Fintype.card (patternSet θ D) < Fintype.card (Fin (N + 1)) := by
    simp only [Fintype.card_fin]
    have he : Fintype.card (patternSet θ D) = N := by
      simp [N, patternComplexity, Nat.card_eq_fintype_card]
    omega
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
  by_cases hlt : i.val < j.val
  · exact ⟨i.val, j.val, hlt, by dsimp [N] at j; omega, congrArg Subtype.val heq⟩
  · exact ⟨j.val, i.val, by omega, by dsimp [N] at i; omega,
      (congrArg Subtype.val heq).symm⟩

variable [AddCommGroup A]

theorem strip_agreement_from_block (θ₁ θ₂ : G → A) (c : ℕ) (h : G)
    (hc : 0 < c) (h₁per : IsPeriod θ₁ (c • horizontal))
    (h₂per : IsPeriod θ₂ h) (hh : 0 < h.2) (t d : ℤ)
    (hblock : ∀ r ∈ representativeBlock c h.2,
      (θ₁ + θ₂) (t • h + r + d • h) = (θ₁ + θ₂) (t • h + r)) :
    ∀ z ∈ strip (t * h.2) ((t + 1) * h.2 - 1),
      shift (d • h) (θ₁ + θ₂) z = (θ₁ + θ₂) z := by
  intro z hz
  obtain ⟨r, hr, m, he⟩ := strip_representative c hc h hh t z hz
  have hd := propagate_difference_agreement θ₁ θ₂ (c • horizontal) h h₁per h₂per d m
    (hblock r hr)
  rw [← he] at hd
  simpa [shift, add_comm] using hd

theorem halfplane_period_multiple (θ : G → A) (a : ℤ) (h : G) (hh : 0 ≤ h.2)
    (hp : ∀ z : G, a ≤ z.2 → θ (z + h) = θ z) :
    ∀ m : ℕ, ∀ z : G, a ≤ z.2 → θ (z + m • h) = θ z := by
  intro m
  induction m with
  | zero => intro z _; simp
  | succ m ih =>
    intro z hz
    have hnew := hp (z + m • h) (by
      change a ≤ z.2 + (m : ℤ) * h.2
      have hm := mul_nonneg (Int.natCast_nonneg m) hh
      omega)
    simpa only [add_nsmul, one_nsmul, ← add_assoc] using hnew.trans (ih z hz)

/-- D.1 after the first direction and the chosen balanced orientation have
been normalized. The ambiguity propagation theorem is fully proved. -/
theorem periodic_of_plus_balanced (θ₁ θ₂ : G → A) (c : ℕ) (h : G)
    (hc : 0 < c) (h₁per : IsPeriod θ₁ (c • horizontal))
    (h₂per : IsPeriod θ₂ h) (hh : 0 < h.2)
    (B : Finset G) (hB : PlusBalanced (θ₁ + θ₂) B) : IsPeriodic (θ₁ + θ₂) := by
  by_contra haperiodic
  let L : ℕ := (upper B - lower B + 1).toNat + 1
  let H := L • h
  have hL : 0 < L := by dsimp [L]; omega
  have hH : 0 < H.2 := by
    change 0 < (L : ℤ) * h.2
    exact mul_pos (by exact_mod_cast hL) hh
  have hheight : upper B - lower B ≤ H.2 - 1 := by
    have hb := lower_le_upper hB.nonempty
    have hLe : upper B - lower B + 1 ≤ (L : ℤ) := by dsimp [L]; omega
    change upper B - lower B ≤ (L : ℤ) * h.2 - 1
    have hLp : (0 : ℤ) < L := by exact_mod_cast hL
    nlinarith
  have hHp : IsPeriod θ₂ H := h₂per.nsmul L
  let D := representativeBlock c H.2
  let N := patternComplexity (θ₁ + θ₂) D
  have hHne : H ≠ 0 := fun he => by simpa [he] using hH
  have hfactne : N.factorial • H ≠ 0 :=
    nsmul_lattice_ne_zero hHne (Nat.factorial_pos N)
  obtain ⟨v₀, hv₀⟩ : ∃ z : G,
      (θ₁ + θ₂) (z + N.factorial • H) ≠ (θ₁ + θ₂) z := by
    by_contra hn
    have hp : IsPeriod (θ₁ + θ₂) (N.factorial • H) := by simpa [IsPeriod] using hn
    exact haperiodic ⟨_, hfactne, hp⟩
  let k : ℤ := v₀.2 / H.2 - (N : ℤ)
  have hvheight : (k + (N : ℤ)) * H.2 ≤ v₀.2 := by
    have hid := Int.emod_add_mul_ediv v₀.2 H.2
    have hrem := Int.emod_nonneg v₀.2 (ne_of_gt hH)
    dsimp [k]
    nlinarith
  obtain ⟨i, j, hij, hjN, heq⟩ := pigeonhole_patterns (θ₁ + θ₂) D k H
  let d := j - i
  let t : ℤ := k + i
  have hd : 0 < d := by dsimp [d]; omega
  have hdN : d ≤ N := by dsimp [d, N]; omega
  have hdiv : d ∣ N.factorial := Nat.dvd_factorial hd hdN
  have hblock : ∀ r ∈ representativeBlock c H.2,
      (θ₁ + θ₂) (t • H + r + (d : ℤ) • H) = (θ₁ + θ₂) (t • H + r) := by
    intro r hr
    have he := congrFun heq ⟨r, hr⟩
    have hj : k + (j : ℤ) = t + (d : ℤ) := by dsimp [t, d]; omega
    simp only [patternAt, hj, add_smul] at he
    simpa only [t, add_smul, add_assoc, add_comm, add_left_comm] using he.symm
  have hstrip := strip_agreement_from_block θ₁ θ₂ c H hc h₁per hHp hH t d hblock
  have hhalf := halfplane_eq_of_strip θ₁ θ₂ c H hc h₁per hHp hH B hB haperiodic
    (t * H.2) ((t + 1) * H.2 - 1) (by nlinarith [hheight])
    (shift_mem_languageHull (self_mem_languageHull (θ₁ + θ₂)) ((d : ℤ) • H)) hstrip
  have hperiod : ∀ z : G, t * H.2 ≤ z.2 →
      (θ₁ + θ₂) (z + d • H) = (θ₁ + θ₂) z := by
    intro z hz
    have hp := hhalf z hz
    simpa [shift, add_comm] using hp
  obtain ⟨m, hm⟩ := hdiv
  have hvstrip : t * H.2 ≤ v₀.2 := by
    have hiN : (i : ℤ) ≤ N := by exact_mod_cast hij.le.trans hjN
    dsimp [t]
    nlinarith [hvheight]
  have hmultiple := halfplane_period_multiple (θ₁ + θ₂) (t * H.2) (d • H)
    (by change 0 ≤ (d : ℤ) * H.2; positivity) hperiod m v₀ hvstrip
  apply hv₀
  rw [← mul_smul, mul_comm m d, ← hm] at hmultiple
  exact hmultiple

theorem periodic_of_comp (e : G ≃+ G) (θ : G → A) (hp : IsPeriodic (θ ∘ e)) :
    IsPeriodic θ := by
  obtain ⟨h, hne, hper⟩ := hp
  refine ⟨e h, ?_, (isPeriod_comp_iff e θ h).mp hper⟩
  intro hz
  apply hne
  apply e.injective
  simpa using hz

theorem periodic_of_plus_balanced_transverse (θ₁ θ₂ : G → A) (c : ℕ) (h : G)
    (hc : 0 < c) (h₁per : IsPeriod θ₁ (c • horizontal))
    (h₂per : IsPeriod θ₂ h) (hh : h.2 ≠ 0)
    (B : Finset G) (hB : PlusBalanced (θ₁ + θ₂) B) : IsPeriodic (θ₁ + θ₂) := by
  by_cases hpos : 0 < h.2
  · exact periodic_of_plus_balanced θ₁ θ₂ c h hc h₁per h₂per hpos B hB
  · exact periodic_of_plus_balanced θ₁ θ₂ c (-h) hc h₁per h₂per.neg
      (by change 0 < -h.2; omega) B hB

/-- Both balanced orientations are actually obtained from the low-complexity
convex window; the reflected case is transported back to the same field. -/
theorem horizontal_low_complexity (θ₁ θ₂ : G → A) (c : ℕ) (h : G)
    (hc : 0 < c) (h₁per : IsPeriod θ₁ (c • horizontal))
    (h₂per : IsPeriod θ₂ h) (hh : h.2 ≠ 0)
    (S : Finset G) (hne : S.Nonempty) (hS : IsLatticeConvex S)
    (hlow : patternComplexity (θ₁ + θ₂) S ≤ S.card) : IsPeriodic (θ₁ + θ₂) := by
  obtain ⟨B, _, hplus | hminus⟩ := exists_balanced_subset (θ₁ + θ₂) S hne hS hlow
  · exact periodic_of_plus_balanced_transverse θ₁ θ₂ c h hc h₁per h₂per hh B hplus
  · have h₁reflect : IsPeriod (θ₁ ∘ reflectY) (c • horizontal) := by
      apply (isPeriod_comp_iff reflectY θ₁ _).mpr
      simpa [map_nsmul, horizontal] using h₁per
    have h₂reflect : IsPeriod (θ₂ ∘ reflectY) (reflectY h) := by
      apply (isPeriod_comp_iff reflectY θ₂ _).mpr
      simpa using h₂per
    have hhreflect : (reflectY h).2 ≠ 0 := by simpa using hh
    have hp := periodic_of_plus_balanced_transverse (θ₁ ∘ reflectY) (θ₂ ∘ reflectY)
      c (reflectY h) hc h₁reflect h₂reflect hhreflect
      (mapWindow reflectY B) hminus.reflect
    exact periodic_of_comp reflectY (θ₁ + θ₂) hp

/-- **Theorem D.1.** Actual independent periods and actual low convex pattern
complexity force a nonzero period of the sum. No propagation, balanced-set,
primitive-coordinate, or finite-state premise is retained. -/
theorem periodic_of_low_convex_complexity (θ₁ θ₂ : G → A) (h₁ h₂ : G)
    (h₁per : IsPeriod θ₁ h₁) (h₂per : IsPeriod θ₂ h₂)
    (hindependent : Geometry.det h₁ h₂ ≠ 0)
    (S : Finset G) (hne : S.Nonempty) (hS : IsLatticeConvex S)
    (hlow : patternComplexity (θ₁ + θ₂) S ≤ S.card) : IsPeriodic (θ₁ + θ₂) := by
  obtain ⟨c, e, hc, hfirst, hsecond⟩ :=
    HorizontalCoordinates.exists_horizontal_coordinates h₁ h₂ hindependent
  have hp₁ : IsPeriod (θ₁ ∘ e) (c • horizontal) :=
    (isPeriod_comp_iff e θ₁ _).mpr (by simpa only [hfirst] using h₁per)
  have hp₂ : IsPeriod (θ₂ ∘ e) (e.symm h₂) :=
    (isPeriod_comp_iff e θ₂ _).mpr (by simpa using h₂per)
  let T := mapWindow e.symm S
  have hTne : T.Nonempty := mapWindow_nonempty e.symm hne
  have hTconvex : IsLatticeConvex T := isLatticeConvex_mapWindow e.symm hS
  have hcomplexity : patternComplexity ((θ₁ + θ₂) ∘ e) T = patternComplexity (θ₁ + θ₂) S := by
    dsimp [T]
    rw [patternComplexity_mapWindow]
    have he : ((θ₁ + θ₂) ∘ e) ∘ e.symm = θ₁ + θ₂ := by
      funext z
      simp
    rw [he]
  have hlow' : patternComplexity ((θ₁ ∘ e) + (θ₂ ∘ e)) T ≤ T.card := by
    change patternComplexity ((θ₁ + θ₂) ∘ e) T ≤ T.card
    rw [hcomplexity]
    simpa [T] using hlow
  exact periodic_of_comp e (θ₁ + θ₂)
    (horizontal_low_complexity (θ₁ ∘ e) (θ₂ ∘ e) c (e.symm h₂)
      hc hp₁ hp₂ hsecond T hTne hTconvex hlow')

theorem aperiodic_complexity_lower_bound (θ₁ θ₂ : G → A) (h₁ h₂ : G)
    (h₁per : IsPeriod θ₁ h₁) (h₂per : IsPeriod θ₂ h₂)
    (hindependent : Geometry.det h₁ h₂ ≠ 0) (haperiodic : ¬IsPeriodic (θ₁ + θ₂))
    (S : Finset G) (hne : S.Nonempty) (hS : IsLatticeConvex S) :
    S.card + 1 ≤ patternComplexity (θ₁ + θ₂) S := by
  by_contra hn
  exact haperiodic (periodic_of_low_convex_complexity θ₁ θ₂ h₁ h₂ h₁per h₂per
    hindependent S hne hS (by omega))

end

end NivatTrial.TwoComponent
