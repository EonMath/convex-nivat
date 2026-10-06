import ConvexNivat.AvailableDirections
import ConvexNivat.TwoComponentLimits
import ConvexNivat.Propagation
import ConvexNivat.RegionExtension

namespace ConvexNivat
open scoped BigOperators

/-- 8.12 second half-plane, stated for exactly the output of 8.10. -/
theorem theorem8_12 (p : ℕ) (hp : p.Prime) (θ : Configuration (ZMod p))
    (D : FirstHalfPlaneData p θ) (haperiodic : ¬ Periodic θ)
    (hlow : LowConvexComplexity θ) :
    ∀ i, ∃ β : ℤ, β < D.threshold i ∧
      FullyPeriodicOn (D.field i) (lowerHalf (D.direction i) β) := by
  classical
  have normalne (i : Fin D.length) :
      ((-((D.direction i).2 : ℝ), ((D.direction i).1 : ℝ)) : ℝ × ℝ) ≠ 0 := by
    intro hz
    have hx := congrArg Prod.fst hz
    have hy := congrArg Prod.snd hz
    have hzero : D.direction i = 0 := by
      apply Prod.ext
      · simp only [Prod.snd_zero] at hy
        change ((D.direction i).1 : ℝ) = 0 at hy
        exact_mod_cast hy
      · change -((D.direction i).2 : ℝ) = 0 at hx
        simp only [neg_eq_zero] at hx
        exact_mod_cast hx
    exact primitive_ne_zero _ (D.primitive i) hzero
  let U (i : Fin D.length) : HalfPlane :=
    ⟨(-(D.direction i).2, (D.direction i).1), normalne i, D.threshold i, false⟩
  have hU (i : Fin D.length) : (U i).carrier = upperHalf (D.direction i) (D.threshold i) := by
    ext z
    simp only [U, HalfPlane.carrier, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq, upperHalf]
    have he : realDot (embed z) (-(D.direction i).2, (D.direction i).1) =
        (det (D.direction i) z : ℝ) := by simp [realDot, embed, det]; ring
    rw [he]
    exact_mod_cast (Iff.rfl : D.threshold i ≤ det (D.direction i) z ↔ D.threshold i ≤ det (D.direction i) z)
  have hupper (i : Fin D.length) : ∃ τ : Configuration (ZMod p),
      DoublyPeriodic τ ∧ AgreesOn (D.field i) τ (upperHalf (D.direction i) (D.threshold i)) := by
    obtain ⟨a, b, hfull⟩ := D.full_upper i
    have hfullH : FullPeriods (D.field i) (U i).carrier a b := by rwa [hU]
    have hN := lemma8_2_eventual_entry (D.field i) (U i).carrier
      (Or.inr ⟨U i, rfl⟩) a b hfullH
    have hentry : ∀ z, ∃ n : ℕ, z + (n : ℤ) • (a + b) ∈ (U i).carrier := by
      intro z
      obtain ⟨n, hn⟩ := hN z
      exact ⟨n, hn n le_rfl⟩
    obtain ⟨hag, hpa, hpb, hlinear, hdouble, hshift⟩ :=
      lemma8_2_extensionAlong (D.field i) (U i).carrier a b hfullH hentry
    refine ⟨extensionAlong (D.field i) (U i).carrier (a + b) hentry, hdouble, ?_⟩
    intro z hz
    exact (hag z (by rwa [hU])).symm
  choose upper upperdouble upperagree using hupper
  let P (i : Fin D.length) : Prop := ∃ β : ℤ, ∃ τ : Configuration (ZMod p),
      β < D.threshold i ∧ DoublyPeriodic τ ∧ AgreesOn (D.field i) τ (lowerHalf (D.direction i) β)
  have hfinish (O : Finset (Fin D.length)) :
      (∀ i, i ∉ O → P i) → ∀ i, P i := by
    refine Finset.strongInductionOn O ?_
    intro O ih hprev
    by_cases hempty : O = ∅
    · subst O
      exact fun i => hprev i (by simp)
    have hO : O.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    let lower (i : Fin D.length) : Configuration (ZMod p) :=
      if hi : i ∉ O then Classical.choose (Classical.choose_spec (hprev i hi)) else 0
    let β (i : Fin D.length) : ℤ :=
      if hi : i ∉ O then Classical.choose (hprev i hi) else 0
    have hlower (i : Fin D.length) (hi : i ∉ O) :
        β i < D.threshold i ∧ DoublyPeriodic (lower i) ∧
          AgreesOn (D.field i) (lower i) (lowerHalf (D.direction i) (β i)) := by
      simpa only [lower, β, dite_eq_left hi] using
        Classical.choose_spec (Classical.choose_spec (hprev i hi))
    have hlowerdouble (i : Fin D.length) : DoublyPeriodic (lower i) := by
      by_cases hi : i ∉ O
      · exact (hlower i hi).2.1
      · have he : lower i = 0 := by simp [lower, hi]
        rw [he]
        exact ⟨(1, 0), (0, 1), by norm_num [Nonparallel, det], by intro z; rfl, by intro z; rfl⟩
    have huppergrid (i : Fin D.length) := (doublyPeriodic_iff_grid (upper i)).mp (upperdouble i)
    have hlowergrid (i : Fin D.length) := (doublyPeriodic_iff_grid (lower i)).mp (hlowerdouble i)
    choose Nu hNu hpu using huppergrid
    choose Nl hNl hpl using hlowergrid
    let f (i : Fin D.length) := D.multiplier i * Nu i * Nl i
    let N := ∏ i : Fin D.length, f i
    have hN : 0 < N := Finset.prod_pos fun i _ =>
      Nat.mul_pos (Nat.mul_pos (D.positive_multiplier i) (hNu i)) (hNl i)
    have hfdiv (i : Fin D.length) : f i ∣ N := Finset.dvd_prod_of_mem f (Finset.mem_univ i)
    have hmultdiv (i : Fin D.length) : D.multiplier i ∣ N :=
      dvd_trans (by dsimp [f]; exact dvd_mul_right _ _ |>.trans (dvd_mul_right _ _)) (hfdiv i)
    have hNudiv (i : Fin D.length) : Nu i ∣ N :=
      dvd_trans (by dsimp [f]; exact dvd_mul_left _ _ |>.trans (dvd_mul_right _ _)) (hfdiv i)
    have hNldiv (i : Fin D.length) : Nl i ∣ N :=
      dvd_trans (by dsimp [f]; exact dvd_mul_left _ _) (hfdiv i)
    have hperiodscale (g : Configuration (ZMod p)) (M : ℕ)
        (hgrid : ∀ z : Lattice, HasPeriod g ((M : ℤ) • z)) (hdiv : M ∣ N) :
        ∀ z : Lattice, HasPeriod g ((N : ℤ) • z) := by
      obtain ⟨q, hq⟩ := hdiv
      intro z
      rw [hq, Nat.cast_mul]
      simpa only [smul_smul, mul_comm] using hasPeriod_zsmul _ _ (hgrid z) (q : ℤ)
    let K : TailInventory D O :=
      { upperTail := upper
        upper_double := upperdouble
        upper_agreement := upperagree
        lowerTail := fun i _ => lower i
        lowerThreshold := fun i _ => β i
        lower_double := fun i hi => (hlower i hi).2.1
        lower_disjoint := fun i hi => (hlower i hi).1
        lower_agreement := fun i hi => (hlower i hi).2.2
        scale := N
        positive_scale := hN
        divisible := hmultdiv
        upper_periods := fun i => hperiodscale _ _ (hpu i) (hNudiv i)
        lower_periods := fun i _ => hperiodscale _ _ (hpl i) (hNldiv i) }
    obtain ⟨b, hb, c, hcb, d, hd, hscale, hfixes, hnegative, hsafe⟩ := lemma8_15 p hp θ D O hO K
    have hlimits : ∀ y, SubsequentialTranslateLimit (D.field b) d y → DoublyPeriodic y := by
      intro y hy
      exact proposition8_14 p hp θ D O K hlow b c hcb.symm d hscale hfixes hnegative hsafe y hy
    obtain ⟨βnew, τ, hτdouble, hag⟩ := lemma8_16 p hp (D.field b) (D.direction b)
      (D.transverse b) (D.primitive b) (D.basis b) (D.multiplier b)
      (D.positive_multiplier b) (D.has_period b) d hnegative hlimits
    have hbnew : P b := by
      refine ⟨min βnew (D.threshold b - 1), τ, ?_, hτdouble, ?_⟩
      · have := min_le_right βnew (D.threshold b - 1); omega
      · intro z hz
        apply hag z
        change det (D.direction b) z ≤ min βnew (D.threshold b - 1) at hz
        exact le_trans hz (min_le_left _ _)
    have hprevnew : ∀ i, i ∉ O.erase b → P i := by
      intro i hi
      by_cases hib : i = b
      · simpa [hib] using hbnew
      · exact hprev i (by simpa [Finset.mem_erase, hib] using hi)
    exact ih (O.erase b) (Finset.erase_ssubset hb) hprevnew
  have hall := hfinish Finset.univ (by intro i hi; exact False.elim (hi (Finset.mem_univ i)))
  intro i
  obtain ⟨β, τ, hβ, hτ, hag⟩ := hall i
  let V : HalfPlane :=
    ⟨((D.direction i).2, -(D.direction i).1), by
      intro hz
      apply normalne i
      have hx := congrArg Prod.fst hz
      have hy := congrArg Prod.snd hz
      apply Prod.ext <;> simp_all,
      -β, false⟩
  have hV : V.carrier = lowerHalf (D.direction i) β := by
    ext z
    simp only [V, HalfPlane.carrier, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq, lowerHalf]
    have he : realDot (embed z) ((D.direction i).2, -(D.direction i).1) =
        -(det (D.direction i) z : ℝ) := by simp [realDot, embed, det]; ring
    rw [he, neg_le_neg_iff]
    exact_mod_cast (Iff.rfl : det (D.direction i) z ≤ β ↔ det (D.direction i) z ≤ β)
  obtain ⟨a, b, hfull⟩ := doublyPeriodic_full_halfPlane τ hτ V
  refine ⟨β, hβ, a, b, ?_⟩
  have hfull' : FullPeriods τ (lowerHalf (D.direction i) β) a b := by rwa [hV] at hfull
  refine ⟨hfull'.1, hfull'.2.1, hfull'.2.2.1, hfull'.2.2.2.1, ?_, ?_⟩
  · intro z hz
    exact (hag _ (hfull'.2.2.1 z hz)).trans ((hfull'.2.2.2.2.1 z hz).trans (hag z hz).symm)
  · intro z hz
    exact (hag _ (hfull'.2.2.2.1 z hz)).trans ((hfull'.2.2.2.2.2 z hz).trans (hag z hz).symm)

end ConvexNivat
