import ConvexNivat.ExternalDynamicsHelpers.PeriodicStrip

namespace ConvexNivat.Colle

theorem periodic_not_double_opposite_pair (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (hperiodic : Periodic ξ) (hnotdouble : ¬ DoublyPeriodic ξ) :
    ∃ n : RealPlane, OneSidedNonexpansive ξ n ∧
      OneSidedNonexpansive ξ (-n) := by
  classical
  obtain ⟨h, hh, hp⟩ := hperiodic
  have hg : 0 < Int.gcd h.1 h.2 := by
    apply Nat.pos_of_ne_zero
    intro hz
    obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp hz
    exact hh (Prod.ext hx hy)
  obtain ⟨a, b, hab, ha, hb⟩ := Int.exists_gcd_one hg
  let v : Lattice := (a, b)
  have hv : Primitive v := hab
  have hparallel : det v h = 0 := by
    dsimp [det, v]
    linear_combination a * hb - b * ha
  have hnonexp : ∀ u : Lattice, Primitive u → det u h = 0 →
      OneSidedNonexpansive ξ (normal u) := by
    intro u hu huh
    by_contra hno
    obtain ⟨w, hw, hpw⟩ :=
      ExternalDynamicsHelpers.periodic_expansive_orientation_transverse_period
        ξ A hA u h hu hh huh hp hno
    apply hnotdouble
    refine ⟨h, w, ?_, hp, hpw⟩
    intro hhw
    have hh1 : h.1 * det u w = 0 := by
      dsimp [Nonparallel, det] at *
      linear_combination u.1 * hhw + w.1 * huh
    have hh2 : h.2 * det u w = 0 := by
      dsimp [Nonparallel, det] at *
      linear_combination u.2 * hhw + w.2 * huh
    exact hh (Prod.ext ((mul_eq_zero.mp hh1).resolve_right (ne_of_gt hw))
      ((mul_eq_zero.mp hh2).resolve_right (ne_of_gt hw)))
  refine ⟨normal v, hnonexp v hv hparallel, ?_⟩
  have hvneg : Primitive (-v) := by simpa [Primitive] using hv
  have hparneg : det (-v) h = 0 := by
    dsimp [det] at *
    linear_combination -hparallel
  have hneg := hnonexp (-v) hvneg hparneg
  simpa [normal] using hneg

theorem periodic_nonexpansive_iff_opposite_pair (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A) (hperiodic : Periodic ξ) (n : RealPlane) :
    NonexpansiveLine ξ n ↔
      OneSidedNonexpansive ξ n ∧ OneSidedNonexpansive ξ (-n) := by
  classical
  constructor
  · intro hn
    have hone : ∀ m : RealPlane, NonexpansiveLine ξ m → OneSidedNonexpansive ξ m := by
      intro m hm
      obtain ⟨h, hh, hp⟩ := hperiodic
      have horth := nonexpansiveLine_period_tangent ξ m hm h hp
      have hg : 0 < Int.gcd h.1 h.2 := by
        apply Nat.pos_of_ne_zero
        intro hz
        obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp hz
        exact hh (Prod.ext hx hy)
      obtain ⟨a, b, hab, ha, hb⟩ := Int.exists_gcd_one hg
      let v : Lattice := (a, b)
      have hv : Primitive v := hab
      have hfac : h = (Int.gcd h.1 h.2 : ℤ) • v :=
        Prod.ext (ha.trans (mul_comm _ _)) (hb.trans (mul_comm _ _))
      have hd : realDot (embed v) m = 0 := by
        have hf : realDot (embed h) m = (Int.gcd h.1 h.2 : ℝ) * realDot (embed v) m := by
          have haR : (h.1 : ℝ) = (a : ℝ) * (Int.gcd h.1 h.2 : ℝ) := by exact_mod_cast ha
          have hbR : (h.2 : ℝ) = (b : ℝ) * (Int.gcd h.1 h.2 : ℝ) := by exact_mod_cast hb
          dsimp [realDot, embed, v]
          rw [haR, hbR]
          ring
        rw [hf] at horth
        exact (mul_eq_zero.mp horth).resolve_left (by exact_mod_cast hg.ne')
      have hvne : v ≠ 0 := by
        intro hz
        rw [hz] at hv
        norm_num [Primitive] at hv
      have hscale : ∃ t : ℝ, t ≠ 0 ∧ m = t • normal v := by
        by_cases ha0 : (v.1 : ℝ) = 0
        · have hb0 : (v.2 : ℝ) ≠ 0 := by
            intro hb0
            apply hvne
            apply Prod.ext <;> dsimp <;> first | exact_mod_cast ha0 | exact_mod_cast hb0
          have hn2 : m.2 = 0 := by
            dsimp [realDot, embed] at hd
            rw [ha0, zero_mul, zero_add] at hd
            exact (mul_eq_zero.mp hd).resolve_left hb0
          have heq : m = (-(m.1 / (v.2 : ℝ))) • normal v := by
            apply Prod.ext
            · dsimp [normal]
              field_simp
            · dsimp [normal]
              rw [ha0, mul_zero, hn2]
          refine ⟨-(m.1 / (v.2 : ℝ)), ?_, heq⟩
          intro ht
          exact hm.1 (by simpa only [ht, zero_smul] using heq)
        · have heq : m = (m.2 / (v.1 : ℝ)) • normal v := by
            apply Prod.ext
            · dsimp [normal]
              dsimp [realDot, embed] at hd
              field_simp
              nlinarith [hd]
            · dsimp [normal]
              field_simp
          refine ⟨m.2 / (v.1 : ℝ), ?_, heq⟩
          intro ht
          exact hm.1 (by simpa only [ht, zero_smul] using heq)
      have hparallel : det v h = 0 := by
        dsimp [det, v]
        linear_combination a * hb - b * ha
      obtain ⟨t, ht, heq⟩ := hscale
      have horiented : ∃ u : Lattice, Primitive u ∧ det u h = 0 ∧
          ∃ c : ℝ, 0 < c ∧ m = c • normal u := by
        rcases lt_or_gt_of_ne ht with ht | ht
        · refine ⟨-v, ?_, ?_, -t, neg_pos.mpr ht, ?_⟩
          · simpa [Primitive] using hv
          · dsimp [det] at *
            linear_combination -hparallel
          · rw [heq]
            ext <;> simp [normal]
        · exact ⟨v, hv, hparallel, t, ht, heq⟩
      obtain ⟨u, hu, huh, c, hc, heq⟩ := horiented
      by_contra hno
      have hexp : ¬ OneSidedNonexpansive ξ (normal u) := by
        intro hx
        apply hno
        rw [heq]
        exact (oneSidedNonexpansive_positive_scale ξ (normal u) c hc).mpr hx
      obtain ⟨w, hw, hpw⟩ :=
        ExternalDynamicsHelpers.periodic_expansive_orientation_transverse_period
          ξ A hA u h hu hh huh hp hexp
      have hwzero := nonexpansiveLine_period_tangent ξ m hm w hpw
      have hdot : realDot (embed w) m = c * (det u w : ℝ) := by
        rw [heq]
        dsimp [realDot, embed, normal, det]
        push_cast
        ring
      rw [hdot] at hwzero
      have hdetpos : (0 : ℝ) < (det u w : ℝ) := by exact_mod_cast hw
      exact (ne_of_gt (mul_pos hc hdetpos)) hwzero
    refine ⟨hone n hn, hone (-n) ?_⟩
    refine ⟨neg_ne_zero.mpr hn.1, fun width hw => ?_⟩
    obtain ⟨x, hx, y, hy, hxy, hagree⟩ := hn.2 width hw
    refine ⟨x, hx, y, hy, hxy, ?_⟩
    intro z hz
    apply hagree z
    have hdot : realDot (embed z) (-n) = -realDot (embed z) n := by
      dsimp [realDot]
      ring
    simpa only [Set.mem_ofPred_eq, hdot, abs_neg] using hz
  · intro hpair
    exact oneSidedNonexpansive_implies_band ξ n hpair.1

end ConvexNivat.Colle
