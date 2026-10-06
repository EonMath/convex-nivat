import ConvexNivat.Colle.ExternalDynamics

namespace ConvexNivat.Colle

/-- Colle Lemma 2.8 and the annihilator-factor producer imply that each
one-sided nonexpansive normal is a positive multiple of an actual primitive
rational left normal. This is the rational-to-real direction bridge. -/
theorem annihilator_nonexpansive_rational (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (hann : HasNontrivialIntegerAnnihilator ξ) (n : RealPlane)
    (hn : OneSidedNonexpansive ξ n) :
    ∃ v : Lattice, Primitive v ∧ ∃ t : ℝ, 0 < t ∧ n = t • normal v := by
  classical
  have horth : ∃ h : Lattice, h ≠ 0 ∧ realDot (embed h) n = 0 := by
    by_cases hp : Periodic ξ
    · obtain ⟨h, hh, hp⟩ := hp
      exact ⟨h, hh, oneSidedNonexpansive_period_tangent ξ n hn h hp⟩
    · obtain ⟨m, _, D, _, hpair⟩ := annihilator_minimal_decomposition ξ A hA hann hp
      obtain ⟨i, hi⟩ := colle_2_8_nonexpansive ξ A hA m D.period
        D.period_nonzero hpair (decomposition_differenceFactors_annihilate ξ m D) n hn
      exact ⟨D.period i, D.period_nonzero i, hi⟩
  obtain ⟨h, hh, horth⟩ := horth
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
  have hd : realDot (embed v) n = 0 := by
    have hf : realDot (embed h) n = (Int.gcd h.1 h.2 : ℝ) * realDot (embed v) n := by
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
  have hscale : ∃ t : ℝ, t ≠ 0 ∧ n = t • normal v := by
    by_cases ha0 : (v.1 : ℝ) = 0
    · have hb0 : (v.2 : ℝ) ≠ 0 := by
        intro hb0
        apply hvne
        apply Prod.ext <;> dsimp <;> first | exact_mod_cast ha0 | exact_mod_cast hb0
      have hn2 : n.2 = 0 := by
        dsimp [realDot, embed] at hd
        rw [ha0, zero_mul, zero_add] at hd
        exact (mul_eq_zero.mp hd).resolve_left hb0
      have heq : n = (-(n.1 / (v.2 : ℝ))) • normal v := by
        apply Prod.ext
        · dsimp [normal]
          field_simp
        · dsimp [normal]
          rw [ha0, mul_zero, hn2]
      refine ⟨-(n.1 / (v.2 : ℝ)), ?_, heq⟩
      intro ht
      exact hn.1 (by simpa only [ht, zero_smul] using heq)
    · have heq : n = (n.2 / (v.1 : ℝ)) • normal v := by
        apply Prod.ext
        · dsimp [normal]
          dsimp [realDot, embed] at hd
          field_simp
          nlinarith [hd]
        · dsimp [normal]
          field_simp
      refine ⟨n.2 / (v.1 : ℝ), ?_, heq⟩
      intro ht
      exact hn.1 (by simpa only [ht, zero_smul] using heq)
  obtain ⟨t, ht, heq⟩ := hscale
  rcases lt_or_gt_of_ne ht with ht | ht
  · refine ⟨-v, ?_, -t, neg_pos.mpr ht, ?_⟩
    · simpa [Primitive] using hv
    · rw [heq]
      ext <;> simp [normal]
  · exact ⟨v, hv, t, ht, heq⟩

/-- Kari–Moutot primary Theorem 3 plus the open/closed and rational/real
bridges: non-determination occurs in both orientations or neither. -/
theorem kariMoutot_no_one_sided_determinism (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (hann : HasNontrivialIntegerAnnihilator ξ) :
    ∃ x ∈ OrbitClosure ξ, ∀ n : RealPlane,
      OneSidedNonexpansive x n ↔ OneSidedNonexpansive x (-n) := by
  classical
  obtain ⟨x, hx, hdet⟩ := kariMoutot_primary_theorem3 ξ A hA hann
  have hAx := orbitClosure_alphabet ξ x A hA hx
  have hannx := orbitClosure_nontrivial_annihilator ξ x hx hann
  have hforward : ∀ n : RealPlane, OneSidedNonexpansive x n →
      OneSidedNonexpansive x (-n) := by
    intro n hn
    obtain ⟨v, hv, t, ht, heq⟩ := annihilator_nonexpansive_rational x A hAx hannx n hn
    let u : Lattice := (-v.2, v.1)
    have hu : u ≠ 0 := by
      intro hz
      have h1 := congrArg Prod.fst hz
      have h2 := congrArg Prod.snd hz
      dsimp [u] at h1 h2
      have hvz : v = 0 := Prod.ext h2 (neg_eq_zero.mp h1)
      rw [hvz] at hv
      norm_num [Primitive] at hv
    have hembed : embed u = normal v := by simp [u, embed, normal]
    have hnegembed : embed (-u) = -normal v := by simp [u, embed, normal]
    have hl := strict_determinism_iff_closed_expansive x u hu
    have hr := strict_determinism_iff_closed_expansive x (-u) (neg_ne_zero.mpr hu)
    rw [hembed] at hl
    rw [hnegembed, neg_neg] at hr
    have hpair : OneSidedNonexpansive x (normal v) ↔
        OneSidedNonexpansive x (-normal v) :=
      (not_iff_not.mp (hl.symm.trans ((hdet u hu).trans hr))).symm
    rw [heq, ← smul_neg]
    apply (oneSidedNonexpansive_positive_scale x (-normal v) t ht).mpr
    apply hpair.mp
    apply (oneSidedNonexpansive_positive_scale x (normal v) t ht).mp
    simpa only [heq] using hn
  refine ⟨x, hx, fun n => ⟨hforward n, ?_⟩⟩
  simpa only [neg_neg] using hforward (-n)

/-- Colle Theorem 1.5, p.4302, obtained from pinned Kari–Moutot Theorem 3
and the line/orientation bridge. No conclusion is assumed as a certificate. -/
theorem kariMoutot_paired_orbit_member (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (hann : HasNontrivialIntegerAnnihilator ξ) :
    ∃ x ∈ OrbitClosure ξ, ∀ n : RealPlane,
      NonexpansiveLine x n ↔
        OneSidedNonexpansive x n ∧ OneSidedNonexpansive x (-n) := by
  obtain ⟨x, hx, hpair⟩ := kariMoutot_no_one_sided_determinism ξ A hA hann
  refine ⟨x, hx, fun n => ?_⟩
  rw [nonexpansiveLine_iff_oneSided_or_opposite x A (orbitClosure_alphabet ξ x A hA hx)]
  exact ⟨fun h => h.elim (fun h => ⟨h, (hpair n).mp h⟩)
    (fun h => ⟨(hpair n).mpr h, h⟩), fun h => Or.inl h.1⟩

/-- Colle §3.1 first step: absence of opposite pairs forces the actual
Kari–Moutot orbit member to have a finite orbit and two independent periods. -/
theorem no_opposite_pair_double_orbit_member (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (hann : HasNontrivialIntegerAnnihilator ξ)
    (hno : ∀ n : RealPlane, n ≠ 0 →
      ¬ OneSidedNonexpansive ξ n ∨ ¬ OneSidedNonexpansive ξ (-n)) :
    ∃ x ∈ OrbitClosure ξ, DoublyPeriodic x := by
  classical
  obtain ⟨x, hx, hpair⟩ := kariMoutot_paired_orbit_member ξ A hA hann
  refine ⟨x, hx, ?_⟩
  by_contra hnot
  obtain ⟨n, hn⟩ := not_double_has_nonexpansive_line x A
    (orbitClosure_alphabet ξ x A hA hx) hnot
  obtain ⟨hpos, hneg⟩ := (hpair n).mp hn
  exact (hno n hn.1).elim
    (fun h => h (oneSidedNonexpansive_inheritance ξ x hx n hpos))
    (fun h => h (oneSidedNonexpansive_inheritance ξ x hx (-n) hneg))

end ConvexNivat.Colle
