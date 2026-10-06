import ConvexNivat.Colle.Orbit

namespace ConvexNivat.Colle

theorem strict_determinism_iff_closed_expansive (ξ : Configuration ℤ)
    (u : Lattice) (hu : u ≠ 0) :
    StrictDeterministic ξ u ↔ ¬ OneSidedNonexpansive ξ (-embed u) := by
  classical
  have huR : embed u ≠ 0 := by
    intro h
    apply hu
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    apply Prod.ext <;> dsimp [embed] at * <;> first | exact_mod_cast h1 | exact_mod_cast h2
  have hneg : -embed u ≠ 0 := neg_ne_zero.mpr huR
  have hnorm : 0 < (u.1 : ℝ) ^ 2 + (u.2 : ℝ) ^ 2 := by
    rcases ne_or_eq (u.1 : ℝ) 0 with h1 | h1
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h1) (sq_nonneg _)
    · have h2 : (u.2 : ℝ) ≠ 0 := by
        intro h2
        apply huR
        exact Prod.ext h1 h2
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h2)
  constructor
  · intro hdet hnon
    obtain ⟨_, x, hx, y, hy, hxy, hagree⟩ := hnon
    apply hxy
    apply hdet x hx y hy
    intro z hz
    apply hagree z
    dsimp [realDot] at *
    simp only [mul_neg]
    linarith
  · intro hnon x hx y hy hagree
    have hshift : translate (-u) x = translate (-u) y := by
      by_contra hne
      apply hnon
      refine ⟨hneg, translate (-u) x, orbitClosure_translate_member ξ x hx (-u),
        translate (-u) y, orbitClosure_translate_member ξ y hy (-u), hne, ?_⟩
      intro z hz
      apply hagree (z + -u)
      dsimp [realDot, embed] at hz ⊢
      push_cast
      nlinarith
    funext z
    have heq := congrFun hshift (z + u)
    simpa [translate, add_assoc] using heq

theorem uniformly_recurrent_orbit_member (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A) :
    ∃ x ∈ OrbitClosure ξ, UniformlyRecurrent x := by
  classical
  let X := OrbitClosure ξ
  let F : Set (Set (Configuration ℤ)) :=
    {Y | Y ⊆ X ∧ IsClosed Y ∧ Y.Nonempty ∧ ∀ x ∈ Y, OrbitClosure x ⊆ Y}
  have hclosed (x : Configuration ℤ) : IsClosed (OrbitClosure x) := by
    rw [orbitClosure_eq_topological_closure]
    exact isClosed_closure
  have hX : X ∈ F :=
    ⟨Set.Subset.rfl, hclosed ξ, ⟨ξ, orbitClosure_contains_self ξ⟩,
      fun x hx => orbitClosure_transitive ξ x hx⟩
  have hbound : ∀ c ⊆ F, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ lb ∈ F, ∀ s ∈ c, lb ⊆ s := by
    intro c hc hchain hcne
    have : Nonempty c := hcne.to_subtype
    have hinter : (⋂₀ c).Nonempty :=
      IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        (fun U hU V hV => by
          rcases hchain.total hU hV with h | h
          · exact ⟨U, hU, Set.Subset.rfl, h⟩
          · exact ⟨V, hV, h, Set.Subset.rfl⟩)
        (fun U hU => (hc hU).2.2.1)
        (fun U hU => (orbitClosure_isCompact ξ A hA).of_isClosed_subset
          (hc hU).2.1 (hc hU).1)
        (fun U hU => (hc hU).2.1)
    refine ⟨⋂₀ c, ⟨?_, ?_, hinter, ?_⟩, ?_⟩
    · obtain ⟨U, hU⟩ := hcne
      exact (Set.sInter_subset_of_mem hU).trans (hc hU).1
    · exact isClosed_sInter (fun U hU => (hc hU).2.1)
    · intro x hx z hz
      exact Set.mem_sInter.mpr (fun U hU => (hc hU).2.2.2 x
        (Set.mem_sInter.mp hx U hU) hz)
    · exact fun U hU => Set.sInter_subset_of_mem hU

  obtain ⟨Y, hYX, hY⟩ := zorn_superset_nonempty F hbound X hX
  obtain ⟨x, hx⟩ := hY.1.2.2.1
  have hclosure (y : Configuration ℤ) (hy : y ∈ Y) : OrbitClosure y = Y := by
    have hyX : y ∈ X := hY.1.1 hy
    have hsub : OrbitClosure y ⊆ Y := hY.1.2.2.2 y hy
    apply Set.Subset.antisymm hsub
    apply hY.2
    · refine ⟨hsub.trans hY.1.1, hclosed y, ⟨y, orbitClosure_contains_self y⟩, ?_⟩
      exact fun z hz => orbitClosure_transitive y z hz
    · exact hsub
  refine ⟨x, hYX hx, ?_⟩
  intro y hy
  exact (hclosure y ((hclosure x hx) ▸ hy)).trans (hclosure x hx).symm

theorem nonexpansiveLine_iff_oneSided_or_opposite (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A) (n : RealPlane) :
    NonexpansiveLine ξ n ↔
      OneSidedNonexpansive ξ n ∨ OneSidedNonexpansive ξ (-n) := by
  classical
  constructor
  · intro hn
    by_contra hpair
    push Not at hpair
    have hcompact := orbitClosure_isCompact ξ A hA
    have hcode : ∀ (m : RealPlane), m ≠ 0 → ¬ OneSidedNonexpansive ξ m →
        ∀ q : Lattice, ∃ S : Finset Lattice,
          (∀ z ∈ S, 0 ≤ realDot (embed z) m) ∧
          ∀ x ∈ OrbitClosure ξ, ∀ y ∈ OrbitClosure ξ,
            AgreesOn x y (S : Set Lattice) → x q = y q := by
      intro m hm hno q
      let K : Set (Configuration ℤ × Configuration ℤ) :=
        (OrbitClosure ξ ×ˢ OrbitClosure ξ) ∩ {p | p.1 q ≠ p.2 q}
      have heval : Continuous (fun p : Configuration ℤ × Configuration ℤ =>
          (p.1 q, p.2 q)) := by fun_prop
      have hK : IsCompact K := (hcompact.prod hcompact).inter_right <|
        (isClosed_discrete {p : ℤ × ℤ | p.1 ≠ p.2}).preimage heval
      let H := {z : Lattice // 0 ≤ realDot (embed z) m}
      let U : H → Set (Configuration ℤ × Configuration ℤ) :=
        fun z => {p | p.1 z ≠ p.2 z}
      have hU : ∀ z, IsOpen (U z) := by
        intro z
        exact isOpen_ne_fun (by fun_prop) (by fun_prop)
      have hcover : K ⊆ ⋃ z, U z := by
        intro p hp
        apply Set.mem_iUnion.mpr
        by_contra h
        push Not at h
        apply hno
        refine ⟨hm, p.1, hp.1.1, p.2, hp.1.2, ?_, ?_⟩
        · exact fun heq => hp.2 (congrFun heq q)
        · intro z hz
          exact not_ne_iff.mp (h ⟨z, hz⟩)
      obtain ⟨T, hT⟩ := hK.elim_finite_subcover U hU hcover
      refine ⟨T.image Subtype.val, ?_, ?_⟩
      · intro z hz
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
        exact w.property
      · intro x hx y hy hagree
        by_contra hne
        have hxyK : (x, y) ∈ K := ⟨⟨hx, hy⟩, hne⟩
        obtain ⟨z, hz, hdiff⟩ := Set.mem_iUnion₂.mp (hT hxyK)
        exact hdiff (hagree z (Finset.mem_image.mpr ⟨z, hz, rfl⟩))
    have hinward : ∃ v : Lattice, 0 < realDot (embed v) n := by
      rcases lt_trichotomy n.1 0 with h | h | h
      · exact ⟨(-1, 0), by simpa [realDot, embed] using neg_pos.mpr h⟩
      · have hn2 : n.2 ≠ 0 := by
          intro hn2
          exact hn.1 (Prod.ext h hn2)
        rcases lt_or_gt_of_ne hn2 with h2 | h2
        · exact ⟨(0, -1), by simpa [realDot, embed] using neg_pos.mpr h2⟩
        · exact ⟨(0, 1), by simpa [realDot, embed] using h2⟩
      · exact ⟨(1, 0), by simpa [realDot, embed] using h⟩
    obtain ⟨v, hv⟩ := hinward
    obtain ⟨Spos, hSpos, hpos⟩ := hcode n hn.1 hpair.1 (-v)
    obtain ⟨Sneg, hSneg, hneg⟩ := hcode (-n) (neg_ne_zero.mpr hn.1) hpair.2 v
    let d := realDot (embed v) n
    let f : Lattice → ℝ := fun z => realDot (embed z) n
    have hfadd (a b : Lattice) : f (a + b) = f a + f b := by
      dsimp [f, realDot, embed]
      push_cast
      ring
    have hfneg (a : Lattice) : f (-a) = -f a := by
      dsimp [f, realDot, embed]
      push_cast
      ring
    let Bpos := ∑ z ∈ Spos, |f z|
    let Bneg := ∑ z ∈ Sneg, |f z|
    have hBp : 0 ≤ Bpos := Finset.sum_nonneg (fun z hz => abs_nonneg _)
    have hBn : 0 ≤ Bneg := Finset.sum_nonneg (fun z hz => abs_nonneg _)
    let W := Bpos + Bneg + d + 1
    have hd : 0 < d := hv
    have hW : 0 < W := by dsimp [W]; linarith
    have hpbound : ∀ z ∈ Spos, 0 ≤ f z ∧ f z ≤ W := by
      intro z hz
      have hzsum : |f z| ≤ Bpos := Finset.single_le_sum
        (fun a ha => abs_nonneg (f a)) hz
      exact ⟨hSpos z hz, by dsimp [W]; linarith [le_abs_self (f z)]⟩
    have hnbound : ∀ z ∈ Sneg, -W ≤ f z ∧ f z ≤ 0 := by
      intro z hz
      have hzsum : |f z| ≤ Bneg := Finset.single_le_sum
        (fun a ha => abs_nonneg (f a)) hz
      have hzneg : f z ≤ 0 := by
        have hh := hSneg z hz
        dsimp [f, realDot] at hh ⊢
        simp only [mul_neg] at hh
        linarith
      exact ⟨by dsimp [W]; linarith [neg_le_abs (f z)], hzneg⟩
    obtain ⟨x, hx, y, hy, hxy, hagree⟩ := hn.2 W hW
    apply hxy
    have hband : ∀ k : ℕ, ∀ z : Lattice, |f z| ≤ W + (k : ℝ) * d → x z = y z := by
      intro k
      induction k with
      | zero =>
        intro z hz
        exact hagree z (by simpa only [Nat.cast_zero, zero_mul, add_zero, Set.mem_ofPred_eq, f] using hz)
      | succ k ih =>
        intro z hz
        by_cases hprev : |f z| ≤ W + (k : ℝ) * d
        · exact ih z hprev
        have hk : 0 ≤ (k : ℝ) * d := mul_nonneg (Nat.cast_nonneg _) hd.le
        have hzupper := (abs_le.mp hz).2
        have hzlower := (abs_le.mp hz).1
        push_cast at hzupper hzlower
        rcases le_or_gt (f z) 0 with hzneg | hzpos
        · have hzstrict : f z < -(W + (k : ℝ) * d) := by
            rw [abs_of_nonpos hzneg] at hprev
            linarith
          have heq := hpos (translate (z + v) x)
            (orbitClosure_translate_member ξ x hx (z + v)) (translate (z + v) y)
            (orbitClosure_translate_member ξ y hy (z + v)) (by
              intro a ha
              apply ih (a + (z + v))
              rw [hfadd, hfadd]
              obtain ⟨ha0, haW⟩ := hpbound a ha
              change |f a + (f z + d)| ≤ W + (k : ℝ) * d
              apply abs_le.mpr
              constructor <;> nlinarith)
          simpa [translate, add_comm, add_left_comm, add_assoc] using heq
        · have hzstrict : W + (k : ℝ) * d < f z := by
            rw [abs_of_pos hzpos] at hprev
            linarith
          have heq := hneg (translate (z + -v) x)
            (orbitClosure_translate_member ξ x hx (z + -v)) (translate (z + -v) y)
            (orbitClosure_translate_member ξ y hy (z + -v)) (by
              intro a ha
              apply ih (a + (z + -v))
              rw [hfadd, hfadd, hfneg]
              obtain ⟨haW, ha0⟩ := hnbound a ha
              change |f a + (f z + -d)| ≤ W + (k : ℝ) * d
              apply abs_le.mpr
              constructor <;> nlinarith)
          simpa [translate, add_comm, add_left_comm, add_assoc] using heq
    funext z
    obtain ⟨k, hk⟩ := exists_nat_gt (|f z| / d)
    apply hband k z
    have hprod := (div_lt_iff₀ hd).mp hk
    linarith
  · intro h
    rcases h with h | h
    · exact oneSidedNonexpansive_implies_band ξ n h
    · obtain ⟨hne, hband⟩ := oneSidedNonexpansive_implies_band ξ (-n) h
      refine ⟨fun hz => hne (by simp [hz]), fun W hW => ?_⟩
      obtain ⟨x, hx, y, hy, hxy, hagree⟩ := hband W hW
      refine ⟨x, hx, y, hy, hxy, ?_⟩
      intro z hz
      apply hagree z
      have hdot : realDot (embed z) (-n) = -realDot (embed z) n := by
        dsimp [realDot]
        ring
      simpa only [Set.mem_ofPred_eq, hdot, abs_neg] using hz

end ConvexNivat.Colle
