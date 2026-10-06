import ConvexNivat.Colle.GeneratingPatterns

namespace ConvexNivat.Colle
open scoped BigOperators

/-- Colle Lemma 2.4 (Cyr–Kra): the actual singleton supporting vertex is
generated, so the oriented half-plane determines every orbit member. -/
theorem colle_2_4 (ξ : Configuration ℤ) (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (S : Finset Lattice) (hconvex : LatticeConvex S) (n : RealPlane) (hn : n ≠ 0)
    (z : Lattice) (hface : supportFace S n = {z})
    (hgenerated : PatternDetermines ξ (S.erase z) z) :
    ¬ OneSidedNonexpansive ξ n := by
  classical
  rintro ⟨_, x, hx, y, hy, hxy, hagree⟩
  let H : Lattice → ℝ := fun w => realDot (embed w) n
  have hadd (a b : Lattice) : H (a + b) = H a + H b := by
    dsimp [H, realDot, embed]
    push_cast
    ring
  have hsub (a b : Lattice) : H (a - b) = H a - H b := by
    dsimp [H, realDot, embed]
    push_cast
    ring
  have hz : z ∈ supportFace S n := by rw [hface]; simp
  have hmin : ∀ q ∈ S, H z ≤ H q := (Finset.mem_filter.mp hz).2
  have hstrict : ∀ q ∈ S.erase z, 0 < H q - H z := by
    intro q hq
    have hqS := (Finset.mem_erase.mp hq).2
    have hqz := (Finset.mem_erase.mp hq).1
    apply sub_pos.mpr
    apply lt_of_le_of_ne (hmin q hqS)
    intro he
    have hqface : q ∈ supportFace S n := by
      apply Finset.mem_filter.mpr
      refine ⟨hqS, ?_⟩
      intro r hr
      change H q ≤ H r
      rw [← he]
      exact hmin r hr
    rw [hface] at hqface
    exact hqz (Finset.mem_singleton.mp hqface)
  by_cases hT : (S.erase z).Nonempty
  · let δ : ℝ := (S.erase z).inf' hT (fun q => H q - H z)
    have hδ : 0 < δ := (Finset.lt_inf'_iff hT).mpr hstrict
    have hδq : ∀ q ∈ S.erase z, δ ≤ H q - H z := by
      intro q hq
      exact Finset.inf'_le _ hq
    let B : Set ℝ := {r | ∃ w : Lattice, x w ≠ y w ∧ r = H w}
    have hB : B.Nonempty := by
      obtain ⟨w, hw⟩ : ∃ w, x w ≠ y w := by
        by_contra h
        push Not at h
        exact hxy (funext h)
      exact ⟨H w, w, hw, rfl⟩
    have hBbound : BddAbove B := by
      refine ⟨0, ?_⟩
      rintro r ⟨w, hw, rfl⟩
      apply le_of_not_ge
      intro hnonneg
      exact hw (hagree w hnonneg)
    obtain ⟨r, ⟨w, hw, hr⟩, hnear⟩ :=
      exists_lt_of_lt_csSup hB (show sSup B - δ < sSup B by linarith)
    subst r
    have he : ∀ q ∈ S.erase z, x (q + (w - z)) = y (q + (w - z)) := by
      intro q hq
      by_contra hbad
      have hb : H (q + (w - z)) ∈ B := ⟨q + (w - z), hbad, rfl⟩
      have hupper := le_csSup hBbound hb
      have hgap := hδq q hq
      rw [hadd, hsub] at hupper
      linarith
    have hletter := hgenerated x hx y hy (w - z) he
    have heq : z + (w - z) = w := by abel
    rw [heq] at hletter
    exact hw hletter
  · apply hxy
    funext w
    have hletter := hgenerated x hx y hy (w - z) (by
      intro q hq
      exact (hT ⟨q, hq⟩).elim)
    have heq : z + (w - z) = w := by abel
    simpa only [heq] using hletter

end ConvexNivat.Colle
