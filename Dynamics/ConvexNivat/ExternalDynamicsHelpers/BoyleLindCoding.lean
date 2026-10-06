import ConvexNivat.ExternalDynamicsHelpers.BoyleLindDefinitions

namespace ConvexNivat.ExternalDynamicsHelpers
open ConvexNivat.Colle
noncomputable section

/-- The approved nonexpansiveness predicate is the failure of finite-band determination. -/
theorem nonexpansive_iff_no_determining_band (ξ : Configuration ℤ) (n : RealPlane)
    (hn : n ≠ 0) :
    NonexpansiveLine ξ n ↔ ∀ t : ℝ, 0 < t → ¬ BandDetermines ξ n t := by
  classical
  constructor
  · intro h t ht hd
    obtain ⟨x, hx, y, hy, hne, hag⟩ := h.2 t ht
    exact hne (hd x hx y hy hag)
  · intro h
    refine ⟨hn, ?_⟩
    intro t ht
    have hd := h t ht
    unfold BandDetermines at hd
    push_neg at hd
    obtain ⟨x, hx, y, hy, hag, hne⟩ := hd
    exact ⟨x, hx, y, hy, hne, hag⟩

theorem expansive_line_determining_band (ξ : Configuration ℤ) (n : RealPlane)
    (hn : n ≠ 0) (hexp : ¬ NonexpansiveLine ξ n) :
    ∃ t : ℝ, 0 < t ∧ BandDetermines ξ n t := by
  classical
  have h := (nonexpansive_iff_no_determining_band ξ n hn).not.mp hexp
  push_neg at h
  exact h

/-- Definition 3.1's monotonicity. -/
theorem realCodes_mono (ξ : Configuration ℤ) (E E' F F' : Set RealPlane)
    (hcode : RealCodes ξ E F) (hE : E ⊆ E') (hF : F' ⊆ F) :
    RealCodes ξ E' F' := by
  intro a x hx y hy hag z hz
  apply hcode a x hx y hy ?_ z (hF hz)
  intro w hw
  exact hag w (hE hw)

theorem realCodes_trans (ξ : Configuration ℤ) (E F G : Set RealPlane)
    (hEF : RealCodes ξ E F) (hFG : RealCodes ξ F G) :
    RealCodes ξ E G := by
  intro a x hx y hy hag
  exact hFG a x hx y hy (hEF a x hx y hy hag)

theorem realCodes_translate (ξ : Configuration ℤ) (E F : Set RealPlane)
    (hEF : RealCodes ξ E F) (a : RealPlane) :
    RealCodes ξ (realTranslate E a) (realTranslate F a) := by
  intro b x hx y hy hag
  have hab : ∀ H : Set RealPlane,
      realTranslate (realTranslate H a) b = realTranslate H (b + a) := by
    intro H
    ext p
    simp only [realTranslate, Set.mem_setOf_eq, sub_sub]
  rw [hab] at hag ⊢
  exact hEF (b + a) x hx y hy hag

/-- The Minkowski-sum observation in Lemma 3.2's proof. -/
theorem realCodes_minkowski_sum (ξ : Configuration ℤ) (E F G : Set RealPlane)
    (hEF : RealCodes ξ E F) :
    RealCodes ξ (realMinkowskiSum E G) (realMinkowskiSum F G) := by
  intro a x hx y hy hag z hz
  obtain ⟨f, hf, g, hg, hfg⟩ := hz
  have heq : embed z - (a + g) = f := by
    rw [sub_add_eq_sub_sub, hfg]
    abel
  refine hEF (a + g) x hx y hy ?_ z ?_
  · intro w hw
    apply hag w
    refine ⟨embed w - (a + g), hw, g, hg, ?_⟩
    abel
  · change embed z - (a + g) ∈ F
    rw [heq]
    exact hf

theorem realCodes_union_right (ξ : Configuration ℤ) (E : Set RealPlane)
    {ι : Type*} (F : ι → Set RealPlane) (hEF : ∀ i, RealCodes ξ E (F i)) :
    RealCodes ξ E (⋃ i, F i) := by
  intro a x hx y hy hag z hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  exact hEF i a x hx y hy hag z hi

end
end ConvexNivat.ExternalDynamicsHelpers
