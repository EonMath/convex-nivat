import NivatTrial.Periodicity

/-! Absorption of doubly periodic summands in a finite directional decomposition. -/

namespace NivatTrial.ReducedDecomposition

open NivatTrial.Geometry NivatTrial.Periodicity
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ

variable {A : Type*} [AddCommGroup A]

theorem doublyPeriodic_add {F H : G → A}
    (hF : IsDoublyPeriodic F) (hH : IsDoublyPeriodic H) :
    IsDoublyPeriodic (F + H) := by
  let K : Bool → G → A := fun b => if b then F else H
  have hK : ∀ b, IsDoublyPeriodic (K b) := by
    intro b
    cases b
    · simpa [K] using hH
    · simpa [K] using hF
  obtain ⟨n, hn, hp⟩ := common_rectangular_periods K hK
  have hF₁ : IsPeriod F (n • ((1, 0) : G)) := by simpa [K] using (hp true).1
  have hF₂ : IsPeriod F (n • ((0, 1) : G)) := by simpa [K] using (hp true).2
  have hH₁ : IsPeriod H (n • ((1, 0) : G)) := by simpa [K] using (hp false).1
  have hH₂ : IsPeriod H (n • ((0, 1) : G)) := by simpa [K] using (hp false).2
  refine ⟨n • ((1, 0) : G), n • ((0, 1) : G), ?_,
    hF₁.add_config hH₁, hF₂.add_config hH₂⟩
  simp [Geometry.det, Prod.smul_mk]
  exact_mod_cast Nat.ne_of_gt hn

theorem doublyPeriodic_neg {F : G → A} (hF : IsDoublyPeriodic F) :
    IsDoublyPeriodic (-F) := by
  obtain ⟨h, k, hdet, hh, hk⟩ := hF
  exact ⟨h, k, hdet, hh.neg_config, hk.neg_config⟩

theorem doublyPeriodic_sub {F H : G → A}
    (hF : IsDoublyPeriodic F) (hH : IsDoublyPeriodic H) :
    IsDoublyPeriodic (F - H) := by
  simpa [sub_eq_add_neg] using doublyPeriodic_add hF (doublyPeriodic_neg hH)

theorem not_doublyPeriodic_add {F H : G → A}
    (hF : ¬IsDoublyPeriodic F) (hH : IsDoublyPeriodic H) :
    ¬IsDoublyPeriodic (F + H) := by
  intro h
  have heq : F + H - H = F := by abel
  exact hF (heq ▸ doublyPeriodic_sub h hH)

structure Data (A : Type*) [AddCommGroup A] where
  count : ℕ
  many : 2 ≤ count
  component : Fin count → G → A
  period : Fin count → G
  period_ne_zero : ∀ i, period i ≠ 0
  independent : ∀ i j, i ≠ j → Geometry.det (period i) (period j) ≠ 0
  component_period : ∀ i, IsPeriod (component i) (period i)
  not_doublyPeriodic : ∀ i, ¬IsDoublyPeriodic (component i)

namespace Data

def total (T : Data A) (z : G) : A := ∑ i, T.component i z

theorem index_nonempty (T : Data A) : Nonempty (Fin T.count) := by
  have hm := T.many
  exact ⟨⟨0, by omega⟩⟩

theorem index_nontrivial (T : Data A) : Nontrivial (Fin T.count) := by
  have hm := T.many
  refine ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩⟩
  intro h
  have := congrArg Fin.val h
  change (0 : ℕ) = 1 at this
  omega

end Data

section Reduction

variable {ι : Type*} [Fintype ι]

abbrev Good (F : ι → G → A) := {i : ι // IsDoublyPeriodic (F i)}
abbrev Bad (F : ι → G → A) := {i : ι // ¬IsDoublyPeriodic (F i)}

def background (F : ι → G → A) : G → A := ∑ i : Good F, F i.val

theorem background_doublyPeriodic (F : ι → G → A) :
    IsDoublyPeriodic (background F) :=
  doublyPeriodic_sum (fun i : Good F => F i.val) (fun i => i.property)

theorem partition_sum (F : ι → G → A) :
    background F + ∑ i : Bad F, F i.val = ∑ i, F i := by
  exact Fintype.sum_subtype_add_sum_subtype (fun i => IsDoublyPeriodic (F i)) F

theorem bad_nonempty (F : ι → G → A) (hnot : ¬IsPeriodic (∑ i, F i)) :
    Nonempty (Bad F) := by
  by_contra h
  have hp : ∀ i, IsDoublyPeriodic (F i) := by
    intro i
    by_contra hi
    exact h ⟨⟨i, hi⟩⟩
  exact hnot (doublyPeriodic_sum F hp).isPeriodic

def absorbed (F : ι → G → A) (j : Bad F) (i : Bad F) : G → A :=
  F i.val + if i = j then background F else 0

theorem absorbed_sum (F : ι → G → A) (j : Bad F) :
    ∑ i, absorbed F j i = ∑ i, F i := by
  simp only [absorbed, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  rw [add_comm]
  exact partition_sum F

theorem absorbed_not_doublyPeriodic (F : ι → G → A) (j i : Bad F) :
    ¬IsDoublyPeriodic (absorbed F j i) := by
  by_cases hij : i = j
  · simp only [absorbed, hij, if_true]
    exact not_doublyPeriodic_add j.property (background_doublyPeriodic F)
  · simpa [absorbed, hij] using i.property

theorem det_nsmul_both (h k : G) (a b : ℕ) :
    Geometry.det (a • h) (b • k) = (a : ℤ) * (b : ℤ) * Geometry.det h k := by
  simp [Geometry.det, nsmul_eq_mul]
  ring

/-- The surviving directions may be replaced by positive multiples, so the
absorbed background shares the chosen component's period. -/
theorem reduce (F : ι → G → A) (h : ι → G)
    (hn : ∀ i, h i ≠ 0)
    (hindependent : ∀ i j, i ≠ j → Geometry.det (h i) (h j) ≠ 0)
    (hperiod : ∀ i, IsPeriod (F i) (h i))
    (hnot : ¬IsPeriodic (∑ i, F i)) :
    ∃ T : Data A, T.total = ∑ i, F i := by
  let j : Bad F := Classical.choice (bad_nonempty F hnot)
  obtain ⟨κ, hκ, _, hFκ, hBκ⟩ := synchronize_direction_period (F j.val)
    (fun _ : Unit => background F) (h j.val) 1 (by omega)
    (by simpa using hperiod j.val) (fun _ => background_doublyPeriodic F)
  let scale : Bad F → ℕ := fun i => if i = j then κ else 1
  let period : Bad F → G := fun i => scale i • h i.val
  have hscale : ∀ i, 0 < scale i := by
    intro i
    by_cases hij : i = j <;> simp [scale, hij, hκ]
  have hper : ∀ i, IsPeriod (absorbed F j i) (period i) := by
    intro i
    by_cases hij : i = j
    · subst i
      simpa [absorbed, period, scale] using hFκ.add_config (hBκ ())
    · simpa [absorbed, period, scale, hij] using hperiod i.val
  have hne : ∀ i, period i ≠ 0 := fun i =>
    nsmul_lattice_ne_zero (hn i.val) (hscale i)
  have hind : ∀ i k : Bad F, i ≠ k → Geometry.det (period i) (period k) ≠ 0 := by
    intro i k hik
    have hval : i.val ≠ k.val := fun heq => hik (Subtype.ext heq)
    dsimp [period]
    rw [det_nsmul_both]
    exact mul_ne_zero (mul_ne_zero
      (by exact_mod_cast Nat.ne_of_gt (hscale i))
      (by exact_mod_cast Nat.ne_of_gt (hscale k))) (hindependent _ _ hval)
  have hmany : 2 ≤ Fintype.card (Bad F) := by
    by_contra hsmall
    have hc : Fintype.card (Bad F) ≤ 1 := by omega
    letI : Subsingleton (Bad F) := Fintype.card_le_one_iff_subsingleton.mp hc
    have hsum : (∑ i, absorbed F j i) = absorbed F j j :=
      Fintype.sum_subsingleton _ j
    apply hnot
    rw [← absorbed_sum F j, hsum]
    exact ⟨period j, hne j, hper j⟩
  let e := (Fintype.equivFin (Bad F)).symm
  let T : Data A := {
    count := Fintype.card (Bad F)
    many := hmany
    component := fun i => absorbed F j (e i)
    period := fun i => period (e i)
    period_ne_zero := fun i => hne (e i)
    independent := fun i k hik => hind (e i) (e k) (fun heq => hik (e.injective heq))
    component_period := fun i => hper (e i)
    not_doublyPeriodic := fun i => absorbed_not_doublyPeriodic F j (e i) }
  refine ⟨T, ?_⟩
  funext z
  change (∑ i, absorbed F j (e i) z) = (∑ i, F i) z
  rw [Fintype.sum_equiv e (fun i => absorbed F j (e i) z)
    (fun i => absorbed F j i z) (fun _ => rfl)]
  have hz := congrFun (absorbed_sum F j) z
  simpa only [Finset.sum_apply] using hz

end Reduction

end

end NivatTrial.ReducedDecomposition
