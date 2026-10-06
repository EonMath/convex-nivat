import NivatTrial.ColleOneSidedAmbiguity

/-! The highest row with defects arbitrarily far to the left gives the
exact one-sided interior strip required by boundary ambiguity. -/

namespace NivatTrial.ColleHighestBoundaryRow

open NivatTrial.Geometry
open scoped Classical
noncomputable section

theorem finite_uniform_left_cutoff (F : Finset ℤ) (P : ℤ → ℤ → Prop)
    (h : ∀ d ∈ F, ∃ L : ℤ, ∀ j : ℤ, j ≤ L → P d j) :
    ∃ L : ℤ, ∀ d ∈ F, ∀ j : ℤ, j ≤ L → P d j := by
  induction F using Finset.induction_on with
  | empty => exact ⟨0,by simp⟩
  | @insert d F hd ih =>
    obtain ⟨Ld,hLd⟩ := h d (by simp)
    obtain ⟨LF,hLF⟩ := ih (fun e he => h e (by simp [he]))
    refine ⟨min Ld LF,?_⟩
    intro e he j hj
    rcases Finset.mem_insert.mp he with rfl | he
    · exact hLd j (hj.trans (min_le_left _ _))
    · exact hLF e he j (hj.trans (min_le_right _ _))

def LeftUnboundedDefects {A : Type*} (x p : Lattice → A) (d : ℤ) : Prop :=
  ∀ L : ℤ, ∃ j : ℤ, j ≤ L ∧ x (j,d) ≠ p (j,d)

theorem left_cutoff_of_not_unbounded {A : Type*} (x p : Lattice → A) (d : ℤ)
    (h : ¬LeftUnboundedDefects x p d) :
    ∃ L : ℤ, ∀ j : ℤ, j ≤ L → x (j,d) = p (j,d) := by
  by_contra hn
  apply h
  intro L
  by_contra hno
  apply hn
  refine ⟨L,?_⟩
  intro j hj
  by_contra he
  exact hno ⟨j,hj,he⟩

theorem exists_highest_unbounded_row {A : Type*} (x p : Lattice → A) (a b : ℤ)
    (hbad : ∀ L : ℤ, ∃ z : Lattice,
      a ≤ z.2 ∧ z.2 ≤ b ∧ z.1 ≤ L ∧ x z ≠ p z) :
    ∃ d : ℤ, a ≤ d ∧ d ≤ b ∧ LeftUnboundedDefects x p d ∧
      ∀ e : ℤ, d < e → e ≤ b → ¬LeftUnboundedDefects x p e := by
  let F := (Finset.Icc a b).filter (LeftUnboundedDefects x p)
  have hF : F.Nonempty := by
    by_contra hn
    have hnot : ∀ d ∈ Finset.Icc a b, ¬LeftUnboundedDefects x p d := by
      intro d hd hp
      exact hn ⟨d,Finset.mem_filter.mpr ⟨hd,hp⟩⟩
    obtain ⟨L,hL⟩ := finite_uniform_left_cutoff (Finset.Icc a b)
      (fun d j => x (j,d) = p (j,d))
      (fun d hd => left_cutoff_of_not_unbounded x p d (hnot d hd))
    obtain ⟨z,haz,hzb,hzL,hne⟩ := hbad L
    exact hne (hL z.2 (Finset.mem_Icc.mpr ⟨haz,hzb⟩) z.1 hzL)
  obtain ⟨d,hd,hmax⟩ := F.exists_max_image (fun d => d) hF
  obtain ⟨hdI,hdu⟩ := Finset.mem_filter.mp hd
  obtain ⟨had,hdb⟩ := Finset.mem_Icc.mp hdI
  refine ⟨d,had,hdb,hdu,?_⟩
  intro e hde heb he
  have heF : e ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,heb⟩,he⟩
  have hh := hmax e heF
  omega

/-- The resulting cutoff is expressed relative to the actual bad point,
so any fixed window width can be absorbed before choosing that point. -/
theorem exists_bad_point_with_left_inner_strip {A : Type*}
    (x p : Lattice → A) (a b : ℤ)
    (hbad : ∀ L : ℤ, ∃ z : Lattice,
      a ≤ z.2 ∧ z.2 ≤ b ∧ z.1 ≤ L ∧ x z ≠ p z)
    (habove : ∀ H : ℤ, ∃ L : ℤ, ∀ z : Lattice,
      b < z.2 → z.2 ≤ H → z.1 ≤ L → x z = p z)
    (height width : ℤ) :
    ∃ w : Lattice, a ≤ w.2 ∧ w.2 ≤ b ∧ x w ≠ p w ∧
      ∀ z : Lattice, w.2 < z.2 → z.2 ≤ w.2+height →
        z.1 ≤ w.1+width → x z = p z := by
  obtain ⟨d,had,hdb,hdu,hmax⟩ := exists_highest_unbounded_row x p a b hbad
  obtain ⟨L₁,hL₁⟩ := finite_uniform_left_cutoff (Finset.Icc (d+1) b)
    (fun e j => x (j,e) = p (j,e)) (by
      intro e he
      obtain ⟨hle,heb⟩ := Finset.mem_Icc.mp he
      exact left_cutoff_of_not_unbounded x p e (hmax e (by omega) heb))
  obtain ⟨L₂,hL₂⟩ := habove (d+height)
  obtain ⟨j,hj,hjne⟩ := hdu (min L₁ L₂-width)
  refine ⟨(j,d),had,hdb,hjne,?_⟩
  intro z hdz hzh hzx
  have hzmin : z.1 ≤ min L₁ L₂ := by
    change z.1 ≤ j+width at hzx
    omega
  by_cases hzb : z.2 ≤ b
  · have heq := hL₁ z.2 (Finset.mem_Icc.mpr ⟨by change d < z.2 at hdz; omega,hzb⟩)
      z.1 (hzmin.trans (min_le_left _ _))
    exact heq
  · exact hL₂ z (lt_of_not_ge hzb) hzh (hzmin.trans (min_le_right _ _))

end
end NivatTrial.ColleHighestBoundaryRow
