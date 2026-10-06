import NivatTrial.JointFiberLimits
import NivatTrial.MaximalIncrementFibers

/-! Eliminate a one-sided deterministic direction using an attained maximal
difference fiber. The new orbit closure inherits determinism on the reverse
side because a further ambiguous pair would enlarge that maximal fiber. -/

namespace NivatTrial.DirectionalElimination

open NivatTrial.Nonexpansive NivatTrial.Dynamics NivatTrial.PeriodicDifference
open NivatTrial.FiniteIncrementFibers NivatTrial.SeparatedFiberLimits
open NivatTrial.JointFiberLimits NivatTrial.MaximalIncrementFibers
open Filter
open scoped Classical
noncomputable section

theorem exists_window_on_lower_side (v : Plane) (d : Lattice)
    (hd : 0 < score v d) (B : Finset Lattice) :
    ∃ u : Lattice, ∀ b ∈ B, score v (u+b) ≤ 0 := by
  have hall : ∀ᶠ n : ℕ in atTop, ∀ b : B, score v (b.val-n•d) ≤ 0 :=
    eventually_all.mpr (fun b => eventually_score_translate_nonpos v d hd b.val)
  obtain ⟨n,hn⟩ := hall.exists
  refine ⟨-(n•d),?_⟩
  intro b hb
  simpa only [sub_eq_add_neg,add_comm] using hn ⟨b,hb⟩

variable {A : Type*} [Fintype A]

theorem eliminate_direction (θ : Lattice → A) (w : A → ℤ)
    (h d : Lattice) (v : Plane) (hd : 0 < score v d) (B : Finset Lattice)
    (hcode : ∀ x ∈ languageHull θ, ∀ y ∈ languageHull θ,
      increment (encode w x) h = increment (encode w y) h →
      (∀ b ∈ B, x b = y b) → ∀ z, score v z ≤ 0 → x z = y z)
    (hfactor : ∀ x ∈ languageHull θ, ∀ y ∈ languageHull θ,
      (∀ z, score v z ≤ 0 → x z = y z) →
      increment (encode w x) h = increment (encode w y) h) :
    ∃ ξ ∈ languageHull θ, OneSidedExpansive ξ (-v) := by
  obtain ⟨n,hn,F,hF,hinj,hinc,hmax⟩ := exists_maximal_fiber θ w h
    (Fintype.card A ^ B.card)
    (card_bound_of_fiber_coding θ w h d v hd B hcode)
  obtain ⟨G,hG,hGinc,hGsep⟩ :=
    exists_separated_fiber_limit θ w h d v hd B hcode n F hF hinj hinc
  let i₀ : Fin n := ⟨0,hn⟩
  refine ⟨G i₀,hG i₀,?_⟩
  rintro ⟨x,hx,y,hy,hne,hagree⟩
  have hxθ := languageHull_trans (hG i₀) hx
  have hyθ := languageHull_trans (hG i₀) hy
  have hlower : ∀ z, score v z ≤ 0 → x z = y z := by
    intro z hz
    apply hagree
    change 0 ≤ score (-v) z
    rw [score_neg_direction]
    linarith
  have hxyinc := hfactor x hxθ y hyθ hlower
  obtain ⟨E,hE,hfirst,hEinc,hEsep⟩ :=
    lift_fiber_limit θ w h n G hG hGinc B hGsep i₀ x hx
  have hEinj : Function.Injective E := by
    intro i j he
    by_contra hij
    exact hEsep i j hij 0 (congrArg (fun f => patternAt f B 0) he)
  obtain ⟨u,hu⟩ := exists_window_on_lower_side v d hd B
  have hyne (j : Fin n) : y ≠ E j := by
    intro hey
    by_cases hj : j = i₀
    · subst j
      exact hne (hfirst.symm.trans hey.symm)
    · apply hEsep i₀ j (Ne.symm hj) u
      have he : patternAt (E i₀) B u = patternAt y B u := by
        rw [hfirst]
        funext b
        exact hlower (u+b.val) (hu b b.property)
      exact he.trans (congrArg (fun f => patternAt f B u) hey)
  have hyoutside : y ∉ Set.range E := by
    rintro ⟨j,hj⟩
    exact hyne j hj.symm
  let F' : Fin (n+1) → Lattice → A := Fin.cons y E
  have hconsinj : Function.Injective F' :=
    Fin.cons_injective_of_injective hyoutside hEinj
  have hconshull (j : Fin (n+1)) : F' j ∈ languageHull θ := by
    refine Fin.cases hyθ (fun i => hE i) j
  have hconsinc (j : Fin (n+1)) :
      increment (encode w (F' j)) h = increment (encode w y) h := by
    refine Fin.cases rfl (fun i => ?_) j
    change increment (encode w (E i)) h = increment (encode w y) h
    exact (hEinc i i₀).trans (by rw [hfirst]; exact hxyinc)
  have htoo := hmax (n+1) F' hconshull hconsinj
    (fun i j => (hconsinc i).trans (hconsinc j).symm)
  omega

end
end NivatTrial.DirectionalElimination
