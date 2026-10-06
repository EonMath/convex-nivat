import NivatTrial.ColleSemiAmbiguity

/-! The finite-family synchronization in Colle's Claim 4.2: the relevant
row starts form a finite cross-section of a half-strip, so their eventual
periods can be multiplied into one common tail period. -/

namespace NivatTrial.ColleHalfStrip

open NivatTrial.Dynamics NivatTrial.ColleAmbiguity NivatTrial.MorseHedlund
open NivatTrial.ColleSemiAmbiguity
open scoped Classical
noncomputable section

abbrev G := ℤ × ℤ
abbrev Plane := ℝ × ℝ

def TailPeriod {A : Type*} (ξ : ℤ → A) (τ : ℤ) (q : ℕ) : Prop :=
  ∀ i : ℤ, τ ≤ i → ξ (i + q) = ξ i

theorem TailPeriod.nsmul {A : Type*} {ξ : ℤ → A} {τ : ℤ} {q : ℕ}
    (hp : TailPeriod ξ τ q) (k : ℕ) : TailPeriod ξ τ (k*q) := by
  intro i hi
  induction k with
  | zero => simp
  | succ k ih =>
    have hcast : ((Nat.succ k * q : ℕ) : ℤ) = ((k*q : ℕ) : ℤ) + q := by
      simp [Nat.succ_mul, Nat.cast_add]
    rw [hcast]
    have hbase : τ ≤ i + ((k*q : ℕ) : ℤ) := by omega
    calc
      ξ (i + (((k*q : ℕ) : ℤ) + (q : ℤ))) = ξ (i + ((k*q : ℕ) : ℤ)) := by
        simpa only [add_assoc] using hp (i + ((k*q : ℕ) : ℤ)) hbase
      _ = ξ i := ih

theorem TailPeriod.of_dvd {A : Type*} {ξ : ℤ → A} {τ : ℤ}
    {q Q : ℕ} (hp : TailPeriod ξ τ q) (hdiv : q ∣ Q) :
    TailPeriod ξ τ Q := by
  obtain ⟨k, rfl⟩ := hdiv
  simpa only [Nat.mul_comm] using hp.nsmul k

variable {A : Type*} [Fintype A]

/-- All rows in a finite cross-section of a semi-ambiguous half-strip share
one positive period after one common start threshold. -/
theorem common_semi_ambiguous_halfStrip_period
    (θ : G → A) (S : Finset G) (v : Plane) (u : G)
    (W : Finset G) (n : ℕ) (τ : ℤ)
    {x : G → A} (hx : x ∈ languageHull θ)
    (hamb : SemiAmbiguous θ S v u x hx τ)
    (hbudget : patternComplexity θ S <
      patternComplexity θ (supportBase S v) + (supportEdge S v).card)
    (hrun : ∀ w ∈ W, ∀ j : Fin n,
      w + (j.val : ℤ) • u ∈ supportBase S v)
    (hlen : (supportEdge S v).card - 1 ≤ n) :
    ∃ N Q : ℕ, 0 < Q ∧
      ∀ w ∈ W, ∀ i : ℤ, τ + N ≤ i →
        x (w + (i + Q) • u) = x (w + i • u) := by
  have hex (w : G) (hw : w ∈ W) :
      ∃ N q : ℕ, 0 < q ∧
        ∀ i : ℤ, τ + N ≤ i →
          x (w + (i + q) • u) = x (w + i • u) :=
    semi_ambiguous_row_eventually_periodic θ S v u w n τ hx hamb
      hbudget (hrun w hw) hlen
  let chooseN (w : W) : ℕ := Classical.choose (hex w.val w.property)
  let chooseQ (w : W) : ℕ :=
    Classical.choose (Classical.choose_spec (hex w.val w.property))
  have hchosen (w : W) : 0 < chooseQ w ∧
      ∀ i : ℤ, τ + chooseN w ≤ i →
        x (w.val + (i + chooseQ w) • u) = x (w.val + i • u) :=
    Classical.choose_spec (Classical.choose_spec (hex w.val w.property))
  let N := Finset.univ.sup chooseN
  let Q := ∏ w : W, chooseQ w
  have hQ : 0 < Q := Finset.prod_pos (fun w _ => (hchosen w).1)
  refine ⟨N,Q,hQ,?_⟩
  intro w hw i hi
  let ww : W := ⟨w,hw⟩
  have hNw : chooseN ww ≤ N := Finset.le_sup (f := chooseN) (Finset.mem_univ ww)
  have hiw : τ + chooseN ww ≤ i := by omega
  have hqdiv : chooseQ ww ∣ Q :=
    Finset.dvd_prod_of_mem chooseQ (Finset.mem_univ ww)
  have hper : TailPeriod (rowSequence x w u) (τ + chooseN ww) (chooseQ ww) :=
    (hchosen ww).2
  exact (hper.of_dvd hqdiv) i hiw

end

end NivatTrial.ColleHalfStrip
