import NivatTrial.ColleStripDichotomy
import Mathlib.Data.Nat.Factorial.Basic

/-! The actual half-plane conclusion of Cyr--Kra's ambiguous-border
propagation, in horizontal lattice coordinates. The period of each moving
finite-width strip is bounded by the same 2h. Their periods all divide
(2h)!, so one fixed period works on the whole half-plane. -/

namespace NivatTrial.ColleHalfPlaneAmbiguity

open NivatTrial.Dynamics NivatTrial.Periodicity
open NivatTrial.BalancedWindows NivatTrial.ColleAmbiguity
open NivatTrial.ColleBalancedRows NivatTrial.ColleGenerating
open NivatTrial.ColleLocalSubshift NivatTrial.ColleStripDichotomy
open NivatTrial.ColleAmbiguousBandBound
open scoped Classical

set_option maxHeartbeats 1000000
noncomputable section

abbrev G := ℤ × ℤ
variable {A : Type*} [Fintype A]

private def horizontal : G := (1,0)
private def horizontalReal : ℝ × ℝ := (1,0)

theorem ambiguous_lower_halfPlane_period
    (θ : G → A) (B : Finset G)
    (hgen : GeneratingWindow θ B) (hB : MinusBalanced θ B)
    {x : G → A} (hx : x ∈ languageHull θ) (d0 : ℤ)
    (hamb : ∀ i : ℤ,
      2 ≤ extensionCount (restriction θ B horizontalReal)
        (restriction θ B horizontalReal
          ⟨patternAt x B (i,d0-lower B),
            localAdmissible_of_hull hx (i,d0-lower B)⟩)) :
    let Q := Nat.factorial (2*((bottomEdge B).card-1))
    0 < Q ∧ ∀ z : G, z.2 ≤ d0+upper B-lower B →
      x (z+(Q:ℤ) • horizontal) = x z := by
  let h := (bottomEdge B).card-1
  let H : ℤ := upper B-lower B
  let Q := Nat.factorial (2*h)
  have hH : 0≤H := by
    dsimp [H]
    exact sub_nonneg.mpr (lower_le_upper hB.nonempty)
  have hxlocal : LocalAdmissible θ B x := localAdmissible_of_hull hx
  have hbands : ∀ n : ℕ, ∃ q : ℕ, 0<q ∧ q≤2*h ∧
      ∀ z : G, d0-(n:ℤ)≤z.2 → z.2≤d0-(n:ℤ)+H →
        x (z+(q:ℤ) • horizontal)=x z := by
    intro n
    induction n with
    | zero =>
      obtain ⟨p,hp,hpbound,hinner⟩ :=
        ambiguous_inner_band_bounded_period θ B hB x hxlocal d0 hamb
      obtain ⟨q,hq,hqbound,hband⟩ :=
        adjacent_strip_bounded_period θ B hgen hB hx d0 p hp
          (by omega) hinner
      refine ⟨q,hq,by simpa [h] using hqbound,?_⟩
      intro z hzlow hzhigh
      have hh := hband z (by simpa using hzlow)
        (by dsimp [H] at hzhigh ⊢; omega)
      exact hh
    | succ n ih =>
      obtain ⟨p,hp,hpbound,hprev⟩ := ih
      let d : ℤ := d0-(n:ℤ)-1
      have hinner : ∀ z : G, d<z.2 →
          z.2≤d+upper B-lower B →
          x (z+(p:ℤ) • horizontal)=x z := by
        intro z hzlow hzhigh
        apply hprev z
        · dsimp [d] at hzlow
          omega
        · dsimp [d,H] at hzhigh ⊢
          omega
      obtain ⟨q,hq,hqbound,hband⟩ :=
        adjacent_strip_bounded_period θ B hgen hB hx d p hp
          (by simpa [h] using hpbound) hinner
      refine ⟨q,hq,by simpa [h] using hqbound,?_⟩
      intro z hzlow hzhigh
      have hzlow' : d≤z.2 := by dsimp [d] at hzlow ⊢; omega
      have hzhigh' : z.2≤d+upper B-lower B := by
        dsimp [d,H] at hzhigh ⊢
        omega
      exact hband z hzlow' hzhigh'
  have hQ : 0<Q := Nat.factorial_pos _
  refine ⟨hQ,?_⟩
  intro z hzupper
  let n : ℕ := (d0-z.2).toNat
  have hnlow : d0-(n:ℤ)≤z.2 := by
    dsimp [n]
    omega
  have hnhigh : z.2≤d0-(n:ℤ)+H := by
    dsimp [n,H] at hzupper ⊢
    omega
  obtain ⟨q,hq,hqbound,hband⟩ := hbands n
  have hdiv : q ∣ Q := Nat.dvd_factorial hq hqbound
  obtain ⟨k,hk⟩ := hdiv
  let R : Set G := {z | d0-(n:ℤ)≤z.2 ∧ z.2≤d0-(n:ℤ)+H}
  have hperR : PeriodicOn x R ((q:ℤ) • horizontal) := by
    constructor
    · intro w hw
      change d0-(n:ℤ)≤(w+(q:ℤ) • horizontal).2 ∧
        (w+(q:ℤ) • horizontal).2≤d0-(n:ℤ)+H
      have he : (w+(q:ℤ) • horizontal).2=w.2 := by
        simp [horizontal]
      rw [he]
      exact hw
    · intro w hw
      exact hband w hw.1 hw.2
  have hmultiple : k • ((q:ℤ) • horizontal) = (Q:ℤ) • horizontal := by
    rw [hk]
    ext <;> simp [horizontal] <;> ring
  have hh := (hperR.nsmul k).2 z ⟨hnlow,hnhigh⟩
  rw [hmultiple] at hh
  exact hh

end

end NivatTrial.ColleHalfPlaneAmbiguity
