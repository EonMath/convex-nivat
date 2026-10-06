import NivatTrial.ColleSecondBoundaryPeriod
import NivatTrial.ColleDirectionalPropagation

/-! Transport the actual semi-ambiguity/periodic-band mechanism to a second
primitive lattice direction. All configuration and window hypotheses remain
the original language and actual pattern complexity after a unimodular
change of coordinates. -/

namespace NivatTrial.ColleSecondBoundaryCoordinates

open NivatTrial.Dynamics NivatTrial.BalancedWindows
open NivatTrial.ColleGenerating NivatTrial.ColleSecondBoundaryPeriod
open NivatTrial.ColleOneSidedAmbiguity NivatTrial.ColleSemiAmbiguity
open NivatTrial.ColleDirectionalPropagation NivatTrial.LatticeCoordinates
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ
variable {A : Type*} [Fintype A]

/-- Use the actual second-edge inner strip to obtain directional
semi-ambiguity. This interface does not require balance in the second
direction; the later parallel-cell counting argument supplies its own run. -/
theorem semi_ambiguous_of_slanted_inner_strip
    (e : G ≃+ G) (θ : G → A) (B : Finset G)
    (hgen : GeneratingWindow (θ ∘ e) B)
    {x y : G → A} (hx : x ∈ languageHull θ)
    (hy : y ∈ languageHull θ)
    (d : ℤ) (w : G) (hwrow : (e.symm w).2 = d)
    (hbad : x w ≠ y w)
    (H : ℤ) (hH : ∀ s ∈ B, s.1 ≤ H)
    (r : ℤ)
    (hr : ∃ l : ℤ, bottomEdge B =
      (Finset.Icc l r).image (fun j => (j,lower B)))
    (hagree : ∀ z : G,
      d < (e.symm z).2 →
      (e.symm z).2 ≤ d+upper B-lower B →
      (e.symm z).1 ≤ (e.symm w).1-r+H → x z=y z) :
    SemiAmbiguous (θ ∘ e) B (1,0) (-1,0)
      (shift (0,d-lower B) (x ∘ e))
      (shift_mem_languageHull (mem_languageHull_comp_equiv e hx)
        (0,d-lower B)) (r-(e.symm w).1) := by
  have hx' : x ∘ e ∈ languageHull (θ ∘ e) :=
    mem_languageHull_comp_equiv e hx
  have hy' : y ∘ e ∈ languageHull (θ ∘ e) :=
    mem_languageHull_comp_equiv e hy
  have hbad' : (x ∘ e) (e.symm w) ≠ (y ∘ e) (e.symm w) := by
    simpa using hbad
  have hagree' : ∀ z : G, d<z.2 →
      z.2≤d+upper B-lower B →
      z.1≤(e.symm w).1-r+H →
        (x ∘ e) z=(y ∘ e) z := by
    intro z hzlo hzup hzleft
    exact hagree (e z) (by simpa using hzlo)
      (by simpa using hzup) (by simpa using hzleft)
  exact semi_ambiguous_of_left_halfStrip (θ ∘ e) B hgen
    hx' hy' d (e.symm w) hwrow hbad' H hH r hr hagree'

/-- Both sides of a genuine interface realize the same ambiguous base
patterns. The periodic reference can therefore be used for directional
Morse--Hedlund even when the other configuration is aperiodic. -/
theorem semi_ambiguous_pair_of_slanted_inner_strip
    (e : G ≃+ G) (θ : G → A) (B : Finset G)
    (hgen : GeneratingWindow (θ ∘ e) B)
    {x p : G → A} (hx : x ∈ languageHull θ)
    (hp : p ∈ languageHull θ)
    (d : ℤ) (w : G) (hwrow : (e.symm w).2 = d)
    (hbad : x w ≠ p w)
    (H : ℤ) (hH : ∀ s ∈ B, s.1 ≤ H)
    (r : ℤ)
    (hr : ∃ l : ℤ, bottomEdge B =
      (Finset.Icc l r).image (fun j => (j,lower B)))
    (hagree : ∀ z : G,
      d < (e.symm z).2 →
      (e.symm z).2 ≤ d+upper B-lower B →
      (e.symm z).1 ≤ (e.symm w).1-r+H → x z=p z) :
    SemiAmbiguous (θ ∘ e) B (1,0) (-1,0)
      (shift (0,d-lower B) (x ∘ e))
      (shift_mem_languageHull (mem_languageHull_comp_equiv e hx)
        (0,d-lower B)) (r-(e.symm w).1) ∧
    SemiAmbiguous (θ ∘ e) B (1,0) (-1,0)
      (shift (0,d-lower B) (p ∘ e))
      (shift_mem_languageHull (mem_languageHull_comp_equiv e hp)
        (0,d-lower B)) (r-(e.symm w).1) := by
  refine ⟨semi_ambiguous_of_slanted_inner_strip e θ B hgen hx hp d w
    hwrow hbad H hH r hr hagree,?_⟩
  apply semi_ambiguous_of_slanted_inner_strip e θ B hgen hp hx d w
    hwrow hbad.symm H hH r hr
  intro z hzlo hzup hzleft
  exact (hagree z hzlo hzup hzleft).symm

theorem eventual_period_of_slanted_halfStrip_interface
    (e : G ≃+ G) (θ : G → A) (B : Finset G)
    (hgen : GeneratingWindow (θ ∘ e) B)
    (hbalanced : MinusBalanced (θ ∘ e) B)
    {x y : G → A} (hx : x ∈ languageHull θ)
    (hy : y ∈ languageHull θ)
    (d : ℤ) (w : G) (hwrow : (e.symm w).2 = d)
    (hbad : x w ≠ y w)
    (H L : ℤ) (hH : ∀ s ∈ B, s.1 ≤ H)
    (hL : ∀ s ∈ B, L ≤ s.1)
    (r : ℤ)
    (hr : ∃ l : ℤ, bottomEdge B =
      (Finset.Icc l r).image (fun j => (j,lower B)))
    (hagree : ∀ z : G,
      d < (e.symm z).2 →
      (e.symm z).2 ≤ d+upper B-lower B →
      (e.symm z).1 ≤ (e.symm w).1-r+H → x z = y z) :
    ∃ N Q : ℕ, 0 < Q ∧
      ∀ z : G,
        d < (e.symm z).2 →
        (e.symm z).2 ≤ d+upper B-lower B →
        (e.symm z).1 ≤ L-(r-(e.symm w).1+N) →
          x (z+(Q:ℤ) • (e (-1,0))) = x z := by
  have hx' : x ∘ e ∈ languageHull (θ ∘ e) :=
    mem_languageHull_comp_equiv e hx
  have hy' : y ∘ e ∈ languageHull (θ ∘ e) :=
    mem_languageHull_comp_equiv e hy
  have hbad' : (x ∘ e) (e.symm w) ≠ (y ∘ e) (e.symm w) := by
    simpa using hbad
  have hagree' : ∀ z : G, d<z.2 →
      z.2≤d+upper B-lower B →
      z.1≤(e.symm w).1-r+H →
        (x ∘ e) z=(y ∘ e) z := by
    intro z hzlo hzup hzleft
    exact hagree (e z) (by simpa using hzlo)
      (by simpa using hzup) (by simpa using hzleft)
  obtain ⟨N,Q,hQ,hper⟩ :=
    eventual_period_of_left_halfStrip_interface
      (θ ∘ e) B hgen hbalanced hx' hy' d (e.symm w)
      hwrow hbad' H L hH hL r hr hagree'
  refine ⟨N,Q,hQ,?_⟩
  intro z hzlo hzup hzleft
  have hh := hper (e.symm z) hzlo hzup hzleft
  change x (e (e.symm z+(Q:ℤ) • ((-1,0):G))) = x (e (e.symm z)) at hh
  rw [map_add,map_zsmul,e.apply_symm_apply] at hh
  exact hh

end
end NivatTrial.ColleSecondBoundaryCoordinates
