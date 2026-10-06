import NivatTrial.ColleOneSidedBoundary
import NivatTrial.ColleInterfaceAmbiguity
import NivatTrial.ColleSemiAmbiguity
import NivatTrial.ColleBalancedRows

/-! A one-sided finite-height agreement strip with a genuine defect on its
exposed row produces ambiguous actual language patterns at every sufficiently
distant anchor along the opposite ray. This is the local interface mechanism
needed at a second edge of a convex agreement region. -/

namespace NivatTrial.ColleOneSidedAmbiguity

open NivatTrial.Dynamics NivatTrial.BalancedWindows
open NivatTrial.ColleAmbiguity NivatTrial.ColleGenerating
open NivatTrial.ColleOneSidedBoundary NivatTrial.ColleInterfaceAmbiguity
open NivatTrial.ColleBalancedRows NivatTrial.ColleLocalSubshift
open NivatTrial.ColleSemiAmbiguity
open scoped Classical

set_option maxHeartbeats 1000000
noncomputable section

abbrev G := ℤ × ℤ
variable {A : Type*} [Fintype A]

/-- The boundary defect yields two true extensions at every sufficiently
far-left anchor. The agreement assumption is only a finite-height, one-sided
strip, with its right endpoint stated by an elementary bound on the window. -/
theorem eventually_ambiguous_of_left_halfStrip
    (θ : G → A) (B : Finset G) (hB : GeneratingWindow θ B)
    {x y : G → A} (hx : x ∈ languageHull θ)
    (hy : y ∈ languageHull θ)
    (d : ℤ) (w : G) (hwrow : w.2 = d) (hbad : x w ≠ y w)
    (H : ℤ) (hH : ∀ s ∈ B, s.1 ≤ H)
    (r : ℤ)
    (hr : ∃ l : ℤ, bottomEdge B =
      (Finset.Icc l r).image (fun j => (j,lower B)))
    (hagree : ∀ z : G, d < z.2 →
      z.2 ≤ d + upper B - lower B →
      z.1 ≤ w.1 - r + H → x z = y z) :
    ∀ i : ℤ, r-w.1 ≤ i →
      AmbiguousPattern θ B (1,0)
        ⟨patternAt x (supportBase B (1,0)) (-i,d-lower B),
          patternSet_subset_of_mem_languageHull hx _ ⟨(-i,d-lower B),rfl⟩⟩ := by
  intro i hi
  let a : G := (-i,d-lower B)
  let N : ℕ := (w.1+i-r).toNat
  have hNnonneg : 0 ≤ w.1+i-r := by omega
  have hNcast : (N:ℤ)=w.1+i-r := Int.toNat_of_nonneg hNnonneg
  have hbase : ∀ s ∈ supportBase B (1,0), x (a+s)=y (a+s) := by
    intro s hs
    have hu : s ∈ upperBase B := by
      rw [← horizontal_supportBase_eq_upperBase B hB.nonempty]
      exact hs
    rw [upperBase_eq_filter] at hu
    obtain ⟨hsB,hsstrict⟩ := Finset.mem_filter.mp hu
    have hmin := lower_le_of_mem hsB
    have hmax := le_upper_of_mem hsB
    apply hagree
    · change d < (d-lower B)+s.2
      omega
    · change (d-lower B)+s.2 ≤ d+upper B-lower B
      omega
    · change -i+s.1 ≤ w.1-r+H
      have hbound := hH s hsB
      omega
  have hinterior : ∀ k : ℕ, k≤N → ∀ s ∈ B,
      lower B<s.2 →
      x (a+(k:ℤ) • ((1,0):G)+s)=
        y (a+(k:ℤ) • ((1,0):G)+s) := by
    intro k hk s hs hsstrict
    have hmax := le_upper_of_mem hs
    have hsb := hH s hs
    apply hagree
    · change d < (d-lower B)+(k:ℤ)*0+s.2
      omega
    · change (d-lower B)+(k:ℤ)*0+s.2 ≤ d+upper B-lower B
      omega
    · have hcoord : (a + (k:ℤ) • ((1,0):G) + s).1 =
          -i+(k:ℤ)+s.1 := by simp [a]
      rw [hcoord]
      have hk' : (k:ℤ) ≤ N := by exact_mod_cast hk
      omega
  have hwin : ∀ l r' : ℤ,
      bottomEdge B=(Finset.Icc l r').image (fun j => (j,lower B)) →
      a.1+l≤w.1 ∧ w.1≤a.1+r'+(N:ℤ) := by
    intro l r' heq
    obtain ⟨l0,heq0⟩ := hr
    have hrEq : r'=r := by
      have hrMem : (r,lower B) ∈ bottomEdge B := by
        rw [heq0]
        have hlr : l0≤r := by
          have hne := bottomEdge_nonempty hB.nonempty
          rw [heq0] at hne
          obtain ⟨s,hs⟩ := hne
          obtain ⟨j,hj,_⟩ := Finset.mem_image.mp hs
          exact (Finset.mem_Icc.mp hj).1.trans (Finset.mem_Icc.mp hj).2
        exact Finset.mem_image.mpr ⟨r,Finset.mem_Icc.mpr ⟨hlr,le_rfl⟩,rfl⟩
      have hrr : r≤r' := by
        rw [heq] at hrMem
        obtain ⟨j,hj,hjs⟩ := Finset.mem_image.mp hrMem
        have hje : j=r := congrArg Prod.fst hjs
        exact hje ▸ (Finset.mem_Icc.mp hj).2
      have hrr' : r'≤r := by
        have hrMem' : (r',lower B) ∈ bottomEdge B := by
          rw [heq]
          have hlr : l≤r' := by
            have hne := bottomEdge_nonempty hB.nonempty
            rw [heq] at hne
            obtain ⟨s,hs⟩ := hne
            obtain ⟨j,hj,_⟩ := Finset.mem_image.mp hs
            exact (Finset.mem_Icc.mp hj).1.trans (Finset.mem_Icc.mp hj).2
          exact Finset.mem_image.mpr ⟨r',Finset.mem_Icc.mpr ⟨hlr,le_rfl⟩,rfl⟩
        rw [heq0] at hrMem'
        obtain ⟨j,hj,hjs⟩ := Finset.mem_image.mp hrMem'
        have hje : j=r' := congrArg Prod.fst hjs
        exact hje ▸ (Finset.mem_Icc.mp hj).2
      omega
    have hlr : l≤r' := by
      have hne := bottomEdge_nonempty hB.nonempty
      rw [heq] at hne
      obtain ⟨s,hs⟩ := hne
      obtain ⟨j,hj,_⟩ := Finset.mem_image.mp hs
      exact (Finset.mem_Icc.mp hj).1.trans (Finset.mem_Icc.mp hj).2
    dsimp [a]
    omega
  have hedge := exposed_defect_of_interior_right_corridor θ B hB
    (localAdmissible_of_hull hx) (localAdmissible_of_hull hy)
    a w N (by dsimp [a]; omega) hwin hbad hinterior
  have hedge' : ∃ s ∈ supportEdge B (1,0), x (a+s) ≠ y (a+s) := by
    have hEdge : supportEdge B ((1,0):ℝ×ℝ)=bottomEdge B := by
      exact horizontal_supportEdge_eq_bottomEdge B hB.nonempty
    rw [hEdge]
    exact hedge
  have ha := ambiguous_of_two_hull_extensions θ B (1,0) hx hy a hbase hedge'
  simpa only [a] using ha

/-- Pack the preceding actual extension count into the directional
semi-ambiguity interface. The ray points left, as in a region whose first
boundary is forward invariant under negative horizontal translation. -/
theorem semi_ambiguous_of_left_halfStrip
    (θ : G → A) (B : Finset G) (hB : GeneratingWindow θ B)
    {x y : G → A} (hx : x ∈ languageHull θ)
    (hy : y ∈ languageHull θ)
    (d : ℤ) (w : G) (hwrow : w.2 = d) (hbad : x w ≠ y w)
    (H : ℤ) (hH : ∀ s ∈ B, s.1 ≤ H)
    (r : ℤ)
    (hr : ∃ l : ℤ, bottomEdge B =
      (Finset.Icc l r).image (fun j => (j,lower B)))
    (hagree : ∀ z : G, d < z.2 →
      z.2 ≤ d + upper B - lower B →
      z.1 ≤ w.1 - r + H → x z = y z) :
    SemiAmbiguous θ B (1,0) (-1,0)
      (shift (0,d-lower B) x)
      (shift_mem_languageHull hx (0,d-lower B)) (r-w.1) := by
  intro i hi
  have ha := eventually_ambiguous_of_left_halfStrip θ B hB hx hy
    d w hwrow hbad H hH r hr hagree i hi
  convert ha using 1
  apply Subtype.ext
  funext s
  change (shift (0,d-lower B) x) (i • ((-1,0):G) + s.val) =
    x ((-i,d-lower B)+s.val)
  have hvec : ((0,d-lower B):G)+i • ((-1,0):G) =
      (-i,d-lower B) := by ext <;> simp
  change x (((0,d-lower B):G)+(i • ((-1,0):G)+s.val)) =
    x ((-i,d-lower B)+s.val)
  rw [← add_assoc, hvec]

end
end NivatTrial.ColleOneSidedAmbiguity
