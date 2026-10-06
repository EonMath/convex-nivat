import NivatTrial.Geometry

/-! Every sufficiently high row meets each far translate of a half-open
lattice parallelogram in a contiguous block of the prescribed length.
Euclidean division selects its unique vertical translate and one residue
class for the transverse determinant. -/

namespace NivatTrial.ColleParallelogramRows

open NivatTrial.Geometry
open scoped Classical

noncomputable section

def cell (a k : Lattice) (L : ℕ) : Set Lattice :=
  {w | a.2 ≤ w.2 ∧ w.2 < a.2+k.2 ∧
    det k a < det k w ∧ det k w ≤ det k a+(L:ℤ)*k.2}

/-- One integer translate of the half-open cell contains `L` consecutive
sites of every sufficiently high row. The same translate index works for
all these sites. -/
theorem consecutive_points_on_high_row
    (a k : Lattice) (hk : 0 < k.2) (L : ℕ)
    (N : ℕ) (t : ℤ) (ht : a.2+(N:ℤ)*k.2 ≤ t) :
    ∃ l n : ℤ, (N:ℤ) ≤ n ∧
      ∀ j : Fin L, ∃ w ∈ cell a k L,
        (l+(j:ℤ),t) = w+n•k := by
  let n : ℤ := (t-a.2)/k.2
  let remY : ℤ := (t-a.2)%k.2
  let y : ℤ := a.2+remY
  have hremY0 : 0 ≤ remY := Int.emod_nonneg _ (ne_of_gt hk)
  have hremYk : remY < k.2 := Int.emod_lt_of_pos _ hk
  have hny : (N:ℤ) ≤ n := by
    dsimp [n]
    apply (Int.le_ediv_iff_mul_le hk).mpr
    omega
  have hy : y+n*k.2 = t := by
    have he := Int.emod_add_mul_ediv (t-a.2) k.2
    dsimp [y,n,remY]
    nlinarith
  let m : ℤ := k.1*y-det k a
  let r : ℤ := (m-1)/k.2
  let remD : ℤ := (m-1)%k.2
  have hremD0 : 0 ≤ remD := Int.emod_nonneg _ (ne_of_gt hk)
  have hremDk : remD < k.2 := Int.emod_lt_of_pos _ hk
  have hmr : m-k.2*r = remD+1 := by
    have he := Int.emod_add_mul_ediv (m-1) k.2
    dsimp [r,remD]
    omega
  let l : ℤ := r-((L:ℤ)-1)+n*k.1
  refine ⟨l,n,hny,?_⟩
  intro j
  let x : ℤ := r-((L:ℤ)-1)+(j:ℤ)
  let w : Lattice := (x,y)
  have hj0 : (0:ℤ) ≤ j := by positivity
  have hjL : (j:ℤ) < L := by exact_mod_cast j.isLt
  have hshift0 : 0 ≤ (L:ℤ)-1-(j:ℤ) := by omega
  have hshiftL : (L:ℤ)-1-(j:ℤ) ≤ (L:ℤ)-1 := by omega
  have hdet : det k w-det k a = remD+1+k.2*((L:ℤ)-1-(j:ℤ)) := by
    dsimp [w,x,m,det] at *
    nlinarith [hmr]
  have hdetlo : det k a < det k w := by
    have hprod := mul_nonneg hk.le hshift0
    omega
  have hdetupper : det k w ≤ det k a+(L:ℤ)*k.2 := by
    have hprod := mul_le_mul_of_nonneg_left hshiftL hk.le
    nlinarith
  have hw : w ∈ cell a k L := by
    change a.2 ≤ w.2 ∧ w.2 < a.2+k.2 ∧
      det k a < det k w ∧ det k w ≤ det k a+(L:ℤ)*k.2
    dsimp [w,y]
    exact ⟨by omega,by omega,hdetlo,hdetupper⟩
  refine ⟨w,hw,?_⟩
  ext
  · simp [w,x,l]
    ring
  · simpa [w,Prod.smul_mk,smul_eq_mul] using hy.symm

end
end NivatTrial.ColleParallelogramRows
