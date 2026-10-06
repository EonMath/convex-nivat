import NivatTrial.ColleParallelogramWindow
import NivatTrial.ColleReferencePropagation

/-! Actual semi-ambiguity supplies a common period on the parallelogram
tail. Its half-open cells provide consecutive seeds on every high row,
including all positive multiples of that period. -/

namespace NivatTrial.ColleParallelogramSeeds

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.LatticePolygon
open NivatTrial.Dynamics NivatTrial.Periodicity NivatTrial.BalancedWindows
open NivatTrial.ColleGenerating NivatTrial.ColleAmbiguity
open NivatTrial.ColleSemiAmbiguity NivatTrial.ColleHalfStrip
open NivatTrial.ColleParallelogramGeometry NivatTrial.ColleParallelogramWindow
open NivatTrial.ColleReferencePropagation NivatTrial.RowDetermination
open scoped Classical
noncomputable section

variable {A : Type*} [Fintype A]

theorem supportEdge_card_two_of_semiAmbiguous
    (θ : Lattice → A) (S : Finset Lattice) (k : Lattice)
    (q : Lattice → A) (hq : q ∈ languageHull θ) (τ : ℤ)
    (hamb : SemiAmbiguous θ S (embed k) k q hq τ)
    (hbudget : patternComplexity θ S <
      patternComplexity θ (supportBase S (embed k)) + (supportEdge S (embed k)).card) :
    2 ≤ (supportEdge S (embed k)).card := by
  have hpos : 0 < (ambiguousPatterns θ S (embed k)).card := by
    apply Finset.card_pos.mpr
    let p : patternSet θ (supportBase S (embed k)) :=
      ⟨patternAt q (supportBase S (embed k)) (τ • k),
        patternSet_subset_of_mem_languageHull hq _ ⟨τ • k,rfl⟩⟩
    exact ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hamb τ le_rfl⟩⟩
  have hlt := ambiguity_count_lt_edge θ S (embed k) hbudget
  omega

/-- The seed block is furnished by the actual parallelogram, and one
height threshold works for every multiple of the common period. -/
theorem high_row_seeds_of_semiAmbiguous
    (θ : Lattice → A) (S : Finset Lattice)
    (hS : S.Nonempty) (hconv : IsLatticeConvex S)
    (k : Lattice) (hprim : Int.gcd k.1 k.2 = 1) (hk : 0 < k.2)
    (q : Lattice → A) (hq : q ∈ languageHull θ) (τ : ℤ)
    (hamb : SemiAmbiguous θ S (embed k) k q hq τ)
    (hbudget : patternComplexity θ S <
      patternComplexity θ (supportBase S (embed k)) + (supportEdge S (embed k)).card)
    (hshort : (bottomEdge S).card ≤ (topEdge S).card) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ lo : ℤ,
      ∀ d : ℤ, lo ≤ d → ∃ l : ℤ, ∀ N : ℕ,
        ∀ j : ℤ, l ≤ j → j < l+((bottomEdge S).card-1 : ℕ) →
          q ((j,d)+(N : ℤ)•(Q•k)) = q (j,d) := by
  let L := (bottomEdge S).card-1
  have hbot : L < (bottomEdge S).card := by
    have hh := Finset.card_pos.mpr (bottomEdge_nonempty hS)
    dsimp [L]
    omega
  have htop : L < (topEdge S).card := hbot.trans_le hshort
  have hedge := supportEdge_card_two_of_semiAmbiguous θ S k q hq τ hamb hbudget
  obtain ⟨a,hrun,hrows⟩ := exists_cellAnchors_of_support_edge S hS hconv
    k hprim hk L hbot htop hedge
  obtain ⟨T,Q,hQ,hper⟩ := common_semi_ambiguous_halfStrip_period θ S (embed k) k
    (cellAnchors S a k L) ((supportEdge S (embed k)).card-1) τ hq hamb
    hbudget hrun le_rfl
  let M : ℕ := (τ+(T : ℤ)).toNat
  have hM : τ+(T : ℤ) ≤ (M : ℤ) := by dsimp [M]; omega
  refine ⟨Q,hQ,a.2+(M : ℤ)*k.2,?_⟩
  intro d hd
  obtain ⟨l,n,hn,hseed⟩ := hrows M d hd
  refine ⟨l,?_⟩
  intro N j hjlo hjhi
  let j' : Fin L := ⟨(j-l).toNat,by dsimp [L]; omega⟩
  obtain ⟨w,hw,he⟩ := hseed j'
  have hj : l+(j' : ℤ) = j := by dsimp [j']; omega
  rw [hj] at he
  have hp : TailPeriod (fun i : ℤ => q (w+i•k)) (τ+(T : ℤ)) Q := hper w hw
  have hm := hp.nsmul N n (hM.trans hn)
  change q (w+(n+((N*Q : ℕ) : ℤ))•k) = q (w+n•k) at hm
  have heq : (w+n•k)+(N : ℤ)•(Q•k) = w+(n+((N*Q : ℕ) : ℤ))•k := by
    rw [← natCast_zsmul,smul_smul,Nat.cast_mul,add_smul]
    abel
  rw [he,heq]
  exact hm

/-- This is exactly the consecutive-seed premise of the reference
half-plane propagation theorem, now derived from a generating window. -/
theorem reference_row_seeds_of_semiAmbiguous
    (θ : Lattice → A) (S : Finset Lattice) (hS : GeneratingWindow θ S)
    (k : Lattice) (hprim : Int.gcd k.1 k.2 = 1) (hk : 0 < k.2)
    (q : Lattice → A) (hq : q ∈ languageHull θ) (τ : ℤ)
    (hamb : SemiAmbiguous θ S (embed k) k q hq τ)
    (hshort : (bottomEdge S).card ≤ (topEdge S).card) :
    ∃ Q : ℕ, 0 < Q ∧
      ∀ N : ℕ, 0 < N → ∃ lo : ℤ, ∀ d : ℤ, lo ≤ d → ∃ l : ℤ,
        ∀ j : ℤ, l ≤ j → j < l+((bottomEdge S).card-1 : ℕ) →
          q ((j,d)+(N : ℤ)•(Q•k)) = q (j,d) := by
  obtain ⟨Q,hQ,lo,hseeds⟩ := high_row_seeds_of_semiAmbiguous θ S
    hS.nonempty hS.latticeConvex k hprim hk q hq τ hamb (hS.strict_edge_budget _) hshort
  refine ⟨Q,hQ,?_⟩
  intro N _
  refine ⟨lo,?_⟩
  intro d hd
  obtain ⟨l,hl⟩ := hseeds d hd
  exact ⟨l,hl N⟩

/-- The actual Q-tail geometry closes the seed input of Claim 4.3. -/
theorem reference_halfPlane_period_of_semiAmbiguous
    (θ : Lattice → A) (S : Finset Lattice) (hS : GeneratingWindow θ S)
    (k : Lattice) (hprim : Int.gcd k.1 k.2 = 1) (hk : 0 < k.2)
    (q : Lattice → A) (hq : q ∈ languageHull θ) (τ : ℤ)
    (hamb : SemiAmbiguous θ S (embed k) k q hq τ)
    (hshort : (bottomEdge S).card ≤ (topEdge S).card)
    (P : ℕ) (hP : 0 < P) (hperiod : IsPeriod q (P•horizontal)) :
    ∃ M : ℕ, 0 < M ∧ ∃ lo : ℤ, ∀ z : Lattice, lo ≤ z.2 →
      q (z+(M : ℤ)•k) = q z := by
  obtain ⟨Q,hQ,hseeds⟩ := reference_row_seeds_of_semiAmbiguous θ S hS k hprim hk
    q hq τ hamb hshort
  have hkQ : 0 < (Q•k).2 := by
    change (0 : ℤ) < Q • k.2
    rw [nsmul_eq_mul]
    exact mul_pos (by exact_mod_cast hQ) hk
  obtain ⟨N,hN,lo,hper⟩ := reference_halfPlane_period_of_row_seeds θ S hS
    q hq P hP hperiod (Q•k) hkQ hseeds
  refine ⟨N*Q,Nat.mul_pos hN hQ,lo,?_⟩
  intro z hz
  have hh := hper z hz
  simpa only [← natCast_zsmul,smul_smul,Nat.cast_mul] using hh

end
end NivatTrial.ColleParallelogramSeeds
