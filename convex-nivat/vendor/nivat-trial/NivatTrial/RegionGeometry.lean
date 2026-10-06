import NivatTrial.SupportGeometry
import NivatTrial.Periodicity

/-! Entry into a convex lattice region and saturation by a component period.
The proofs need only convexity, not a separate recession-cone classification. -/

namespace NivatTrial.RegionGeometry

open NivatTrial.Zonotope NivatTrial.Periodicity NivatTrial.Dynamics
open NivatTrial.Geometry
open scoped Classical

noncomputable section

def LatticeConvexRegion (R : Set Lattice) : Prop :=
  ∃ C : Set Plane, Convex ℝ C ∧ R = embed ⁻¹' C

def ForwardInvariant (R : Set Lattice) (h : Lattice) : Prop := ∀ z ∈ R, z+h ∈ R

theorem ForwardInvariant.nsmul {R : Set Lattice} {h : Lattice}
    (hh : ForwardInvariant R h) (n : ℕ) : ForwardInvariant R (n•h) := by
  intro z hz
  induction n with
  | zero => simpa using hz
  | succ n ih =>
    rw [succ_nsmul, ← add_assoc]
    exact hh (z+n•h) ih

theorem ForwardInvariant.add {R : Set Lattice} {h k : Lattice}
    (hh : ForwardInvariant R h) (hk : ForwardInvariant R k) : ForwardInvariant R (h+k) := by
  intro z hz
  simpa [← add_assoc] using hk (z+h) (hh z hz)

theorem convex_nonnegative_span {C : Set Plane} (hC : Convex ℝ C)
    (x a b : Plane) (hNat : ∀ m n : ℕ, x+(m:ℝ)•a+(n:ℝ)•b ∈ C)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) : x+s•a+t•b ∈ C := by
  obtain ⟨M, hM⟩ := exists_nat_gt s
  obtain ⟨N, hN⟩ := exists_nat_gt t
  have hMpos : (0 : ℝ) < M := lt_of_le_of_lt hs hM
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt ht hN
  have hrow : ∀ n : ℕ, x+s•a+(n:ℝ)•b ∈ C := by
    intro n
    have hx : x+(n:ℝ)•b ∈ C := by simpa using hNat 0 n
    have hy : (x+(n:ℝ)•b)+(M:ℝ)•a ∈ C := by
      simpa only [add_right_comm] using hNat M n
    have hh := hC.add_smul_mem hx hy
      (t := s/(M:ℝ)) ⟨div_nonneg hs hMpos.le, (div_le_one hMpos).mpr hM.le⟩
    simpa only [smul_smul, div_mul_cancel₀ s (ne_of_gt hMpos), add_right_comm] using hh
  have hx : x+s•a ∈ C := by simpa using hrow 0
  have hh := hC.add_smul_mem hx (hrow N)
    (t := t/(N:ℝ)) ⟨div_nonneg ht hNpos.le, (div_le_one hNpos).mpr hN.le⟩
  simpa only [smul_smul, div_mul_cancel₀ t (ne_of_gt hNpos)] using hh

/-- Independent forward translations give a common entry direction for every lattice site. -/
theorem eventual_entry (R : Set Lattice) (hR : LatticeConvexRegion R)
    (hne : R.Nonempty) (a b : Lattice) (hab : det a b ≠ 0)
    (ha : ForwardInvariant R a) (hb : ForwardInvariant R b) :
    ∀ z, ∃ N : ℕ, ∀ n ≥ N, z+n•(a+b) ∈ R := by
  obtain ⟨C, hC, hRC⟩ := hR
  obtain ⟨z₀, hz₀⟩ := hne
  have hcone : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      embed z₀+s•embed a+t•embed b ∈ C := by
    intro s t hs ht
    apply convex_nonnegative_span hC (embed z₀) (embed a) (embed b) _ s t hs ht
    intro m n
    have hz := (hb.nsmul n) (z₀+m•a) ((ha.nsmul m) z₀ hz₀)
    rw [hRC] at hz
    simpa only [Set.mem_preimage, embed_add, embed_nsmul] using hz
  intro z
  let x : ℝ := NivatTrial.Divisibility.longitudinalCoordinate a b (z-z₀)
  let y : ℝ := NivatTrial.Divisibility.transverseCoordinate a b (z-z₀)
  have hxy : x•embed a+y•embed b = embed (z-z₀) :=
    NivatTrial.SupportGeometry.real_coordinates a b (z-z₀) hab
  obtain ⟨N, hN⟩ := exists_nat_gt (max (-x) (-y))
  refine ⟨N, ?_⟩
  intro n hn
  have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 ≤ x+(n:ℝ) := by linarith [le_max_left (-x) (-y)]
  have ht : 0 ≤ y+(n:ℝ) := by linarith [le_max_right (-x) (-y)]
  have hm := hcone (x+n) (y+n) hs ht
  rw [hRC]
  change embed (z+n•(a+b)) ∈ C
  convert hm using 1
  rw [embed_add, embed_nsmul, embed_add, smul_add, add_smul, add_smul]
  rw [embed_sub] at hxy
  have hz : embed z = embed z₀+(x•embed a+y•embed b) := by rw [hxy]; abel
  rw [hz]
  abel

/-- The geometric hypotheses of Lemma 8.2 supply its entry premise. -/
theorem doublyPeriodic_extension {A : Type*} (f : Lattice → A)
    (R : Set Lattice) (hR : LatticeConvexRegion R) (hne : R.Nonempty)
    (a b : Lattice) (hab : det a b ≠ 0)
    (ha : PeriodicOn f R a) (hb : PeriodicOn f R b) :
    ∃ η : Lattice → A, (∀ z ∈ R, η z=f z) ∧
      IsPeriod η a ∧ IsPeriod η b ∧ IsDoublyPeriodic η := by
  apply doublyPeriodic_extension_of_entry f R a b hab ha hb
  intro z
  obtain ⟨N,hN⟩ := eventual_entry R hR hne a b hab ha.1 hb.1 z
  exact ⟨N,hN N le_rfl⟩

def erosion (R : Set Lattice) (E : Finset Lattice) : Set Lattice :=
  {z | ∀ e ∈ E, z+e ∈ R}

theorem erosion_forward {R : Set Lattice} {g : Lattice}
    (hg : ForwardInvariant R g) (E : Finset Lattice) : ForwardInvariant (erosion R E) g := by
  intro z hz e he
  simpa [add_right_comm] using hg (z+e) (hz e he)

theorem erosion_entry {R : Set Lattice} (g : Lattice)
    (hentry : ∀ z, ∃ N : ℕ, ∀ n ≥ N, z+n•g ∈ R) (E : Finset Lattice) :
    ∀ z, ∃ N : ℕ, ∀ n ≥ N, z+n•g ∈ erosion R E := by
  intro z
  choose N hN using fun e : E => hentry (z+e)
  let M := Finset.univ.sup N
  refine ⟨M, ?_⟩
  intro n hn e he
  have hle : N ⟨e,he⟩ ≤ M := Finset.le_sup (f := N) (Finset.mem_univ _)
  simpa [add_right_comm] using hN ⟨e,he⟩ n (hle.trans hn)

/-- A periodic function vanishing on an entering region vanishes on a whole half-plane. -/
theorem vanishing_halfplane {A : Type*} [Zero A] (f : Lattice → A)
    (R : Set Lattice) (h g : Lattice) (hper : IsPeriod f h) (hdet : 0 < det h g)
    (hentry : ∀ z, ∃ N : ℕ, ∀ n ≥ N, z+n•g ∈ R) (hzero : ∀ z ∈ R, f z=0) :
    ∃ c : ℤ, ∀ z, c ≤ det h z → f z=0 := by
  let F := NivatTrial.Divisibility.fundamentalDomain h g
  letI : Fintype F := (NivatTrial.Divisibility.fundamentalDomain_finite h g
    (ne_of_gt hdet)).fintype
  choose N hN using fun r : F => hentry r
  let M := Finset.univ.sup N
  refine ⟨((M:ℤ)+1)*det h g, ?_⟩
  intro z hz
  obtain ⟨r,m,n,heq⟩ := NivatTrial.Divisibility.fundamentalDomain_representatives h g
    (ne_of_gt hdet) z
  have hrbound := (NivatTrial.Divisibility.fundamentalDomain_det_bounds h g
    (ne_of_gt hdet) r.property).1
  change |det h r| ≤ |det h g| at hrbound
  have hr : det h r ≤ det h g := (le_abs_self _).trans (by simpa [abs_of_pos hdet] using hrbound)
  have hzdet : det h z = det h r+n*det h g := by
    rw [heq]
    simp only [det_add_right, det_zsmul_right, det_self, mul_zero, add_zero]
  have hmn : (M : ℤ) ≤ n := by nlinarith
  have hn0 : 0 ≤ n := le_trans (by positivity) hmn
  have hNle : N r ≤ M := Finset.le_sup (f := N) (Finset.mem_univ _)
  have hmem : (r:Lattice)+n.toNat•g ∈ R := hN r n.toNat (by omega)
  have hvalue := (hper.zsmul m) ((r:Lattice)+n•g)
  have hzper : f z = f ((r:Lattice)+n•g) := by
    rw [heq]
    convert hvalue using 1 <;> congr 1 <;> abel
  rw [hzper]
  have hcast : (n.toNat : ℤ)=n := Int.toNat_of_nonneg hn0
  have hs : n.toNat•g = n•g := by rw [← natCast_zsmul, hcast]
  rw [hs] at hmem
  exact hzero _ hmem

theorem vanishing_global {A : Type*} [Zero A] (f : Lattice → A)
    (R : Set Lattice) (g : Lattice) (M : ℕ) (hM : 0 < M)
    (hper : IsPeriod f (M•g))
    (hentry : ∀ z, ∃ N : ℕ, ∀ n ≥ N, z+n•g ∈ R) (hzero : ∀ z ∈ R, f z=0) :
    f=0 := by
  funext z
  obtain ⟨N,hN⟩ := hentry z
  have hNM : N ≤ N*M := Nat.le_mul_of_pos_right N hM
  have hvalue := (hper.nsmul N) z
  rw [smul_smul] at hvalue
  exact hvalue.symm.trans (hzero _ (hN (N*M) hNM))

end
end NivatTrial.RegionGeometry
