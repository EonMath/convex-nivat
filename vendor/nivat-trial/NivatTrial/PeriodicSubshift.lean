import NivatTrial.Dynamics
import Mathlib.Topology.Sequences
import Mathlib.Topology.DiscreteSubset
import Mathlib.Data.Int.LeastGreatest

/-! Compact one-dimensional subshifts consisting entirely of periodic points
are finite. This is the finiteness mechanism used in Lemma 8.16. -/

namespace NivatTrial.PeriodicSubshift

open Set Filter Topology Function
open scoped Classical

variable {B : Type*}

def shift (n : ℤ) (x : ℤ → B) : ℤ → B := fun i => x (i + n)

@[simp] theorem shift_apply (n : ℤ) (x : ℤ → B) (i : ℤ) : shift n x i = x (i + n) := rfl

def PeriodicPoint (x : ℤ → B) : Prop := ∃ q : ℕ, 0 < q ∧ Function.Periodic x (q : ℤ)

theorem periodic_reduce (x : ℤ → B) (q : ℕ) (hq : 0 < q)
    (hp : Function.Periodic x (q : ℤ)) (i : ℤ) : x i = x (i % q) := by
  calc
    x i = x (i % q + (i / q) * q) := congrArg x (Int.emod_add_ediv_mul i (q : ℤ)).symm
    _ = x (i % q) := by simpa using hp.int_mul (i / q) (i % q)

theorem periodic_determined (x y : ℤ → B) (q : ℕ) (hq : 0 < q)
    (hx : Function.Periodic x (q : ℤ)) (hy : Function.Periodic y (q : ℤ))
    (hagree : ∀ i : ℤ, 0 ≤ i → i < q → x i = y i) : x = y := by
  funext i
  rw [periodic_reduce x q hq hx, periodic_reduce y q hq hy]
  exact hagree _ (Int.emod_nonneg _ (by omega)) (Int.emod_lt_of_pos _ (by omega))

theorem periodic_of_halfline (x : ℤ → B) (q : ℤ) (hp : PeriodicPoint x)
    (hhalf : (∀ i : ℤ, i < 0 → x (i + q) = x i) ∨
      (∀ i : ℤ, 0 < i → x (i + q) = x i)) : Function.Periodic x q := by
  obtain ⟨r, hr, hperiod⟩ := hp
  intro i
  rcases hhalf with hleft | hright
  · obtain ⟨N, hN⟩ := exists_nat_gt i
    have hpos : i - (N : ℤ) * r < 0 := by
      have hcast : (1 : ℤ) ≤ r := by exact_mod_cast hr
      have hN0 : (0 : ℤ) ≤ N := by exact_mod_cast Nat.zero_le N
      nlinarith
    have hP := hperiod.nat_mul N
    calc
      x (i + q) = x ((i - (N : ℤ) * r) + q) := by
        convert (hP.sub_eq (i + q)).symm using 1 <;> congr 1 <;> ring
      _ = x (i - (N : ℤ) * r) := hleft _ hpos
      _ = x i := hP.sub_eq i
  · obtain ⟨N, hN⟩ := exists_nat_gt (-i)
    have hpos : 0 < i + (N : ℤ) * r := by
      have hcast : (1 : ℤ) ≤ r := by exact_mod_cast hr
      have hN0 : (0 : ℤ) ≤ N := by exact_mod_cast Nat.zero_le N
      nlinarith
    have hP := hperiod.nat_mul N
    calc
      x (i + q) = x ((i + (N : ℤ) * r) + q) := by
        convert (hP (i + q)).symm using 1 <;> congr 1 <;> ring
      _ = x (i + (N : ℤ) * r) := hright _ hpos
      _ = x i := hP i

/-- Move the closest defect of a proposed period to the origin. A growing
interval on at least one side of the defect remains free of defects. -/
theorem recenter_defect (x : ℤ → B) (q : ℤ) (n : ℕ)
    (hgood : ∀ i : ℤ, -(n : ℤ) ≤ i → i ≤ n → x (i + q) = x i)
    (hbad : ¬Function.Periodic x q) :
    ∃ b : ℤ, shift b x q ≠ shift b x 0 ∧
      ((∀ i : ℤ, -(n : ℤ) ≤ i → i < 0 → shift b x (i + q) = shift b x i) ∨
       (∀ i : ℤ, 0 < i → i ≤ n → shift b x (i + q) = shift b x i)) := by
  have hex : ∃ i : ℤ, x (i + q) ≠ x i := by simpa [Function.Periodic] using hbad
  by_cases hright : ∃ b : ℤ, 0 ≤ b ∧ x (b + q) ≠ x b
  · obtain ⟨b, ⟨hb0, hb⟩, hmin⟩ := Int.exists_least_of_bdd
      ⟨0, fun z hz => hz.1⟩ hright
    have hbn : (n : ℤ) < b := by
      by_contra hn
      exact hb (hgood b (by omega) (by omega))
    refine ⟨b, by simpa [shift, add_comm] using hb, Or.inl ?_⟩
    intro i hi hi0
    have hbi : 0 ≤ i + b := by omega
    have hlt : i + b < b := by omega
    have heq : x ((i + b) + q) = x (i + b) := by
      by_contra hne
      have h := hmin (i + b) ⟨hbi, hne⟩
      omega
    simpa [shift, add_assoc, add_comm, add_left_comm] using heq
  · have hnegative : ∃ b : ℤ, 0 ≤ b ∧ x (-b + q) ≠ x (-b) := by
      obtain ⟨i, hi⟩ := hex
      have hi0 : i < 0 := by
        by_contra hn
        exact hright ⟨i, by omega, hi⟩
      exact ⟨-i, by omega, by simpa using hi⟩
    obtain ⟨b, ⟨hb0, hb⟩, hmin⟩ := Int.exists_least_of_bdd
      ⟨0, fun z hz => hz.1⟩ hnegative
    have hbn : (n : ℤ) < b := by
      by_contra hn
      exact hb (hgood (-b) (by omega) (by omega))
    refine ⟨-b, by simpa [shift, add_comm] using hb, Or.inr ?_⟩
    intro i hi0 hi
    have hbi : 0 ≤ b - i := by omega
    have hlt : b - i < b := by omega
    have heq : x (-(b - i) + q) = x (-(b - i)) := by
      by_contra hne
      have h := hmin (b - i) ⟨hbi, hne⟩
      omega
    simpa [shift, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using heq

section Topology

variable [TopologicalSpace B] [DiscreteTopology B]

theorem eventually_coordinate_eq {x : ℕ → ℤ → B} {y : ℤ → B}
    (h : Tendsto x atTop (𝓝 y)) (i : ℤ) : ∀ᶠ n in atTop, x n i = y i := by
  have hi := (tendsto_pi_nhds.mp h) i
  have hsingle : ({y i} : Set B) ∈ 𝓝 (y i) :=
    (isOpen_discrete _).mem_nhds (Set.mem_singleton _)
  filter_upwards [hi.eventually hsingle] with n hn
  exact Set.mem_singleton_iff.mp hn

/-- A periodic point of a compact, invariant, pointwise periodic subshift is
isolated by agreement on a finite interval. -/
theorem exists_isolating_window (Ω : Set (ℤ → B)) (hcompact : IsCompact Ω)
    (hshift : ∀ b : ℤ, shift b '' Ω = Ω)
    (hperiodic : ∀ y ∈ Ω, PeriodicPoint y) (x : ℤ → B) (hx : x ∈ Ω) :
    ∃ N : ℕ, ∀ y ∈ Ω,
      (∀ i : ℤ, -(N : ℤ) ≤ i → i ≤ N → y i = x i) → y = x := by
  obtain ⟨q, hq, hxp⟩ := hperiodic x hx
  by_contra hnone
  have hex (n : ℕ) : ∃ y : ℤ → B, y ∈ Ω ∧
      (∀ i : ℤ, -((n + q : ℕ) : ℤ) ≤ i → i ≤ n + q → y i = x i) ∧ y ≠ x := by
    by_contra hn
    apply hnone
    refine ⟨n + q, ?_⟩
    intro y hy hagree
    by_contra hne
    exact hn ⟨y, hy, hagree, hne⟩
  choose y hy hagree hne using hex
  have hnotper (n : ℕ) : ¬Function.Periodic (y n) (q : ℤ) := by
    intro hp
    apply hne n
    exact periodic_determined (y n) x q hq hp hxp
      (fun i hi0 hiq => hagree n i (by omega) (by omega))
  have hgood (n : ℕ) (i : ℤ) (hlo : -(n : ℤ) ≤ i) (hhi : i ≤ n) :
      y n (i + q) = y n i := by
    rw [hagree n (i + q) (by omega) (by omega), hagree n i (by omega) (by omega), hxp i]
  choose b hbad hhalf using (fun n => recenter_defect (y n) q n (hgood n) (hnotper n))
  have hmem (n : ℕ) : shift (b n) (y n) ∈ Ω := by
    rw [← hshift (b n)]
    exact ⟨y n, hy n, rfl⟩
  obtain ⟨z, hz, φ, hφ, hlimit⟩ := hcompact.tendsto_subseq hmem
  have heq (i : ℤ) : ∀ᶠ n in atTop, shift (b (φ n)) (y (φ n)) i = z i :=
    eventually_coordinate_eq hlimit i
  have hzbad : z (q : ℤ) ≠ z 0 := by
    intro hequal
    obtain ⟨n, hnq, hn0⟩ := (heq (q : ℤ) |>.and (heq 0)).exists
    exact hbad (φ n) (hnq.trans (hequal.trans hn0.symm))
  have hzone : (∀ i : ℤ, i < 0 → z (i + q) = z i) ∨
      (∀ i : ℤ, 0 < i → z (i + q) = z i) := by
    by_cases hleft : ∀ i : ℤ, i < 0 → z (i + q) = z i
    · exact Or.inl hleft
    · push_neg at hleft
      obtain ⟨i, hi, hzi⟩ := hleft
      refine Or.inr ?_
      intro j hj
      obtain ⟨N, hN⟩ := exists_nat_ge (max (-i) j)
      have hbound : ∀ᶠ n in atTop, N ≤ φ n :=
        hφ.tendsto_atTop.eventually (eventually_ge_atTop N)
      have hresult : ∀ᶠ n : ℕ in atTop, z (j + q) = z j := by
        filter_upwards [hbound, heq i, heq (i + q), heq j, heq (j + q)] with n hn hni hniq hnj hnjq
        have hncast : (N : ℤ) ≤ φ n := by exact_mod_cast hn
        have hbi : -(φ n : ℤ) ≤ i := by have := le_max_left (-i) j; omega
        have hbj : j ≤ (φ n : ℤ) := by have := le_max_right (-i) j; omega
        rcases hhalf (φ n) with hnegative | hpositive
        · have hiq := hnegative i hbi hi
          exact False.elim (hzi (hniq.symm.trans (hiq.trans hni)))
        · exact hnjq.symm.trans ((hpositive j hj hbj).trans hnj)
      exact eventually_const.mp hresult
  have hglobal := periodic_of_halfline z q (hperiodic z hz) hzone
  exact hzbad (by simpa using hglobal 0)

def intervalCylinder (x : ℤ → B) (N : ℕ) : Set (ℤ → B) :=
  {y | ∀ i : ℤ, -(N : ℤ) ≤ i → i ≤ N → y i = x i}

theorem isOpen_intervalCylinder (x : ℤ → B) (N : ℕ) : IsOpen (intervalCylinder x N) := by
  have heq : intervalCylinder x N =
      ⋂ i ∈ Finset.Icc (-(N : ℤ)) N, {y : ℤ → B | y i = x i} := by
    ext y
    simp only [intervalCylinder, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_Icc]
    tauto
  rw [heq]
  apply isOpen_biInter_finset
  intro i hi
  exact (continuous_apply i : Continuous (fun y : ℤ → B => y i)).isOpen_preimage
    ({x i} : Set B) (isOpen_discrete _)

/-- Compact shift-invariant subshifts whose points all have positive periods
are finite; this is proved rather than assumed as a structural input. -/
theorem finite_of_compact_periodic (Ω : Set (ℤ → B)) (hcompact : IsCompact Ω)
    (hshift : ∀ b : ℤ, shift b '' Ω = Ω)
    (hperiodic : ∀ y ∈ Ω, PeriodicPoint y) : Ω.Finite := by
  apply hcompact.finite
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro x hx
  obtain ⟨N, hN⟩ := exists_isolating_window Ω hcompact hshift hperiodic x hx
  refine ⟨intervalCylinder x N, isOpen_intervalCylinder x N, ?_⟩
  ext y
  constructor
  · rintro ⟨hc, hy⟩
    exact Set.mem_singleton_iff.mpr (hN y hy hc)
  · rintro rfl
    exact ⟨fun _ _ _ => rfl, hx⟩

end Topology

end NivatTrial.PeriodicSubshift
