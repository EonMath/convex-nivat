import NivatTrial.Dynamics
import NivatTrial.Geometry

/-! Period groups, lattice representatives, and finite-state propagation. -/

namespace NivatTrial.Periodicity

open NivatTrial.Dynamics

section Groups

variable {G A B : Type*} [AddCommGroup G]

/-- A period may be zero; nonzero existence is a separate periodicity statement. -/
def IsPeriod (θ : G → A) (h : G) : Prop := ∀ z, θ (z + h) = θ z

theorem isPeriod_zero (θ : G → A) : IsPeriod θ 0 := by
  intro z
  rw [add_zero]

theorem IsPeriod.add {θ : G → A} {h k : G} (hh : IsPeriod θ h)
    (hk : IsPeriod θ k) : IsPeriod θ (h + k) := by
  intro z
  rw [← add_assoc, hk, hh]

theorem IsPeriod.neg {θ : G → A} {h : G} (hh : IsPeriod θ h) : IsPeriod θ (-h) := by
  intro z
  have hp := hh (z - h)
  simpa [sub_eq_add_neg] using hp.symm

theorem IsPeriod.sub {θ : G → A} {h k : G} (hh : IsPeriod θ h)
    (hk : IsPeriod θ k) : IsPeriod θ (h - k) := by
  simpa [sub_eq_add_neg] using hh.add hk.neg

theorem IsPeriod.nsmul {θ : G → A} {h : G} (hh : IsPeriod θ h) (n : ℕ) :
    IsPeriod θ (n • h) := by
  induction n with
  | zero => simpa using isPeriod_zero θ
  | succ n ih => simpa [succ_nsmul] using ih.add hh

theorem IsPeriod.zsmul {θ : G → A} {h : G} (hh : IsPeriod θ h) (n : ℤ) :
    IsPeriod θ (n • h) := by
  cases n with
  | ofNat n => simpa using hh.nsmul n
  | negSucc n => simpa using (hh.nsmul (n + 1)).neg

/-- All periods form an additive subgroup. -/
def periodGroup (θ : G → A) : AddSubgroup G where
  carrier := {h | IsPeriod θ h}
  zero_mem' := isPeriod_zero θ
  add_mem' := fun hh hk => hh.add hk
  neg_mem' := fun hh => hh.neg

@[simp] theorem mem_periodGroup (θ : G → A) (h : G) :
    h ∈ periodGroup θ ↔ IsPeriod θ h := Iff.rfl

theorem IsPeriod.eq_of_sub {θ : G → A} {x y : G} (h : IsPeriod θ (x - y)) :
    θ x = θ y := by
  have hy := h y
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hy

theorem isPeriod_const (a : A) (h : G) : IsPeriod (fun _ : G => a) h := fun _ => rfl

theorem IsPeriod.encode {θ : G → A} {h : G} (hh : IsPeriod θ h) (f : A → B) :
    IsPeriod (f ∘ θ) h := fun z => congrArg f (hh z)

theorem isPeriod_encode_iff {f : A → B} (hf : Function.Injective f)
    (θ : G → A) (h : G) : IsPeriod (f ∘ θ) h ↔ IsPeriod θ h := by
  exact ⟨fun hp z => hf (hp z), fun hp => hp.encode f⟩

theorem IsPeriod.pair {θ : G → A} {η : G → B} {h : G}
    (hθ : IsPeriod θ h) (hη : IsPeriod η h) : IsPeriod (fun z => (θ z, η z)) h := by
  intro z
  exact Prod.ext (hθ z) (hη z)

theorem isPeriod_pair_iff (θ : G → A) (η : G → B) (h : G) :
    IsPeriod (fun z => (θ z, η z)) h ↔ IsPeriod θ h ∧ IsPeriod η h := by
  constructor
  · intro hp
    exact ⟨fun z => congrArg Prod.fst (hp z), fun z => congrArg Prod.snd (hp z)⟩
  · rintro ⟨hθ, hη⟩
    exact hθ.pair hη

theorem periodGroup_pair (θ : G → A) (η : G → B) :
    periodGroup (fun z => (θ z, η z)) = periodGroup θ ⊓ periodGroup η := by
  ext h
  exact isPeriod_pair_iff θ η h

section AdditiveValues

variable [AddCommGroup A]

theorem IsPeriod.add_config {θ η : G → A} {h : G}
    (hθ : IsPeriod θ h) (hη : IsPeriod η h) : IsPeriod (θ + η) h := by
  intro z
  simp only [Pi.add_apply, hθ z, hη z]

theorem IsPeriod.neg_config {θ : G → A} {h : G}
    (hθ : IsPeriod θ h) : IsPeriod (-θ) h := by
  intro z
  simp only [Pi.neg_apply, hθ z]

theorem IsPeriod.sub_config {θ η : G → A} {h : G}
    (hθ : IsPeriod θ h) (hη : IsPeriod η h) : IsPeriod (θ - η) h := by
  simpa [sub_eq_add_neg] using hθ.add_config hη.neg_config

theorem IsPeriod.sum_config {ι : Type*} (s : Finset ι) (θ : ι → G → A) (h : G)
    (hp : ∀ i ∈ s, IsPeriod (θ i) h) : IsPeriod (∑ i ∈ s, θ i) h := by
  classical
  intro z
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i hi => hp i hi z)

theorem difference_periodic_in_other_direction (θ₁ θ₂ : G → A) (h₁ h₂ : G)
    (h₁per : IsPeriod θ₁ h₁) (h₂per : IsPeriod θ₂ h₂) (s : ℤ) :
    IsPeriod (fun z => (θ₁ + θ₂) (z + s • h₂) - (θ₁ + θ₂) z) h₁ := by
  have hs := h₂per.zsmul s
  intro z
  simp only [Pi.add_apply]
  rw [hs (z + h₁), hs z]
  have heq : z + h₁ + s • h₂ = z + s • h₂ + h₁ := by abel
  rw [heq, h₁per (z + s • h₂), h₁per z]
  abel

theorem propagate_difference_agreement (θ₁ θ₂ : G → A) (h₁ h₂ : G)
    (h₁per : IsPeriod θ₁ h₁) (h₂per : IsPeriod θ₂ h₂)
    (s t : ℤ) {z : G}
    (hz : (θ₁ + θ₂) (z + s • h₂) = (θ₁ + θ₂) z) :
    (θ₁ + θ₂) (z + t • h₁ + s • h₂) = (θ₁ + θ₂) (z + t • h₁) := by
  have hp := (difference_periodic_in_other_direction θ₁ θ₂ h₁ h₂ h₁per h₂per s).zsmul t z
  rw [sub_eq_zero.mpr hz] at hp
  exact sub_eq_zero.mp hp

end AdditiveValues

end Groups

section Lattice

variable {A B : Type*}

theorem isPeriod_iff_shift (θ : Lattice → A) (h : Lattice) :
    IsPeriod θ h ↔ shift h θ = θ := by
  simp only [IsPeriod, funext_iff, shift, add_comm]

theorem IsPeriod.shift {θ : Lattice → A} {h : Lattice} (hp : IsPeriod θ h)
    (u : Lattice) : IsPeriod (shift u θ) h := by
  intro z
  simpa [shift, add_assoc] using hp (u + z)

theorem periodGroup_shift (θ : Lattice → A) (u : Lattice) :
    periodGroup (shift u θ) = periodGroup θ := by
  ext h
  constructor
  · intro hp
    simpa using hp.shift (-u)
  · intro hp
    exact hp.shift u

def IsPeriodic (θ : Lattice → A) : Prop := ∃ h : Lattice, h ≠ 0 ∧ IsPeriod θ h

def IsDoublyPeriodic (θ : Lattice → A) : Prop :=
  ∃ h k : Lattice, Geometry.det h k ≠ 0 ∧ IsPeriod θ h ∧ IsPeriod θ k

theorem IsPeriodic.shift {θ : Lattice → A} (hp : IsPeriodic θ) (u : Lattice) :
    IsPeriodic (shift u θ) := by
  rcases hp with ⟨h, hn, hh⟩
  exact ⟨h, hn, hh.shift u⟩

theorem isPeriodic_shift_iff (θ : Lattice → A) (u : Lattice) :
    IsPeriodic (shift u θ) ↔ IsPeriodic θ := by
  exact ⟨fun hp => by simpa using hp.shift (-u), fun hp => hp.shift u⟩

theorem IsDoublyPeriodic.shift {θ : Lattice → A} (hp : IsDoublyPeriodic θ)
    (u : Lattice) : IsDoublyPeriodic (shift u θ) := by
  rcases hp with ⟨h, k, hd, hh, hk⟩
  exact ⟨h, k, hd, hh.shift u, hk.shift u⟩

theorem IsDoublyPeriodic.isPeriodic {θ : Lattice → A} (hp : IsDoublyPeriodic θ) :
    IsPeriodic θ := by
  rcases hp with ⟨h, k, hd, hh, hk⟩
  refine ⟨h, ?_, hh⟩
  intro hzero
  exact hd (by simp [hzero, Geometry.det])

theorem IsPeriodic.encode {θ : Lattice → A} (hp : IsPeriodic θ) (f : A → B) :
    IsPeriodic (encode f θ) := by
  rcases hp with ⟨h, hn, hh⟩
  exact ⟨h, hn, hh.encode f⟩

theorem isPeriodic_encode_iff {f : A → B} (hf : Function.Injective f)
    (θ : Lattice → A) : IsPeriodic (encode f θ) ↔ IsPeriodic θ := by
  constructor
  · rintro ⟨h, hn, hh⟩
    exact ⟨h, hn, (isPeriod_encode_iff hf θ h).mp hh⟩
  · intro hp
    exact hp.encode f

theorem IsDoublyPeriodic.encode {θ : Lattice → A} (hp : IsDoublyPeriodic θ)
    (f : A → B) : IsDoublyPeriodic (encode f θ) := by
  rcases hp with ⟨h, k, hd, hh, hk⟩
  exact ⟨h, k, hd, hh.encode f, hk.encode f⟩

theorem isDoublyPeriodic_encode_iff {f : A → B} (hf : Function.Injective f)
    (θ : Lattice → A) : IsDoublyPeriodic (encode f θ) ↔ IsDoublyPeriodic θ := by
  constructor
  · rintro ⟨h, k, hd, hh, hk⟩
    exact ⟨h, k, hd, (isPeriod_encode_iff hf θ h).mp hh,
      (isPeriod_encode_iff hf θ k).mp hk⟩
  · intro hp
    exact hp.encode f

theorem common_direction_period {θ : Lattice → A} {η : Lattice → B}
    (v : Lattice) (m n : ℕ) (hm : IsPeriod θ (m • v)) (hn : IsPeriod η (n • v)) :
    IsPeriod (fun z => (θ z, η z)) ((m * n) • v) := by
  have hm' : IsPeriod θ ((m * n) • v) := by
    simpa [smul_smul, mul_comm, mul_assoc] using hm.nsmul n
  have hn' : IsPeriod η ((m * n) • v) := by
    simpa [smul_smul, mul_assoc] using hn.nsmul m
  exact hm'.pair hn'

/-- Cramer's identity supplies a horizontal period from two independent periods. -/
theorem horizontal_period_of_independent {θ : Lattice → A} {h k : Lattice}
    (hh : IsPeriod θ h) (hk : IsPeriod θ k) :
    IsPeriod θ (Geometry.det h k • ((1, 0) : Lattice)) := by
  have heq : Geometry.det h k • ((1, 0) : Lattice) = k.2 • h - h.2 • k := by
    apply Prod.ext <;> simp [Geometry.det, Prod.smul_mk] <;> ring
  rw [heq]
  exact (hh.zsmul k.2).sub (hk.zsmul h.2)

/-- The second Cramer identity supplies a vertical period. -/
theorem vertical_period_of_independent {θ : Lattice → A} {h k : Lattice}
    (hh : IsPeriod θ h) (hk : IsPeriod θ k) :
    IsPeriod θ (Geometry.det h k • ((0, 1) : Lattice)) := by
  have heq : Geometry.det h k • ((0, 1) : Lattice) = h.1 • k - k.1 • h := by
    apply Prod.ext <;> simp [Geometry.det, Prod.smul_mk] <;> ring
  rw [heq]
  exact (hk.zsmul h.1).sub (hh.zsmul k.1)

theorem IsPeriod.abs_zsmul {θ : Lattice → A} {v : Lattice} {n : ℤ}
    (hp : IsPeriod θ (n • v)) : IsPeriod θ (|n| • v) := by
  by_cases hn : 0 ≤ n
  · simpa [abs_of_nonneg hn] using hp
  · simpa [abs_of_neg (lt_of_not_ge hn), neg_smul] using hp.neg

theorem rectangular_periods_of_doublyPeriodic {θ : Lattice → A}
    (hp : IsDoublyPeriodic θ) : ∃ n : ℕ, 0 < n ∧
      IsPeriod θ (n • ((1, 0) : Lattice)) ∧ IsPeriod θ (n • ((0, 1) : Lattice)) := by
  rcases hp with ⟨h, k, hd, hh, hk⟩
  refine ⟨(Geometry.det h k).natAbs, Int.natAbs_pos.mpr hd, ?_, ?_⟩
  · change IsPeriod θ (((Geometry.det h k).natAbs : ℤ) • ((1, 0) : Lattice))
    rw [Int.natCast_natAbs]
    exact (horizontal_period_of_independent hh hk).abs_zsmul
  · change IsPeriod θ (((Geometry.det h k).natAbs : ℤ) • ((0, 1) : Lattice))
    rw [Int.natCast_natAbs]
    exact (vertical_period_of_independent hh hk).abs_zsmul

section ClosedPeriods

variable [TopologicalSpace A] [DiscreteTopology A]

/-- A fixed period passes to every point of the orbit closure. -/
theorem IsPeriod.orbitClosure {θ ξ : Lattice → A} {h : Lattice}
    (hp : IsPeriod θ h) (hξ : ξ ∈ orbitClosure θ) : IsPeriod ξ h := by
  classical
  intro z
  obtain ⟨u, hu⟩ := (mem_orbitClosure_iff_finite_agreement θ ξ).mp hξ {z, z + h}
  calc
    ξ (z + h) = θ (u + (z + h)) := (hu _ (by simp)).symm
    _ = θ (u + z) := by simpa [add_assoc] using hp (u + z)
    _ = ξ z := hu _ (by simp)

theorem periodGroup_le_of_mem_orbitClosure {θ ξ : Lattice → A}
    (hξ : ξ ∈ orbitClosure θ) : periodGroup θ ≤ periodGroup ξ :=
  fun _ hp => hp.orbitClosure hξ

theorem IsPeriodic.orbitClosure {θ ξ : Lattice → A} (hp : IsPeriodic θ)
    (hξ : ξ ∈ orbitClosure θ) : IsPeriodic ξ := by
  rcases hp with ⟨h, hn, hh⟩
  exact ⟨h, hn, hh.orbitClosure hξ⟩

theorem IsDoublyPeriodic.orbitClosure {θ ξ : Lattice → A} (hp : IsDoublyPeriodic θ)
    (hξ : ξ ∈ orbitClosure θ) : IsDoublyPeriodic ξ := by
  rcases hp with ⟨h, k, hd, hh, hk⟩
  exact ⟨h, k, hd, hh.orbitClosure hξ, hk.orbitClosure hξ⟩

end ClosedPeriods

end Lattice

section FiniteState

variable {X : Type*} [Finite X]

/-- Equality propagates in both directions under forward and backward determinacy. -/
theorem finite_state_propagate (σ : ℤ → X)
    (hforward : ∀ i j, σ i = σ j → σ (i + 1) = σ (j + 1))
    (hbackward : ∀ i j, σ i = σ j → σ (i - 1) = σ (j - 1))
    {i j : ℤ} (hij : σ i = σ j) (k : ℤ) : σ (i + k) = σ (j + k) := by
  induction k using Int.induction_on with
  | zero => simpa using hij
  | succ n ih =>
    convert hforward (i + n) (j + n) ih using 1 <;> congr 1 <;> omega
  | pred n ih =>
    have ih' : σ (i - n) = σ (j - n) := by simpa [sub_eq_add_neg] using ih
    convert hbackward (i - n) (j - n) ih' using 1 <;> congr 1 <;> omega

/-- A bi-infinite finite-state sequence with determinacy in both directions is periodic. -/
theorem finite_state_periodic (σ : ℤ → X)
    (hforward : ∀ i j, σ i = σ j → σ (i + 1) = σ (j + 1))
    (hbackward : ∀ i j, σ i = σ j → σ (i - 1) = σ (j - 1)) :
    ∃ q : ℕ, 0 < q ∧ ∀ i : ℤ, σ (i + q) = σ i := by
  obtain ⟨m, n, hmn, hne⟩ := Function.not_injective_iff.mp
    (not_injective_infinite_finite (fun n : ℕ => σ n))
  wlog hlt : m < n generalizing m n
  · exact this n m hmn.symm hne.symm (lt_of_le_of_ne (le_of_not_gt hlt) hne.symm)
  refine ⟨n - m, Nat.sub_pos_of_lt hlt, ?_⟩
  intro i
  have hp := finite_state_propagate σ hforward hbackward hmn (i - m)
  have hcast : ((n - m : ℕ) : ℤ) = (n : ℤ) - m := Int.ofNat_sub (le_of_lt hlt)
  rw [hcast]
  convert hp.symm using 1 <;> congr 1 <;> omega

end FiniteState

section LatticeCovering

variable {A : Type*}

/-- A finite square of representatives for coordinate-axis periods. -/
noncomputable def representativeSquare (n : ℕ) : Finset Lattice :=
  (Finset.Ico (0 : ℤ) n).product (Finset.Ico (0 : ℤ) n)

def squareRepresentative (n : ℕ) (z : Lattice) : Lattice :=
  (z.1 % (n : ℤ), z.2 % (n : ℤ))

theorem squareRepresentative_mem {n : ℕ} (hn : 0 < n) (z : Lattice) :
    squareRepresentative n z ∈ representativeSquare n := by
  have hnz : 0 < (n : ℤ) := by exact_mod_cast hn
  apply Finset.mem_product.mpr
  constructor <;> apply Finset.mem_Ico.mpr
  · exact ⟨Int.emod_nonneg _ (ne_of_gt hnz), Int.emod_lt_of_pos _ hnz⟩
  · exact ⟨Int.emod_nonneg _ (ne_of_gt hnz), Int.emod_lt_of_pos _ hnz⟩

/-- The difference from the finite representative is an integral combination of periods. -/
theorem squareRepresentative_difference (n : ℕ) (z : Lattice) :
    z - squareRepresentative n z =
      (z.1 / (n : ℤ)) • (n • ((1, 0) : Lattice)) +
      (z.2 / (n : ℤ)) • (n • ((0, 1) : Lattice)) := by
  apply Prod.ext
  · simp [squareRepresentative, Prod.smul_mk]
    nlinarith [Int.emod_add_mul_ediv z.1 (n : ℤ)]
  · simp [squareRepresentative, Prod.smul_mk]
    nlinarith [Int.emod_add_mul_ediv z.2 (n : ℤ)]

theorem period_difference_squareRepresentative (θ : Lattice → A) (n : ℕ)
    (hhor : IsPeriod θ (n • ((1, 0) : Lattice)))
    (hver : IsPeriod θ (n • ((0, 1) : Lattice))) (z : Lattice) :
    IsPeriod θ (z - squareRepresentative n z) := by
  rw [squareRepresentative_difference]
  exact (hhor.zsmul _).add (hver.zsmul _)

theorem value_eq_squareRepresentative (θ : Lattice → A) (n : ℕ)
    (hhor : IsPeriod θ (n • ((1, 0) : Lattice)))
    (hver : IsPeriod θ (n • ((0, 1) : Lattice))) (z : Lattice) :
    θ z = θ (squareRepresentative n z) :=
  (period_difference_squareRepresentative θ n hhor hver z).eq_of_sub

theorem shift_eq_squareRepresentative (θ : Lattice → A) (n : ℕ)
    (hhor : IsPeriod θ (n • ((1, 0) : Lattice)))
    (hver : IsPeriod θ (n • ((0, 1) : Lattice))) (z : Lattice) :
    shift z θ = shift (squareRepresentative n z) θ := by
  funext u
  change θ (z + u) = θ (squareRepresentative n z + u)
  apply IsPeriod.eq_of_sub
  have hp := period_difference_squareRepresentative θ n hhor hver z
  convert hp using 1
  abel

/-- Two independent periods give an actual finite cover of all translates. -/
theorem finite_orbit_of_doublyPeriodic (θ : Lattice → A) (hp : IsDoublyPeriodic θ) :
    (orbit θ).Finite := by
  obtain ⟨n, hn, hhor, hver⟩ := rectangular_periods_of_doublyPeriodic hp
  have hsub : orbit θ ⊆ (fun z => shift z θ) '' (representativeSquare n : Set Lattice) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨squareRepresentative n z, squareRepresentative_mem hn z,
      (shift_eq_squareRepresentative θ n hhor hver z).symm⟩
  exact ((representativeSquare n).finite_toSet.image _).subset hsub

theorem finite_range_of_doublyPeriodic (θ : Lattice → A) (hp : IsDoublyPeriodic θ) :
    (Set.range θ).Finite := by
  obtain ⟨n, hn, hhor, hver⟩ := rectangular_periods_of_doublyPeriodic hp
  have hsub : Set.range θ ⊆ θ '' (representativeSquare n : Set Lattice) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨squareRepresentative n z, squareRepresentative_mem hn z,
      (value_eq_squareRepresentative θ n hhor hver z).symm⟩
  exact ((representativeSquare n).finite_toSet.image _).subset hsub

theorem orbitClosure_eq_orbit_of_doublyPeriodic [TopologicalSpace A] [DiscreteTopology A]
    (θ : Lattice → A) (hp : IsDoublyPeriodic θ) : orbitClosure θ = orbit θ := by
  exact (finite_orbit_of_doublyPeriodic θ hp).isClosed.closure_eq

theorem mem_orbitClosure_iff_translate_of_doublyPeriodic
    [TopologicalSpace A] [DiscreteTopology A] (θ ξ : Lattice → A)
    (hp : IsDoublyPeriodic θ) : ξ ∈ orbitClosure θ ↔ ∃ u, shift u θ = ξ := by
  rw [orbitClosure_eq_orbit_of_doublyPeriodic θ hp]
  rfl

end LatticeCovering

section CommonPeriods

variable {ι A : Type*} [Fintype ι]

/-- A finite family of doubly periodic fields shares nonzero rectangular periods. -/
theorem common_rectangular_periods (θ : ι → Lattice → A)
    (hp : ∀ i, IsDoublyPeriodic (θ i)) : ∃ n : ℕ, 0 < n ∧ ∀ i,
      IsPeriod (θ i) (n • ((1, 0) : Lattice)) ∧
      IsPeriod (θ i) (n • ((0, 1) : Lattice)) := by
  classical
  choose n hn hhor hver using fun i => rectangular_periods_of_doublyPeriodic (hp i)
  let N := ∏ i, n i
  have hN : 0 < N := Finset.prod_pos (fun i _ => hn i)
  refine ⟨N, hN, ?_⟩
  intro i
  have hdiv : n i ∣ N := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  obtain ⟨k, hk⟩ := hdiv
  constructor
  · rw [hk]
    simpa only [mul_comm (n i) k, mul_smul] using (hhor i).nsmul k
  · rw [hk]
    simpa only [mul_comm (n i) k, mul_smul] using (hver i).nsmul k

theorem common_nonzero_period (θ : ι → Lattice → A)
    (hp : ∀ i, IsDoublyPeriodic (θ i)) : ∃ h : Lattice, h ≠ 0 ∧ ∀ i, IsPeriod (θ i) h := by
  obtain ⟨n, hn, hp⟩ := common_rectangular_periods θ hp
  refine ⟨n • ((1, 0) : Lattice), ?_, fun i => (hp i).1⟩
  intro hz
  have hfst := congrArg Prod.fst hz
  simp only [Prod.smul_mk, Prod.fst, nsmul_eq_mul, mul_one, Prod.fst_zero] at hfst
  exact Nat.ne_of_gt hn (by exact_mod_cast hfst)

theorem doublyPeriodic_sum [AddCommGroup A] (θ : ι → Lattice → A)
    (hp : ∀ i, IsDoublyPeriodic (θ i)) : IsDoublyPeriodic (∑ i, θ i) := by
  obtain ⟨n, hn, hp⟩ := common_rectangular_periods θ hp
  refine ⟨n • ((1, 0) : Lattice), n • ((0, 1) : Lattice), ?_, ?_, ?_⟩
  · simp [Geometry.det, Prod.smul_mk]
    exact_mod_cast Nat.ne_of_gt hn
  · exact IsPeriod.sum_config Finset.univ θ _ (fun i _ => (hp i).1)
  · exact IsPeriod.sum_config Finset.univ θ _ (fun i _ => (hp i).2)

end CommonPeriods

section RegionExtension

variable {A : Type*}

/-- Periodicity on a forward-invariant region includes the domain-preservation condition. -/
def PeriodicOn (θ : Lattice → A) (R : Set Lattice) (h : Lattice) : Prop :=
  (∀ z ∈ R, z + h ∈ R) ∧ ∀ z ∈ R, θ (z + h) = θ z

theorem PeriodicOn.nsmul {θ : Lattice → A} {R : Set Lattice} {h : Lattice}
    (hp : PeriodicOn θ R h) (n : ℕ) : PeriodicOn θ R (n • h) := by
  induction n with
  | zero => constructor <;> simpa
  | succ n ih =>
    constructor
    · intro z hz
      simpa only [succ_nsmul, add_assoc] using hp.1 (z + n • h) (ih.1 z hz)
    · intro z hz
      simpa only [succ_nsmul, add_assoc] using
        (hp.2 (z + n • h) (ih.1 z hz)).trans (ih.2 z hz)

theorem PeriodicOn.add {θ : Lattice → A} {R : Set Lattice} {h k : Lattice}
    (hh : PeriodicOn θ R h) (hk : PeriodicOn θ R k) : PeriodicOn θ R (h + k) := by
  constructor
  · intro z hz
    simpa [add_assoc] using hk.1 (z + h) (hh.1 z hz)
  · intro z hz
    simpa [add_assoc] using (hk.2 (z + h) (hh.1 z hz)).trans (hh.2 z hz)

theorem PeriodicOn.value_eq_after_entry {θ : Lattice → A} {R : Set Lattice} {g : Lattice}
    (hp : PeriodicOn θ R g) (z : Lattice) {m n : ℕ}
    (hm : z + m • g ∈ R) (hn : z + n • g ∈ R) :
    θ (z + m • g) = θ (z + n • g) := by
  wlog hmn : m ≤ n generalizing m n
  · exact (this hn hm (le_of_not_ge hmn)).symm
  have heq : z + n • g = (z + m • g) + (n - m) • g := by
    rw [add_assoc, ← add_nsmul, Nat.add_sub_of_le hmn]
  rw [heq]
  exact ((hp.nsmul (n - m)).2 (z + m • g) hm).symm

/-- The extension uses a chosen entry time; independence is proved separately. -/
noncomputable def regionExtension (θ : Lattice → A) (R : Set Lattice) (g : Lattice)
    (hentry : ∀ z, ∃ n : ℕ, z + n • g ∈ R) : Lattice → A :=
  fun z => θ (z + (hentry z).choose • g)

theorem regionExtension_eq_entry (θ : Lattice → A) (R : Set Lattice) (g : Lattice)
    (hentry : ∀ z, ∃ n : ℕ, z + n • g ∈ R) (hp : PeriodicOn θ R g)
    (z : Lattice) (n : ℕ) (hn : z + n • g ∈ R) :
    regionExtension θ R g hentry z = θ (z + n • g) :=
  hp.value_eq_after_entry z (hentry z).choose_spec hn

theorem regionExtension_agrees (θ : Lattice → A) (R : Set Lattice) (g : Lattice)
    (hentry : ∀ z, ∃ n : ℕ, z + n • g ∈ R) (hp : PeriodicOn θ R g) :
    ∀ z ∈ R, regionExtension θ R g hentry z = θ z := by
  intro z hz
  simpa using regionExtension_eq_entry θ R g hentry hp z 0 (by simpa using hz)

theorem regionExtension_period (θ : Lattice → A) (R : Set Lattice) (g : Lattice)
    (hentry : ∀ z, ∃ n : ℕ, z + n • g ∈ R) (hg : PeriodicOn θ R g)
    (h : Lattice) (hh : PeriodicOn θ R h) : IsPeriod (regionExtension θ R g hentry) h := by
  intro z
  obtain ⟨n, hn⟩ := hentry z
  have hnh : z + h + n • g ∈ R := by
    have heq : z + h + n • g = (z + n • g) + h := by abel
    rw [heq]
    exact hh.1 _ hn
  rw [regionExtension_eq_entry θ R g hentry hg (z + h) n hnh,
    regionExtension_eq_entry θ R g hentry hg z n hn]
  have heq : z + h + n • g = (z + n • g) + h := by abel
  rw [heq]
  exact hh.2 _ hn

/-- The constructive extension part of Lemma 8.2. -/
theorem doublyPeriodic_extension_of_entry (θ : Lattice → A) (R : Set Lattice)
    (h k : Lattice) (hd : Geometry.det h k ≠ 0)
    (hh : PeriodicOn θ R h) (hk : PeriodicOn θ R k)
    (hentry : ∀ z, ∃ n : ℕ, z + n • (h + k) ∈ R) :
    ∃ η : Lattice → A, (∀ z ∈ R, η z = θ z) ∧
      IsPeriod η h ∧ IsPeriod η k ∧ IsDoublyPeriodic η := by
  let η := regionExtension θ R (h + k) hentry
  have hg := hh.add hk
  have hηh := regionExtension_period θ R (h + k) hentry hg h hh
  have hηk := regionExtension_period θ R (h + k) hentry hg k hk
  exact ⟨η, regionExtension_agrees θ R (h + k) hentry hg, hηh, hηk,
    ⟨h, k, hd, hηh, hηk⟩⟩

end RegionExtension

section Normalization

variable {A B ι : Type*} [Fintype ι]

theorem lattice_coordinate_decomposition (v : Lattice) :
    v.1 • ((1, 0) : Lattice) + v.2 • ((0, 1) : Lattice) = v := by
  apply Prod.ext <;> simp [Prod.smul_mk]

/-- Rectangular periods preserve every direction after the same scaling. -/
theorem period_in_scaled_direction (θ : Lattice → A) (n : ℕ) (v : Lattice)
    (hhor : IsPeriod θ (n • ((1, 0) : Lattice)))
    (hver : IsPeriod θ (n • ((0, 1) : Lattice))) : IsPeriod θ (n • v) := by
  have heq : n • v = v.1 • (n • ((1, 0) : Lattice)) +
      v.2 • (n • ((0, 1) : Lattice)) := by
    apply Prod.ext <;> simp [Prod.smul_mk, mul_comm]
  rw [heq]
  exact (hhor.zsmul _).add (hver.zsmul _)

theorem nsmul_lattice_ne_zero {v : Lattice} (hv : v ≠ 0) {n : ℕ} (hn : 0 < n) :
    n • v ≠ 0 := by
  intro hzero
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  apply hv
  apply Prod.ext
  · have hx := congrArg Prod.fst hzero
    simp only [Prod.smul_fst, nsmul_eq_mul, Prod.fst_zero] at hx
    exact (mul_eq_zero.mp hx).resolve_left hnz
  · have hy := congrArg Prod.snd hzero
    simp only [Prod.smul_snd, nsmul_eq_mul, Prod.snd_zero] at hy
    exact (mul_eq_zero.mp hy).resolve_left hnz

/-- Section 0.3's common choice must preserve the component as well as all tail fields. -/
theorem synchronize_direction_period (F : Lattice → A) (tails : ι → Lattice → B)
    (v : Lattice) (k : ℕ) (hk : 0 < k) (hF : IsPeriod F (k • v))
    (htails : ∀ i, IsDoublyPeriodic (tails i)) :
    ∃ κ : ℕ, 0 < κ ∧ k ∣ κ ∧ IsPeriod F (κ • v) ∧
      ∀ i, IsPeriod (tails i) (κ • v) := by
  obtain ⟨N, hN, hp⟩ := common_rectangular_periods tails htails
  refine ⟨k * N, Nat.mul_pos hk hN, ⟨N, rfl⟩, ?_, ?_⟩
  · simpa only [mul_comm k N, mul_smul] using hF.nsmul N
  · intro i
    have hdir := period_in_scaled_direction (tails i) N v (hp i).1 (hp i).2
    simpa only [mul_smul] using hdir.nsmul k

theorem synchronized_nonzero_vector (F : Lattice → A) (tails : ι → Lattice → B)
    (v : Lattice) (hv : v ≠ 0) (k : ℕ) (hk : 0 < k) (hF : IsPeriod F (k • v))
    (htails : ∀ i, IsDoublyPeriodic (tails i)) :
    ∃ H : Lattice, H ≠ 0 ∧ IsPeriod F H ∧ (∀ i, IsPeriod (tails i) H) ∧
      ∃ κ : ℕ, 0 < κ ∧ k ∣ κ ∧ H = κ • v := by
  obtain ⟨κ, hκ, hkκ, hFκ, htailκ⟩ := synchronize_direction_period F tails v k hk hF htails
  exact ⟨κ • v, nsmul_lattice_ne_zero hv hκ, hFκ, htailκ, κ, hκ, hkκ, rfl⟩

end Normalization

section StripPropagation

variable {A : Type*} [AddCommGroup A]

def coordinateStrip (π : Lattice →+ ℤ) (a b : ℤ) : Set Lattice :=
  {z | a ≤ π z ∧ π z ≤ b}

theorem strip_invariant_under_kernel (π : Lattice →+ ℤ) (a b : ℤ) (h : Lattice)
    (hh : π h = 0) : ∀ z ∈ coordinateStrip π a b, z + h ∈ coordinateStrip π a b := by
  intro z hz
  simpa [coordinateStrip, map_add, hh] using hz

/-- Every orbit of a transverse period meets a strip of at least one period's width. -/
theorem transverse_orbit_meets_strip (π : Lattice →+ ℤ) (h : Lattice)
    (hh : 0 < π h) (a b : ℤ) (hwidth : π h ≤ b - a) (z : Lattice) :
    ∃ s : ℤ, z + s • h ∈ coordinateStrip π a b := by
  let s : ℤ := -((π z - a) / π h)
  refine ⟨s, ?_⟩
  have hid : π (z + s • h) = a + (π z - a) % π h := by
    simp only [map_add, map_zsmul, smul_eq_mul, s]
    nlinarith [Int.emod_add_mul_ediv (π z - a) (π h)]
  have hrem0 := Int.emod_nonneg (π z - a) (ne_of_gt hh)
  have hrem1 := Int.emod_lt_of_pos (π z - a) hh
  change a ≤ π (z + s • h) ∧ π (z + s • h) ≤ b
  rw [hid]
  omega

theorem period_of_zero_on_transverse_strip (ψ : Lattice → A) (π : Lattice →+ ℤ)
    (h : Lattice) (hperiod : IsPeriod ψ h) (hh : 0 < π h) (a b : ℤ)
    (hwidth : π h ≤ b - a) (hzero : ∀ z ∈ coordinateStrip π a b, ψ z = 0) :
    ψ = 0 := by
  funext z
  obtain ⟨s, hs⟩ := transverse_orbit_meets_strip π h hh a b hwidth z
  have heq := hperiod.zsmul s z
  exact heq.symm.trans (hzero _ hs)

/-- Appendix D.3: the periodic difference vanishing on a wide strip vanishes globally. -/
theorem periodic_sum_of_strip (θ₁ θ₂ : Lattice → A) (π : Lattice →+ ℤ)
    (u h₂ : Lattice) (c₁ q : ℕ)
    (h₁per : IsPeriod θ₁ (c₁ • u)) (h₂per : IsPeriod θ₂ h₂)
    (hπu : π u = 0) (hπh₂ : 0 < π h₂) (a b : ℤ)
    (hwidth : π h₂ ≤ b - a)
    (hstrip : ∀ z ∈ coordinateStrip π a b,
      (θ₁ + θ₂) (z + q • u) = (θ₁ + θ₂) z) :
    IsPeriod (θ₁ + θ₂) ((q * c₁) • u) := by
  let θ := θ₁ + θ₂
  have hπqu : π (q • u) = 0 := by simp only [map_nsmul, hπu, smul_zero]
  have hlocal : PeriodicOn θ (coordinateStrip π a b) (q • u) :=
    ⟨strip_invariant_under_kernel π a b _ hπqu, hstrip⟩
  have hlocal' : PeriodicOn θ (coordinateStrip π a b) ((q * c₁) • u) := by
    simpa only [mul_comm q c₁, mul_smul] using hlocal.nsmul c₁
  have hθ₁ : IsPeriod θ₁ ((q * c₁) • u) := by
    simpa only [mul_smul] using h₁per.nsmul q
  let ψ : Lattice → A := fun z => θ (z + (q * c₁) • u) - θ z
  have hψ : IsPeriod ψ h₂ := by
    intro z
    simp only [ψ, θ, Pi.add_apply]
    have heq : z + h₂ + (q * c₁) • u = z + (q * c₁) • u + h₂ := by abel
    rw [hθ₁ (z + h₂), hθ₁ z, heq, h₂per (z + (q * c₁) • u), h₂per z]
    abel
  have hz : ∀ z ∈ coordinateStrip π a b, ψ z = 0 := by
    intro z hz
    exact sub_eq_zero.mpr (hlocal'.2 z hz)
  have hglobal := period_of_zero_on_transverse_strip ψ π h₂ hψ hπh₂ a b hwidth hz
  intro z
  exact sub_eq_zero.mp (congrFun hglobal z)

theorem periodic_of_strip_for_two_components (θ₁ θ₂ : Lattice → A)
    (π : Lattice →+ ℤ) (u h₂ : Lattice) (hu : u ≠ 0) (c₁ q : ℕ)
    (hc₁ : 0 < c₁) (hq : 0 < q)
    (h₁per : IsPeriod θ₁ (c₁ • u)) (h₂per : IsPeriod θ₂ h₂)
    (hπu : π u = 0) (hπh₂ : 0 < π h₂) (a b : ℤ)
    (hwidth : π h₂ ≤ b - a)
    (hstrip : ∀ z ∈ coordinateStrip π a b,
      (θ₁ + θ₂) (z + q • u) = (θ₁ + θ₂) z) : IsPeriodic (θ₁ + θ₂) :=
  ⟨(q * c₁) • u, nsmul_lattice_ne_zero hu (Nat.mul_pos hq hc₁),
    periodic_sum_of_strip θ₁ θ₂ π u h₂ c₁ q h₁per h₂per hπu hπh₂ a b hwidth hstrip⟩

end StripPropagation

section FiniteIndex

variable {A : Type*}

/-- The finite representative cover proves finite index of the actual period subgroup. -/
theorem finite_period_quotient (θ : Lattice → A) (hp : IsDoublyPeriodic θ) :
    Finite (Lattice ⧸ periodGroup θ) := by
  classical
  obtain ⟨n, hn, hhor, hver⟩ := rectangular_periods_of_doublyPeriodic hp
  let f : representativeSquare n → Lattice ⧸ periodGroup θ := fun r => r.val
  apply Finite.of_surjective f
  intro q
  refine Quotient.inductionOn' q ?_
  intro z
  refine ⟨⟨squareRepresentative n z, squareRepresentative_mem hn z⟩, ?_⟩
  change (squareRepresentative n z : Lattice ⧸ periodGroup θ) = (z : Lattice ⧸ periodGroup θ)
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  change IsPeriod θ (squareRepresentative n z - z)
  simpa only [neg_sub] using (period_difference_squareRepresentative θ n hhor hver z).neg

theorem finiteIndex_periodGroup (θ : Lattice → A) (hp : IsDoublyPeriodic θ) :
    (periodGroup θ).FiniteIndex := by
  letI := finite_period_quotient θ hp
  exact AddSubgroup.finiteIndex_of_finite_quotient

end FiniteIndex

section RationalHalfPlaneExtension

variable {A : Type*}

def heightHalfPlane (π : Lattice →+ ℤ) (c : ℤ) : Set Lattice := {z | c ≤ π z}

theorem forward_halfplane_period_nonneg (θ : Lattice → A) (π : Lattice →+ ℤ)
    (c : ℤ) (h : Lattice) (hne : (heightHalfPlane π c).Nonempty)
    (hp : PeriodicOn θ (heightHalfPlane π c) h) : 0 ≤ π h := by
  obtain ⟨z, hz⟩ := hne
  change c ≤ π z at hz
  by_contra hn
  have hneg : π h ≤ -1 := by omega
  let N := (π z - c).natAbs + 1
  have hN : (N : ℤ) = π z - c + 1 := by
    simp only [N, Nat.cast_add, Nat.cast_one, Int.natCast_natAbs, abs_of_nonneg (sub_nonneg.mpr hz)]
  have hentry := (hp.nsmul N).1 z (show z ∈ heightHalfPlane π c from hz)
  change c ≤ π (z + N • h) at hentry
  rw [map_add, map_nsmul] at hentry
  simp only [nsmul_eq_mul] at hentry
  have hNpos : 0 < (N : ℤ) := by omega
  nlinarith

theorem nonzero_height_on_independent_pair (π : Lattice →+ ℤ) (h k : Lattice)
    (hπ : π ≠ 0) (hd : Geometry.det h k ≠ 0) : π h ≠ 0 ∨ π k ≠ 0 := by
  by_contra hn
  push_neg at hn
  have hh : IsPeriod π h := by intro z; simp [map_add, hn.1]
  have hk : IsPeriod π k := by intro z; simp [map_add, hn.2]
  have hhor := horizontal_period_of_independent hh hk 0
  have hver := vertical_period_of_independent hh hk 0
  simp only [zero_add, map_zsmul, map_zero, smul_eq_mul] at hhor hver
  have hx : π ((1, 0) : Lattice) = 0 := (mul_eq_zero.mp hhor).resolve_left hd
  have hy : π ((0, 1) : Lattice) = 0 := (mul_eq_zero.mp hver).resolve_left hd
  apply hπ
  ext z
  rw [← lattice_coordinate_decomposition z, map_add, map_zsmul, map_zsmul, hx, hy]
  simp

/-- A positive height direction eventually enters every rational half-plane. -/
theorem positive_direction_enters_halfplane (π : Lattice →+ ℤ) (c : ℤ) (g : Lattice)
    (hg : 0 < π g) (z : Lattice) : ∃ N : ℕ, ∀ n ≥ N, z + n • g ∈ heightHalfPlane π c := by
  let N := (c - π z).natAbs
  have hdelta : c - π z ≤ (N : ℤ) := by
    simpa only [N, Int.natCast_natAbs] using le_abs_self (c - π z)
  refine ⟨N, ?_⟩
  intro n hn
  have hnn : (N : ℤ) ≤ n := by exact_mod_cast hn
  have hnzero : 0 ≤ (n : ℤ) := by omega
  change c ≤ π (z + n • g)
  rw [map_add, map_nsmul]
  simp only [nsmul_eq_mul]
  nlinarith

/-- Lemma 8.2 for half-planes whose normal is an integer height homomorphism. -/
theorem doublyPeriodic_extension_halfplane (θ : Lattice → A) (π : Lattice →+ ℤ)
    (c : ℤ) (h k : Lattice) (hπ : π ≠ 0) (hd : Geometry.det h k ≠ 0)
    (hne : (heightHalfPlane π c).Nonempty)
    (hh : PeriodicOn θ (heightHalfPlane π c) h)
    (hk : PeriodicOn θ (heightHalfPlane π c) k) :
    ∃ η : Lattice → A, (∀ z ∈ heightHalfPlane π c, η z = θ z) ∧
      IsPeriod η h ∧ IsPeriod η k ∧ IsDoublyPeriodic η := by
  have hnonneg := forward_halfplane_period_nonneg θ π c h hne hh
  have knonneg := forward_halfplane_period_nonneg θ π c k hne hk
  have hpair := nonzero_height_on_independent_pair π h k hπ hd
  have hsum : 0 < π (h + k) := by rw [map_add]; omega
  apply doublyPeriodic_extension_of_entry θ (heightHalfPlane π c) h k hd hh hk
  intro z
  obtain ⟨N, hN⟩ := positive_direction_enters_halfplane π c (h + k) hsum z
  exact ⟨N, hN N le_rfl⟩

end RationalHalfPlaneExtension

section FiniteOrbitCharacterization

variable {A : Type*}

/-- A finite orbit forces a positive multiple of every direction to be a period. -/
theorem direction_period_of_finite_orbit (θ : Lattice → A) (v : Lattice)
    (hfinite : (orbit θ).Finite) : ∃ n : ℕ, 0 < n ∧ IsPeriod θ (n • v) := by
  classical
  letI : Fintype (orbit θ) := hfinite.fintype
  let f : ℕ → orbit θ := fun n => ⟨shift (n • v) θ, ⟨n • v, rfl⟩⟩
  obtain ⟨m, n, hmn, hne⟩ := Function.not_injective_iff.mp
    (not_injective_infinite_finite f)
  wlog hlt : m < n generalizing m n
  · exact this n m hmn.symm hne.symm (lt_of_le_of_ne (le_of_not_gt hlt) hne.symm)
  have hshift : shift (m • v) θ = shift (n • v) θ := congrArg Subtype.val hmn
  have htranslate := congrArg (shift (-(m • v))) hshift
  rw [shift_neg_shift, ← shift_add] at htranslate
  have hcast : ((n - m : ℕ) : ℤ) = (n : ℤ) - m := Int.ofNat_sub (le_of_lt hlt)
  have hvec : -(m • v) + n • v = (n - m) • v := by
    change -((m : ℤ) • v) + (n : ℤ) • v = ((n - m : ℕ) : ℤ) • v
    rw [hcast, sub_smul]
    abel
  rw [hvec] at htranslate
  exact ⟨n - m, Nat.sub_pos_of_lt hlt,
    (isPeriod_iff_shift θ _).mpr htranslate.symm⟩

theorem doublyPeriodic_of_finite_orbit (θ : Lattice → A) (hfinite : (orbit θ).Finite) :
    IsDoublyPeriodic θ := by
  obtain ⟨n, hn, hhor⟩ := direction_period_of_finite_orbit θ (1, 0) hfinite
  obtain ⟨m, hm, hver⟩ := direction_period_of_finite_orbit θ (0, 1) hfinite
  refine ⟨n • ((1, 0) : Lattice), m • ((0, 1) : Lattice), ?_, hhor, hver⟩
  simp [Geometry.det, Prod.smul_mk, Nat.ne_of_gt hn, Nat.ne_of_gt hm]

theorem doublyPeriodic_iff_finite_orbit (θ : Lattice → A) :
    IsDoublyPeriodic θ ↔ (orbit θ).Finite :=
  ⟨finite_orbit_of_doublyPeriodic θ, doublyPeriodic_of_finite_orbit θ⟩

theorem finite_orbitClosure_of_doublyPeriodic [TopologicalSpace A] [DiscreteTopology A]
    (θ : Lattice → A) (hp : IsDoublyPeriodic θ) : (orbitClosure θ).Finite := by
  rw [orbitClosure_eq_orbit_of_doublyPeriodic θ hp]
  exact finite_orbit_of_doublyPeriodic θ hp

theorem doublyPeriodic_iff_finite_orbitClosure [TopologicalSpace A] [DiscreteTopology A]
    (θ : Lattice → A) : IsDoublyPeriodic θ ↔ (orbitClosure θ).Finite := by
  constructor
  · exact finite_orbitClosure_of_doublyPeriodic θ
  · intro hfinite
    exact doublyPeriodic_of_finite_orbit θ (hfinite.subset (orbit_subset_orbitClosure θ))

/-- Every finite-window language of a doubly periodic field is bounded by its finite orbit. -/
theorem patternComplexity_le_orbit_card [Fintype A] (θ : Lattice → A)
    (hfinite : (orbit θ).Finite) (S : Finset Lattice) :
    patternComplexity θ S ≤ Nat.card (orbit θ) := by
  classical
  letI : Fintype (orbit θ) := hfinite.fintype
  let f : orbit θ → patternSet θ S := fun ξ =>
    ⟨patternAt ξ.val S 0, by
      rcases ξ.property with ⟨u, hu⟩
      refine ⟨u, ?_⟩
      rw [← hu, patternAt_shift]
      simp⟩
  have hf : Function.Surjective f := by
    rintro ⟨p, u, rfl⟩
    refine ⟨⟨shift u θ, ⟨u, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change patternAt (shift u θ) S 0 = patternAt θ S u
    rw [patternAt_shift, add_zero]
  simpa [patternComplexity, Nat.card_eq_fintype_card] using
    Fintype.card_le_of_surjective f hf

end FiniteOrbitCharacterization

end NivatTrial.Periodicity
