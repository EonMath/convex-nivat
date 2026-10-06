import ConvexNivat.Colle.Orbit

namespace ConvexNivat.ExternalDynamicsHelpers
open ConvexNivat.Colle
noncomputable section

def WindowCodes (ξ : Configuration ℤ) (B : Finset Lattice) (U : Set Lattice) : Prop :=
  ∀ x ∈ OrbitClosure ξ, ∀ y ∈ OrbitClosure ξ,
    AgreesOn x y (B : Set Lattice) → AgreesOn x y U

theorem periodic_representatives_code_strip (ξ : Configuration ℤ)
    (h : Lattice) (hperiod : HasPeriod ξ h) (v : Lattice) (a b : ℤ)
    (B : Finset Lattice)
    (hreps : ∀ z ∈ latticeStrip v a b, ∃ q ∈ B, ∃ j : ℤ, z = q + j • h) :
    WindowCodes ξ B (latticeStrip v a b) := by
  intro x hx y hy hagree z hz
  obtain ⟨q, hq, j, rfl⟩ := hreps z hz
  have hxp := orbitClosure_period_inheritance ξ x hx h hperiod
  have hyp := orbitClosure_period_inheritance ξ y hy h hperiod
  rw [hasPeriod_zsmul x h hxp j q, hasPeriod_zsmul y h hyp j q]
  exact hagree q hq

theorem bounded_transverse_pattern_repeat (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (B : Finset Lattice) (w : Lattice) (τ : ℤ) :
    ∃ t t' : ℤ, τ ≤ t ∧ t < t' ∧ t' ≤ τ + (complexity ξ B : ℤ) ∧
      AgreesOn (translate (t • w) ξ) (translate (t' • w) ξ) (B : Set Lattice) := by
  classical
  let encode : Pattern {a : ℤ // a ∈ A} B → Pattern ℤ B := fun p z => (p z).val
  have hfinite : (patternSet ξ B).Finite := by
    apply (Set.finite_range encode).subset
    rintro p ⟨u, rfl⟩
    exact ⟨fun z => ⟨ξ (u + z.val), hA _⟩, rfl⟩
  letI := hfinite.fintype
  let f : Fin (complexity ξ B + 1) → patternSet ξ B := fun i =>
    ⟨pattern ξ B ((τ + (i.val : ℤ)) • w), ⟨_, rfl⟩⟩
  have hcard : Fintype.card (patternSet ξ B) <
      Fintype.card (Fin (complexity ξ B + 1)) := by
    rw [Fintype.card_fin, Set.fintypeCard_eq_ncard]
    change complexity ξ B < complexity ξ B + 1
    omega
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hpair : ∃ i j : Fin (complexity ξ B + 1), i.val < j.val ∧ f i = f j := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h, heq⟩
    · exact ⟨j, i, h, heq.symm⟩
  obtain ⟨i, j, hij, heq⟩ := hpair
  refine ⟨τ + i.val, τ + j.val, by omega, by omega, by omega, ?_⟩
  intro z hz
  have hh := congrFun (congrArg Subtype.val heq) ⟨z, hz⟩
  simpa [f, pattern, translate, add_comm] using hh

theorem bounded_transverse_strip_repeat (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (v w : Lattice) (a b : ℤ) (B : Finset Lattice)
    (hcode : WindowCodes ξ B (latticeStrip v a b)) (τ : ℤ) :
    ∃ t t' : ℤ, τ ≤ t ∧ t < t' ∧ t' ≤ τ + (complexity ξ B : ℤ) ∧
      AgreesOn (translate (t • w) ξ) (translate (t' • w) ξ) (latticeStrip v a b) := by
  obtain ⟨t, t', ht, htt', hbound, hagree⟩ :=
    bounded_transverse_pattern_repeat ξ A hA B w τ
  refine ⟨t, t', ht, htt', hbound, ?_⟩
  exact hcode _ (orbitClosure_translate_member ξ ξ (orbitClosure_contains_self ξ) _) _
    (orbitClosure_translate_member ξ ξ (orbitClosure_contains_self ξ) _) hagree

theorem bounded_cofinal_half_period_global (ξ : Configuration ℤ)
    (v w : Lattice) (hw : 0 < det v w) (b : ℤ) (N : ℕ)
    (hperiods : ∀ τ : ℤ, ∃ t : ℤ, τ ≤ t ∧ ∃ q : ℕ,
      0 < q ∧ q ≤ N ∧
      ∀ z ∈ lowerHalf v (b + t * det v w), ξ (z + (q : ℤ) • w) = ξ z) :
    ∃ q : ℕ, 0 < q ∧ q ≤ N ∧ HasPeriod ξ ((q : ℤ) • w) := by
  classical
  by_contra hnone
  push_neg at hnone
  have hbad : ∀ q : ℕ, ∃ z : Lattice,
      0 < q → q ≤ N → ξ (z + (q : ℤ) • w) ≠ ξ z := by
    intro q
    by_cases hp : 0 < q
    · by_cases hq : q ≤ N
      · obtain ⟨z, hz⟩ := not_forall.mp (hnone q hp hq)
        exact ⟨z, fun _ _ => hz⟩
      · exact ⟨0, fun _ h => (hq h).elim⟩
    · exact ⟨0, fun h _ => (hp h).elim⟩
  choose z hz using hbad
  let M : ℕ := (Finset.range (N + 1)).sup (fun q => (det v (z q) - b).toNat)
  obtain ⟨t, ht, q, hqpos, hqN, hp⟩ := hperiods M
  have hqmem : q ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  have hM : (det v (z q) - b).toNat ≤ M := Finset.le_sup (f := fun q => (det v (z q) - b).toNat) hqmem
  have hdet : det v (z q) - b ≤ (M : ℤ) :=
    (Int.self_le_toNat _).trans (by exact_mod_cast hM)
  have ht0 : 0 ≤ t := le_trans (Int.natCast_nonneg _) ht
  have hwt : t ≤ t * det v w := by nlinarith
  exact hz q hqpos hqN (hp _ (show det v (z q) ≤ b + t * det v w by omega))

end
end ConvexNivat.ExternalDynamicsHelpers
