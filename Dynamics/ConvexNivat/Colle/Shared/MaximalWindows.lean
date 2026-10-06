import ConvexNivat.Colle.Shared.CycleAlignment

namespace ConvexNivat.Colle
noncomputable section

private theorem realDet_embed_sub (d z q : Lattice) :
    realDet (embed d) (embed z - embed q) = (det d (z - q) : ℝ) := by
  simp [realDet, embed, det]

private theorem aligned_lattice_mem_iff {S A : Finset Lattice} {m : ℕ}
    {C : AntipodalEdgeCycle S m} (hA : EnvelopedWindow S A)
    (D : AlignedBoundary C A) (z : Lattice) :
    z ∈ A ↔ ∀ d : ℤ, 0 ≤ det (C.direction d) (z - D.vertex d) := by
  rw [← hA.2.1 z, D.hull_eq]
  change (∀ d : ℤ, 0 ≤ realDet (embed (C.direction d)) (embed z - embed (D.vertex d))) ↔ _
  simp only [realDet_embed_sub]
  constructor <;> intro h d <;> exact_mod_cast h d

private theorem periodic_integer_representative {α : Type*} {f : ℤ → α} {p : ℤ}
    (_hp : 0 < p) (hf : Function.Periodic f p) (d : ℤ) :
    f d = f (d % p) := by
  have h := hf.int_mul (d / p) (d % p)
  have hd : d % p + d / p * p = d := by
    simpa [Int.mul_comm] using Int.emod_add_ediv_mul d p
  simpa [hd] using h

private theorem window_subset_halfStrip (B : Finset Lattice) (v : Lattice) :
    (B : Set Lattice) ⊆ halfStrip B v := by
  intro z hz
  exact ⟨z, hz, 0, by simp⟩

private theorem bounded_agreement_family_maximal (S B : Finset Lattice) (v : Lattice)
    (x y : Configuration ℤ) (hB : EnvelopedWindow S B)
    (hagrees : AgreesOn x y (B : Set Lattice)) (N : ℕ)
    (hbound : ∀ A : Finset Lattice, EnvelopedWindow S A → B ⊆ A →
      (A : Set Lattice) ⊆ halfStrip B v → AgreesOn x y (A : Set Lattice) → A.card ≤ N) :
    ∃ A : Finset Lattice, maximalAgreementWindow S B A v x y := by
  classical
  let family : Set (Finset Lattice) := {A | EnvelopedWindow S A ∧ B ⊆ A ∧
    (A : Set Lattice) ⊆ halfStrip B v ∧ AgreesOn x y (A : Set Lattice)}
  have hn : family.Nonempty := ⟨B, hB, Finset.Subset.refl _, window_subset_halfStrip B v, hagrees⟩
  have hf : (Finset.card '' family).Finite :=
    (Set.finite_le_nat N).subset (by
      rintro n ⟨A, hA, rfl⟩
      exact hbound A hA.1 hA.2.1 hA.2.2.1 hA.2.2.2)
  obtain ⟨A, hA, hmax⟩ := hf.exists_maximalFor' Finset.card family hn
  refine ⟨A, hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, ?_⟩
  intro T hT hAT hstrip hag
  have hmem : T ∈ family := ⟨hT, hA.2.1.trans hAT, hstrip, hag⟩
  have hc : T.card ≤ A.card := hmax hmem (Finset.card_le_card hAT)
  exact (Finset.eq_of_subset_of_card_le hAT hc).symm

private theorem excluded_point_uniform_bound {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (v z : Lattice) (hz : z ∈ halfStrip B v) :
    ∃ N : ℕ, ∀ A : Finset Lattice, EnvelopedWindow S A → B ⊆ A →
      (A : Set Lattice) ⊆ halfStrip B v → z ∉ A → A.card ≤ N := by
  classical
  let K : ℕ := (Finset.univ.product B).sup
    (fun t : Fin (2 * m) × Lattice => (det (C.direction (t.1.val : ℤ)) (t.2 - z)).toNat)
  let F : Finset Lattice := (B.product (Finset.range (K + 1))).image
    (fun t => t.1 + (t.2 : ℤ) • v)
  refine ⟨F.card, ?_⟩
  intro A hA hBA hstrip hnot
  obtain ⟨D⟩ := (enveloped_boundary_aligned_cycle C hA).1
  have hsep : ∃ d : ℤ, det (C.direction d) (z - D.vertex d) < 0 := by
    have hn := mt (aligned_lattice_mem_iff hA D z).mpr hnot
    push Not at hn
    exact hn
  obtain ⟨d, hd⟩ := hsep
  obtain ⟨b, hb, t, hzt⟩ := hz
  have hb0 := (aligned_lattice_mem_iff hA D b).mp (hBA hb) d
  have hv : det (C.direction d) v < 0 := by
    have he : det (C.direction d) (z - D.vertex d) =
        det (C.direction d) (b - D.vertex d) + (t : ℤ) * det (C.direction d) v := by
      rw [hzt]
      simp [det]
      ring
    rw [he] at hd
    by_contra! hn
    have := mul_nonneg (Int.natCast_nonneg t) hn
    omega
  have hp : 0 < 2 * (m : ℤ) := by have := C.at_least_two; omega
  let r := d % (2 * (m : ℤ))
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hp.ne'
  have hrp : r < 2 * (m : ℤ) := Int.emod_lt_of_pos _ hp
  let j : Fin (2 * m) := ⟨r.toNat, by omega⟩
  have hj : (j.val : ℤ) = r := Int.toNat_of_nonneg hr0
  have hdir : C.direction d = C.direction (j.val : ℤ) := by
    rw [hj]
    exact periodic_integer_representative hp C.direction_periodic d
  apply Finset.card_le_card
  intro p hpA
  obtain ⟨q, hq, n, hpn⟩ := hstrip hpA
  have hp0 := (aligned_lattice_mem_iff hA D p).mp hpA d
  have he : det (C.direction d) (p - D.vertex d) -
      det (C.direction d) (z - D.vertex d) =
      det (C.direction d) (q - z) + (n : ℤ) * det (C.direction d) v := by
    rw [hpn]
    simp [det]
    ring
  have hpos : 0 < det (C.direction d) (q - z) +
      (n : ℤ) * det (C.direction d) v := by omega
  have hnZ : (n : ℤ) < det (C.direction d) (q - z) := by
    have hneg : det (C.direction d) v ≤ -1 := by omega
    have hmul := mul_le_mul_of_nonneg_left hneg (Int.natCast_nonneg n)
    nlinarith
  have hK : (det (C.direction d) (q - z)).toNat ≤ K := by
    rw [hdir]
    exact Finset.le_sup (s := Finset.univ.product B) (b := (j, q)) (f := fun t : Fin (2 * m) × Lattice =>
      (det (C.direction (t.1.val : ℤ)) (t.2 - z)).toNat)
      (Finset.mem_product.mpr ⟨Finset.mem_univ j, hq⟩)
  have hnK : n < K + 1 := by omega
  exact Finset.mem_image.mpr ⟨(q, n),
    Finset.mem_product.mpr ⟨hq, Finset.mem_range.mpr hnK⟩, hpn.symm⟩

theorem maximal_agreement_enveloped_window (ξ : Configuration ℤ) (alphabet : Finset ℤ)
    (halphabet : ∀ z, ξ z ∈ alphabet) (S : Finset Lattice) (hS : GeneratingSet ξ S)
    (m : ℕ) (C : AntipodalEdgeCycle S m) (i : ℤ) (B : Finset Lattice)
    (hB : EnvelopedWindow S B)
    (hposition : ∀ z ∈ supportRow B (C.direction i), det (C.direction i) z = -1)
    (x y : Configuration ℤ) (hx : x ∈ OrbitClosure ξ) (hy : y ∈ OrbitClosure ξ)
    (hperiod : ∃ a : ℤ, a ≠ 0 ∧ HasPeriod y (a • C.direction i))
    (hagrees : AgreesOn x y (B : Set Lattice))
    (hfailure : ¬ AgreesOn x y (halfStrip B (C.direction i))) :
    ∃ A : Finset Lattice, maximalAgreementWindow S B A (C.direction i) x y ∧
      Nonempty (AlignedBoundary C A) := by
  classical
  have hf : ∃ z ∈ halfStrip B (C.direction i), x z ≠ y z := by
    by_contra! hn
    exact hfailure (fun z hz => hn z hz)
  obtain ⟨z, hz, hxy⟩ := hf
  obtain ⟨N, hN⟩ := excluded_point_uniform_bound C (C.direction i) z hz
  obtain ⟨A, hA⟩ := bounded_agreement_family_maximal S B (C.direction i) x y hB hagrees N
    (fun A henv hBA hstrip hag => hN A henv hBA hstrip (fun hzA => hxy (hag z hzA)))
  exact ⟨A, hA, (enveloped_boundary_aligned_cycle C hA.1).1⟩

end
end ConvexNivat.Colle
