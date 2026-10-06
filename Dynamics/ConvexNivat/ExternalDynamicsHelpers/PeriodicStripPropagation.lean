import ConvexNivat.ExternalDynamicsHelpers.PeriodicStripCore

namespace ConvexNivat.ExternalDynamicsHelpers
open ConvexNivat.Colle
noncomputable section

theorem generated_minimum_propagates_strip_down (ξ x y : Configuration ℤ)
    (hx : x ∈ OrbitClosure ξ) (hy : y ∈ OrbitClosure ξ)
    (S : Finset Lattice) (hS : S.Nonempty) (v : Lattice) (hv : Primitive v)
    (g : Lattice) (hface : supportRow S v = {g})
    (hgen : PatternDetermines ξ (S.erase g) g) (a b : ℤ)
    (hwidth : rowHeight v S hS ≤ b - a)
    (hagree : AgreesOn x y (latticeStrip v a b)) :
    AgreesOn x y (lowerHalf v b) := by
  classical
  have hdot (z : Lattice) : realDot (embed z) (normal v) = (det v z : ℝ) := by
    dsimp [realDot, embed, normal, det]
    push_cast
    ring
  have hgm : g ∈ supportRow S v := by rw [hface]; simp
  obtain ⟨hgS, hgmin⟩ := Finset.mem_filter.mp hgm
  have hmin : ∀ r ∈ S, det v g ≤ det v r := by
    intro r hr
    have hh := hgmin r hr
    rw [hdot, hdot] at hh
    exact_mod_cast hh
  have hming : rowMinimum v S hS = det v g := by
    apply le_antisymm (Finset.inf'_le _ hgS)
    exact Finset.le_inf' hS _ hmin
  have hrows : ∀ r ∈ S.erase g, det v g < det v r ∧
      det v r - det v g ≤ rowHeight v S hS := by
    intro r hr
    obtain ⟨hrg, hrS⟩ := Finset.mem_erase.mp hr
    refine ⟨lt_of_le_of_ne (hmin r hrS) ?_, ?_⟩
    · intro he
      have hrface : r ∈ supportRow S v := by
        apply Finset.mem_filter.mpr
        refine ⟨hrS, fun q hq => ?_⟩
        rw [hdot, hdot]
        exact_mod_cast (he ▸ hmin q hq)
      rw [hface] at hrface
      exact hrg (Finset.mem_singleton.mp hrface)
    · have hrmax : det v r ≤ rowMaximum v S hS := Finset.le_sup' _ hrS
      dsimp [rowHeight]
      rw [hming]
      omega
  have hind : ∀ n : ℕ, ∀ z : Lattice,
      a - (n : ℤ) ≤ det v z → det v z ≤ b → x z = y z := by
    intro n
    induction n with
    | zero =>
      intro z hza hzb
      exact hagree z ⟨by simpa using hza, hzb⟩
    | succ n ih =>
      intro z hza hzb
      by_cases hprev : a - (n : ℤ) ≤ det v z
      · exact ih z hprev hzb
      have hzrow : det v z = a - (n : ℤ) - 1 := by omega
      have hzab : det v z ≤ a := by omega
      have hgenerated := hgen x hx y hy (z - g) (fun r hr => ?_)
      · simpa only [add_sub_cancel] using hgenerated
      · obtain ⟨hrlow, hrhigh⟩ := hrows r hr
        apply ih (r + (z - g))
        · have he : det v (r + (z - g)) = det v r + det v z - det v g := by
            dsimp [det]; ring
          rw [he]
          omega
        · have he : det v (r + (z - g)) = det v r + det v z - det v g := by
            dsimp [det]; ring
          rw [he]
          omega
  intro z hz
  exact hind (a - det v z).toNat z (by have := Int.self_le_toNat (a - det v z); omega) hz

theorem strip_repeat_produces_translated_half_period (ξ : Configuration ℤ)
    (S : Finset Lattice) (hS : S.Nonempty) (v : Lattice) (hv : Primitive v)
    (g : Lattice) (hface : supportRow S v = {g})
    (hgen : PatternDetermines ξ (S.erase g) g)
    (w : Lattice) (a b t t' : ℤ) (htt' : t < t')
    (hwidth : rowHeight v S hS ≤ b - a)
    (hagree : AgreesOn (translate (t • w) ξ) (translate (t' • w) ξ)
      (latticeStrip v a b)) :
    ∀ z ∈ lowerHalf v (b + t * det v w), ξ (z + (t' - t) • w) = ξ z := by
  have heq := generated_minimum_propagates_strip_down ξ _ _
    (orbitClosure_translate_member ξ ξ (orbitClosure_contains_self ξ) _)
    (orbitClosure_translate_member ξ ξ (orbitClosure_contains_self ξ) _)
    S hS v hv g hface hgen a b hwidth hagree
  intro z hz
  have hz' : z - t • w ∈ lowerHalf v b := by
    change det v (z - t • w) ≤ b
    have hd : det v (z - t • w) = det v z - t * det v w := by
      dsimp [det]; ring
    rw [hd]
    exact sub_le_iff_le_add.mpr hz
  have hh := heq (z - t • w) hz'
  change ξ (z - t • w + t • w) = ξ (z - t • w + t' • w) at hh
  have hshift : z - t • w + t' • w = z + (t' - t) • w := by
    rw [sub_smul]; abel
  rw [sub_add_cancel, hshift] at hh
  exact hh.symm

theorem periodic_strip_bounded_half_periods (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (S : Finset Lattice) (hS : S.Nonempty) (v : Lattice) (hv : Primitive v)
    (g : Lattice) (hface : supportRow S v = {g})
    (hgen : PatternDetermines ξ (S.erase g) g)
    (w : Lattice) (hw : 0 < det v w) (a b : ℤ)
    (hwidth : rowHeight v S hS ≤ b - a) (B : Finset Lattice)
    (hcode : WindowCodes ξ B (latticeStrip v a b)) :
    ∀ τ : ℤ, ∃ t : ℤ, τ ≤ t ∧ ∃ q : ℕ,
      0 < q ∧ q ≤ complexity ξ B ∧
      ∀ z ∈ lowerHalf v (b + t * det v w), ξ (z + (q : ℤ) • w) = ξ z := by
  intro τ
  obtain ⟨t, t', ht, htt', hbound, hagree⟩ :=
    bounded_transverse_strip_repeat ξ A hA v w a b B hcode τ
  have hq : 0 ≤ t' - t := by omega
  refine ⟨t, ht, (t' - t).toNat, by omega, by omega, ?_⟩
  simpa only [Int.toNat_of_nonneg hq] using
    strip_repeat_produces_translated_half_period ξ S hS v hv g hface hgen w
      a b t t' htt' hwidth hagree

end
end ConvexNivat.ExternalDynamicsHelpers
