import ConvexNivat.ReductionDefinitions
import ConvexNivat.CorePeriods
import ConvexNivat.CorePatterns
import ConvexNivat.CoreLattice

namespace ConvexNivat
open scoped BigOperators

theorem hasPeriod_sum {A : Type*} [AddCommMonoid A]
    (f g : Configuration A) (h : Lattice) (hf : HasPeriod f h) (hg : HasPeriod g h) :
    HasPeriod (fun z => f z + g z) h := by
  exact hasPeriod_add_fields f g h hf hg

theorem hasPeriod_sub {A : Type*} [AddCommGroup A]
    (f g : Configuration A) (h : Lattice) (hf : HasPeriod f h) (hg : HasPeriod g h) :
    HasPeriod (fun z => f z - g z) h := by
  exact hasPeriod_sub_fields f g h hf hg

theorem doublyPeriodic_sum {A : Type*} [AddCommMonoid A]
    (f g : Configuration A) (hf : DoublyPeriodic f) (hg : DoublyPeriodic g) :
    DoublyPeriodic (fun z => f z + g z) := by
  exact doublyPeriodic_add_fields f g hf hg

theorem doublyPeriodic_sub {A : Type*} [AddCommGroup A]
    (f g : Configuration A) (hf : DoublyPeriodic f) (hg : DoublyPeriodic g) :
    DoublyPeriodic (fun z => f z - g z) := by
  exact doublyPeriodic_sub_fields f g hf hg

theorem parallel_periodic_sum {A : Type*} [AddCommMonoid A]
    (f g : Configuration A) (h k : Lattice) (hh : h ≠ 0) (hk : k ≠ 0)
    (hparallel : det h k = 0) (hf : HasPeriod f h) (hg : HasPeriod g k) :
    ∃ q : Lattice, q ≠ 0 ∧ det q h = 0 ∧ HasPeriod (fun z => f z + g z) q := by
  by_cases hh₁ : h.1 = 0
  · have hh₂ : h.2 ≠ 0 := by
      intro hz
      apply hh
      exact Prod.ext hh₁ hz
    have hk₁ : k.1 = 0 := by
      have hprod : h.2 * k.1 = 0 := by
        simpa [det, hh₁] using hparallel
      exact (mul_eq_zero.mp hprod).resolve_left hh₂
    have hk₂ : k.2 ≠ 0 := by
      intro hz
      apply hk
      exact Prod.ext hk₁ hz
    have hcommon : k.2 • h = h.2 • k := by
      ext <;> simp [hh₁, hk₁, mul_comm]
    refine ⟨k.2 • h, ?_, ?_, ?_⟩
    · intro hz
      apply mul_ne_zero hk₂ hh₂
      simpa using congrArg Prod.snd hz
    · simp [det]
      ring
    · apply hasPeriod_sum
      · exact hasPeriod_zsmul f h hf k.2
      · rw [hcommon]
        exact hasPeriod_zsmul g k hg h.2
  · have hk₁ : k.1 ≠ 0 := by
      intro hz
      have hk₂ : k.2 = 0 := by
        have hprod : h.1 * k.2 = 0 := by
          simpa [det, hz] using hparallel
        exact (mul_eq_zero.mp hprod).resolve_left hh₁
      apply hk
      exact Prod.ext hz hk₂
    have hcommon : k.1 • h = h.1 • k := by
      ext
      · simp [mul_comm]
      · change k.1 * h.2 = h.1 * k.2
        dsimp [det] at hparallel
        nlinarith
    refine ⟨k.1 • h, ?_, ?_, ?_⟩
    · intro hz
      apply mul_ne_zero hk₁ hh₁
      simpa using congrArg Prod.fst hz
    · simp [det]
      ring
    · apply hasPeriod_sum
      · exact hasPeriod_zsmul f h hf k.1
      · rw [hcommon]
        exact hasPeriod_zsmul g k hg h.1

theorem orbitClosure_preserves_integer_annihilator (ξ η : Configuration ℤ)
    (a : IntegerLaurent) (hη : η ∈ OrbitClosure ξ)
    (ha : ∀ z, integerLaurentAction a ξ z = 0) :
    ∀ z, integerLaurentAction a η z = 0 := by
  classical
  intro z
  obtain ⟨u, hu⟩ := hη (a.support.image (fun h => z + h))
  calc
    integerLaurentAction a η z = integerLaurentAction a ξ (u + z) := by
      unfold integerLaurentAction
      apply Finsupp.sum_congr
      intro h hh
      rw [hu (z + h) (Finset.mem_image.mpr ⟨h, hh, rfl⟩)]
      simp only [add_assoc]
    _ = 0 := ha (u + z)

theorem modPrime_preserves_period (p : ℕ) (f : Configuration ℤ) (h : Lattice)
    (hf : HasPeriod f h) : HasPeriod (fun z => (f z : ZMod p)) h := by
  intro z
  exact congrArg (fun a : ℤ => (a : ZMod p)) (hf z)

theorem modPrime_sum (p m : ℕ) (f : Fin m → Configuration ℤ) (z : Lattice) :
    ((∑ i, f i z : ℤ) : ZMod p) = ∑ i, (f i z : ZMod p) := by
  simp only [Int.cast_sum]

theorem appendixD_difference_identity {A : Type*} [AddCommGroup A]
    (θ₁ θ₂ : Configuration A) (h₂ : Lattice) (hperiod : HasPeriod θ₂ h₂)
    (s : ℤ) (z : Lattice) :
    (θ₁ (z + s • h₂) + θ₂ (z + s • h₂)) - (θ₁ z + θ₂ z) =
      θ₁ (z + s • h₂) - θ₁ z := by
  rw [(hasPeriod_zsmul θ₂ h₂ hperiod s) z]
  abel

theorem appendixD_difference_hasPeriod {A : Type*} [AddCommGroup A]
    (θ₁ θ₂ : Configuration A) (h₁ h₂ : Lattice)
    (hperiod₁ : HasPeriod θ₁ h₁) (hperiod₂ : HasPeriod θ₂ h₂) (s : ℤ) :
    HasPeriod (fun z => (θ₁ (z + s • h₂) + θ₂ (z + s • h₂)) -
      (θ₁ z + θ₂ z)) h₁ := by
  have ht : HasPeriod (translate (s • h₂) θ₁) h₁ :=
    (hasPeriod_translate_iff θ₁ (s • h₂) h₁).mpr hperiod₁
  intro z
  dsimp only
  rw [appendixD_difference_identity θ₁ θ₂ h₂ hperiod₂ s (z + h₁),
    appendixD_difference_identity θ₁ θ₂ h₂ hperiod₂ s z]
  exact (hasPeriod_sub_fields (translate (s • h₂) θ₁) θ₁ h₁ ht hperiod₁) z

theorem appendixD_agreement_saturates {A : Type*} [AddCommGroup A]
    (θ₁ θ₂ : Configuration A) (h₁ h₂ : Lattice)
    (hperiod₁ : HasPeriod θ₁ h₁) (hperiod₂ : HasPeriod θ₂ h₂)
    (s : ℤ) (F : Set Lattice)
    (hF : AgreesOn (translate (s • h₂) (fun z => θ₁ z + θ₂ z))
      (fun z => θ₁ z + θ₂ z) F) :
    ∀ z ∈ F, ∀ t : ℤ,
      (θ₁ (z + t • h₁ + s • h₂) + θ₂ (z + t • h₁ + s • h₂)) =
        θ₁ (z + t • h₁) + θ₂ (z + t • h₁) := by
  intro z hz t
  apply sub_eq_zero.mp
  calc
    (θ₁ (z + t • h₁ + s • h₂) + θ₂ (z + t • h₁ + s • h₂)) -
        (θ₁ (z + t • h₁) + θ₂ (z + t • h₁)) =
        (θ₁ (z + s • h₂) + θ₂ (z + s • h₂)) - (θ₁ z + θ₂ z) :=
      (hasPeriod_zsmul _ h₁
        (appendixD_difference_hasPeriod θ₁ θ₂ h₁ h₂ hperiod₁ hperiod₂ s) t) z
    _ = 0 := sub_eq_zero.mpr (hF z hz)

theorem strip_invariant (v : Lattice) (a b q : ℤ) :
    ForwardInvariant (latticeStrip v a b) (q • v) := by
  intro z hz
  change a ≤ height v (z + q • v) ∧ height v (z + q • v) ≤ b
  simp only [height_add, height_zsmul, height_self, mul_zero, add_zero]
  exact hz

theorem empty_strip (v : Lattice) (a : ℤ) : latticeStrip v a (a - 1) = ∅ := by
  ext z
  simp only [latticeStrip, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hz
  omega

end ConvexNivat
