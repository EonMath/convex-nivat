import ConvexNivat.CorePeriods
import ConvexNivat.MainTheorem

/-!
Source-facing scaffolds for Remark 0.1, source.txt lines 188–193.
The background is added to one actual StarComponent. The defining star axioms
remain those of Core; no conclusion is stored as a new hypothesis bundle.
-/

namespace ConvexNivat

noncomputable section

/-- Remark 0.1: enlarge an existing tangential period by a positive integer
multiple which also preserves the actual background. -/
theorem starComponent_background_period_multiple {p : ℕ}
    (C : StarComponent p) (B : Configuration (ZMod p)) (hB : DoublyPeriodic B)
    (k : ℤ) (hk : 1 ≤ k) (hperiod : HasPeriod C.field (k • C.direction)) :
    ∃ t : ℤ, 1 ≤ t ∧ HasPeriod B ((t * k) • C.direction) ∧
      HasPeriod (C.field + B) ((t * k) • C.direction) := by
  rcases doublyPeriodic_multiple_period B hB (k • C.direction) with ⟨t, ht, hBt⟩
  have hBtk : HasPeriod B ((t * k) • C.direction) := by
    simpa only [smul_smul] using hBt
  refine ⟨t, ht, hBtk, hasPeriod_add_fields _ _ _ ?_ hBtk⟩
  simpa only [smul_smul] using hasPeriod_zsmul C.field _ hperiod t

/-- The (S1) field used by the actual background-absorbing component constructor. -/
theorem starComponent_background_tangential_period {p : ℕ}
    (C : StarComponent p) (B : Configuration (ZMod p)) (hB : DoublyPeriodic B) :
    ∃ k : ℤ, 1 ≤ k ∧ HasPeriod (C.field + B) (k • C.direction) := by
  rcases C.tangential_period with ⟨k, hk, hperiod⟩
  rcases starComponent_background_period_multiple C B hB k hk hperiod with
    ⟨t, ht, _, hsum⟩
  exact ⟨t * k, by nlinarith, hsum⟩

/-- Remark 0.1's cancellation step preserves (S2). No finiteness of the alphabet
is required for this additive-group fact. -/
theorem not_doublyPeriodic_add_background {A : Type*} [AddCommGroup A]
    (F B : Configuration A) (hF : ¬ DoublyPeriodic F) (hB : DoublyPeriodic B) :
    ¬ DoublyPeriodic (F + B) := by
  intro hsum
  apply hF
  simpa only [add_sub_cancel_right] using doublyPeriodic_sub_fields (F + B) B hsum hB

/-- Adding the same background to a field and its tail preserves their agreement. -/
theorem agreesOn_add_background {A : Type*} [AddMonoid A]
    (F L B : Configuration A) (U : Set Lattice) (hFL : AgreesOn F L U) :
    AgreesOn (F + B) (L + B) U := by
  intro z hz
  exact congrArg (fun a => a + B z) (hFL z hz)

/-- The actual component of Remark 0.1: field and both tails gain B;
direction and transition-strip bounds stay the source's original values. -/
def StarComponent.addBackground {p : ℕ} (C : StarComponent p)
    (B : Configuration (ZMod p)) (hB : DoublyPeriodic B) : StarComponent p where
  direction := C.direction
  primitive := C.primitive
  field := C.field + B
  tangential_period := starComponent_background_tangential_period C B hB
  not_doubly_periodic := not_doublyPeriodic_add_background C.field B
    C.not_doubly_periodic hB
  leftTail := C.leftTail + B
  rightTail := C.rightTail + B
  left_doubly_periodic := doublyPeriodic_add_fields C.leftTail B C.left_doubly_periodic hB
  right_doubly_periodic := doublyPeriodic_add_fields C.rightTail B C.right_doubly_periodic hB
  lower := C.lower
  upper := C.upper
  bounds := C.bounds
  left_agreement := agreesOn_add_background C.field C.leftTail B _ C.left_agreement
  right_agreement := agreesOn_add_background C.field C.rightTail B _ C.right_agreement

/-- Replace just the chosen component of the actual finite star family. -/
def backgroundComponent {p : ℕ} (star : StarData p)
    (B : Configuration (ZMod p)) (hB : DoublyPeriodic B) (i j : Fin star.m) :
    StarComponent p :=
  if j = i then (star.component j).addBackground B hB else star.component j

/-- Direction preservation needed to form the same nonparallel star family. -/
theorem background_components_nonparallel {p : ℕ} (star : StarData p)
    (B : Configuration (ZMod p)) (hB : DoublyPeriodic B) (i : Fin star.m) :
    ∀ j k : Fin star.m, j ≠ k →
      Nonparallel (backgroundComponent star B hB i j).direction
        (backgroundComponent star B hB i k).direction := by
  have hdir : ∀ j : Fin star.m,
      (backgroundComponent star B hB i j).direction = (star.component j).direction := by
    intro j
    unfold backgroundComponent
    split_ifs <;> rfl
  intro j k hjk
  rw [hdir j, hdir k]
  exact star.pairwise_nonparallel j k hjk

/-- The star in Remark 0.1 is constructed by changing one component only.
Any component index may be used; the source chooses its first component. -/
def StarData.absorbBackground {p : ℕ} (star : StarData p)
    (B : Configuration (ZMod p)) (hB : DoublyPeriodic B) (i : Fin star.m) : StarData p where
  prime := star.prime
  m := star.m
  two_le := star.two_le
  component := backgroundComponent star B hB i
  pairwise_nonparallel := background_components_nonparallel star B hB i

/-- Remark 0.1, exact sum identity for the canonical absorption construction. -/
theorem absorbBackground_configuration {p : ℕ} (star : StarData p)
    (B : Configuration (ZMod p)) (hB : DoublyPeriodic B) (i : Fin star.m) :
    (star.absorbBackground B hB i).configuration = star.configuration + B := by
  classical
  funext z
  change (∑ j : Fin star.m, (backgroundComponent star B hB i j).field z) =
    (∑ j : Fin star.m, (star.component j).field z) + B z
  have hfield : ∀ j : Fin star.m,
      (backgroundComponent star B hB i j).field z =
        (star.component j).field z + if j = i then B z else 0 := by
    intro j
    unfold backgroundComponent
    split_ifs <;> simp [StarComponent.addBackground]
  simp_rw [hfield]
  rw [Finset.sum_add_distrib]
  simp

/-- Remark 0.1: the configuration with an arbitrary doubly periodic background
is still a star in exactly the original (S1)–(S3) sense. -/
theorem remark0_1_absorb_background {p : ℕ} (star : StarData p)
    (B : Configuration (ZMod p)) (hB : DoublyPeriodic B) :
    IsStarConfiguration (star.configuration + B) := by
  let i : Fin star.m := ⟨0, by have := star.two_le; omega⟩
  exact ⟨star.absorbBackground B hB i,
    (absorbBackground_configuration star B hB i).symm⟩

/-- Remark 0.1's final source claim: Theorem T also covers the actual sum
with an arbitrary doubly periodic background. -/
theorem remark0_1_background_complexity {p : ℕ} (star : StarData p)
    (B : Configuration (ZMod p)) (hB : DoublyPeriodic B)
    (S : Finset Lattice) (hS : S.Nonempty) (hconvex : LatticeConvex S) :
    S.card + 1 ≤ complexity (star.configuration + B) S := by
  exact theoremT (star.configuration + B)
    (remark0_1_absorb_background star B hB) S hS hconvex

end
end ConvexNivat
