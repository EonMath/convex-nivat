import ConvexNivat.SectorGeometry
import ConvexNivat.SectorCycleIncidence
import ConvexNivat.SectorCycleArithmetic

namespace ConvexNivat
noncomputable section

def sectorCycleEnumeration {p : ℕ} (star : StarData p) :
    Fin (2 * star.m) ≃ {ε : SectorSigns star // RealisedSector star ε} :=
  (sectorTwoBlockEquiv star.m).symm.trans (sectorSignedEquiv star)

/-- Lemma 3.0's cycle clause, including exactly 2m realised sectors and exactly
the neighbour relation of a 2m-cycle under geometric ray adjacency. -/
theorem realised_sectors_cycle {p : ℕ} (star : StarData p) :
    ∃ enumeration : Fin (2 * star.m) ≃ {ε : SectorSigns star // RealisedSector star ε},
      ∀ j k : Fin (2 * star.m),
        (∃ i σ, SectorsAdjacentAtRay star i σ (enumeration j).val
          (enumeration k).val) ↔
        ((j.val + 1) % (2 * star.m) = k.val ∨
          (k.val + 1) % (2 * star.m) = j.val) := by
  refine ⟨sectorCycleEnumeration star, ?_⟩
  intro j k
  have hE :
      (∀ l : Fin star.m, (sectorSignedEquiv star (.inl l)).val = sectorPositiveCode star l) ∧
      (∀ l : Fin star.m, (sectorSignedEquiv star (.inr l)).val = sectorNegativeCode star l) :=
    Classical.choose_spec (sector_signed_bijection star).2.2
  have hblocks (a b : Fin star.m ⊕ Fin star.m) :
      (∃ i σ, SectorsAdjacentAtRay star i σ (sectorSignedEquiv star a).val
        (sectorSignedEquiv star b).val) ↔ sectorTwoBlockRelation star.m a b := by
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        rw [hE.1, hE.1]
        exact (sector_adjacency_blocks star).1 a b
      | inr b =>
        rw [hE.1, hE.2]
        exact (sector_adjacency_blocks star).2.2.1 a b
    | inr a =>
      cases b with
      | inl b =>
        rw [hE.2, hE.1]
        exact (sector_adjacency_blocks star).2.2.2 a b
      | inr b =>
        rw [hE.2, hE.2]
        exact (sector_adjacency_blocks star).2.1 a b
  change (∃ i σ, SectorsAdjacentAtRay star i σ
    (sectorSignedEquiv star ((sectorTwoBlockEquiv star.m).symm j)).val
    (sectorSignedEquiv star ((sectorTwoBlockEquiv star.m).symm k)).val) ↔ _
  exact (hblocks _ _).trans ((two_block_cycle_arithmetic star.m star.two_le).2.2 j k)


end
end ConvexNivat
