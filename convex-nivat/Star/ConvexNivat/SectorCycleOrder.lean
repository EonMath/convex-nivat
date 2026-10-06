import ConvexNivat.SectorCycleAlgebra

namespace ConvexNivat
noncomputable section

def sectorBreakpointImage {p : ℕ} (star : StarData p) : Finset ℝ :=
  Finset.univ.image (sectorBreakpoint star)

theorem sector_sorted_labelled_breakpoints {p : ℕ} (star : StarData p) :
    ∃ label : Fin (star.m - 1) ≃ SectorRest star,
      StrictMono (fun r => sectorBreakpoint star (label r)) ∧
      (sectorBreakpointImage star).card = star.m - 1 ∧
      (∀ j : SectorRest star, ∃! r : Fin (star.m - 1),
        sectorBreakpoint star (label r) = sectorBreakpoint star j) ∧
      (∀ r, label.symm (label r) = r) ∧
      (∀ j, label (label.symm j) = j) := by
  classical
  have hi := (sector_breakpoint_injective star).2
  have hcRest : Fintype.card (SectorRest star) = star.m - 1 := by
    simp [SectorRest, Fintype.card_subtype_compl]
  have hc : (sectorBreakpointImage star).card = star.m - 1 := by
    rw [sectorBreakpointImage, Finset.card_image_of_injective _ hi,
      Finset.card_univ, hcRest]
  let e : SectorRest star ≃ ↥(sectorBreakpointImage star) :=
    Equiv.ofBijective (fun j => ⟨sectorBreakpoint star j, by simp [sectorBreakpointImage]⟩)
      ⟨fun j k h => hi (congrArg Subtype.val h), by
        rintro ⟨t, ht⟩
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp ht
        exact ⟨j, Subtype.ext hj⟩⟩
  let o := (sectorBreakpointImage star).orderIsoOfFin hc
  let label := o.toEquiv.trans e.symm
  have he (r : Fin (star.m - 1)) : sectorBreakpoint star (label r) = (o r).val := by
    exact congrArg Subtype.val (e.apply_symm_apply (o r))
  refine ⟨label, ?_, hc, ?_, label.symm_apply_apply, label.apply_symm_apply⟩
  · intro r s hrs
    change sectorBreakpoint star (label r) < sectorBreakpoint star (label s)
    rw [he r, he s]
    exact o.strictMono hrs
  · intro j
    refine ⟨label.symm j, ?_, ?_⟩
    · simp
    · intro r hr
      calc
        r = label.symm (label r) := (label.symm_apply_apply r).symm
        _ = label.symm j := congrArg label.symm (hi hr)

def sectorLabel {p : ℕ} (star : StarData p) : Fin (star.m - 1) ≃ SectorRest star :=
  Classical.choose (sector_sorted_labelled_breakpoints star)

def sectorRank {p : ℕ} (star : StarData p) (j : SectorRest star) : Fin (star.m - 1) :=
  (sectorLabel star).symm j

def sectorOrderedBreakpoint {p : ℕ} (star : StarData p) (r : Fin (star.m - 1)) : ℝ :=
  sectorBreakpoint star (sectorLabel star r)

end
end ConvexNivat
