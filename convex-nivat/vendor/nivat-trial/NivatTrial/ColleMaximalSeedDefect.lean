import NivatTrial.ColleHullCoding
import NivatTrial.ColleStepExpansionGeometry

/-! A fixed early window detects every later maximal-window defect.
The candidate sites form one fixed finite set, so they cannot all disappear
when a subsequence of configurations converges. -/

namespace NivatTrial.ColleMaximalSeedDefect

open NivatTrial.Geometry NivatTrial.LatticePolygon NivatTrial.RegionGeometry
open NivatTrial.Dynamics NivatTrial.Nonexpansive NivatTrial.OneSidedRecurrence
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleLongFaces
open NivatTrial.ColleEnvelopeTranslation NivatTrial.ColleEnvelopeExpansion
open NivatTrial.ColleStepExpansionGeometry NivatTrial.ColleHullCoding
open NivatTrial.ColleEnvelopeGeometry
open scoped Classical
noncomputable section

def stepWindow (W : Finset Lattice) (u : Lattice) : Finset Lattice :=
  W ∪ recenterWindow W (-u)

theorem coe_stepWindow (W : Finset Lattice) (u : Lattice) :
    (stepWindow W u : Set Lattice) = (W : Set Lattice) ∪ recenter (W : Set Lattice) (-u) := by
  simp only [stepWindow, Finset.coe_union, coe_recenterWindow]

theorem coe_stepWindow_eq_stepExpansion (D W : Finset Lattice) (u : Lattice)
    (hW : W.Nonempty) (hWe : IsEnvelope D (W : Set Lattice))
    (hWf : LongFaces D (W : Set Lattice))
    (hu0 : u ≠ 0) (hu : u ∈ D) (hnu : -u ∈ D) :
    (stepWindow W u : Set Lattice) = stepExpansion D (W : Set Lattice) u := by
  rw [coe_stepWindow,stepExpansion_eq_union D W u hW hWe hWf hu0 hu hnu]

theorem factor_faces_of_directions (hs : List Lattice) (D : Finset Lattice)
    (hdirs : ∀ d ∈ hs, d ∈ D ∧ -d ∈ D) (R : Set Lattice) (hR : LongFaces D R) :
    ∀ u ∈ hs, LongFaces {u,-u} R := by
  intro u hu d hd
  have hdu := hdirs u hu
  apply hR d
  rcases Finset.mem_insert.mp hd with rfl | hd
  · exact hdu.1
  · rw [Finset.mem_singleton.mp hd]
    exact hdu.2

/-- Uniform finite defect set: its size and location depend on W and u,
not on the later maximal window T. -/
theorem maximal_window_has_fixed_seed_defect {A : Type*}
    (θ : Lattice → A) (code : A → ℤ) (hcode : Function.Injective code)
    (hs : List Lattice) (hne : ∀ d ∈ hs, d ≠ 0)
    (hind : hs.Pairwise (fun d e => det d e ≠ 0))
    (hann : iteratedIncrement hs (encode code θ) = 0)
    (x p : Lattice → A) (hx : x ∈ languageHull θ) (hp : p ∈ languageHull θ)
    (D T W : Finset Lattice) (Q : Set Lattice) (u : Lattice)
    (hdirs : ∀ d ∈ hs, d ∈ D ∧ -d ∈ D)
    (hTe : IsEnvelope D (T : Set Lattice)) (hTf : LongFaces D (T : Set Lattice))
    (hWe : IsEnvelope D (W : Set Lattice)) (hWf : LongFaces D (W : Set Lattice))
    (hWT : W ⊆ T) (hzero : 0 ∈ W) (hout : u ∉ T)
    (hu0 : u ≠ 0) (hu : u ∈ D) (hnu : -u ∈ D)
    (hQ : IsEnvelope D Q) (hTQ : (T : Set Lattice) ⊆ Q)
    (hforward : ForwardInvariant Q u) (hagree : AgreeOn x p (T : Set Lattice))
    (hmax : ∀ R : Set Lattice, (T : Set Lattice) ⊆ R → R ⊆ Q → IsEnvelope D R →
      LongFaces D R → AgreeOn x p R → R = (T : Set Lattice)) :
    ∃ z ∈ stepWindow W u, x z ≠ p z := by
  by_contra hnone
  push Not at hnone
  let S := stepWindow W u
  have hW : W.Nonempty := ⟨0,hzero⟩
  have hSstep : (S : Set Lattice) = stepExpansion D (W : Set Lattice) u :=
    coe_stepWindow_eq_stepExpansion D W u hW hWe hWf hu0 hu hnu
  have hSe : IsEnvelope D (S : Set Lattice) := by
    rw [hSstep]
    exact supportHull_idempotent D _
  have hSf : LongFaces D (S : Set Lattice) := by
    rw [hSstep]
    exact stepExpansion_longFaces hWf u
  have hWS : W ⊆ S := Finset.subset_union_left
  have hSQ : (S : Set Lattice) ⊆ Q := by
    rw [hSstep]
    exact stepExpansion_subset hQ (fun _ hw => hTQ (hWT hw)) u hforward
  have hSagree : AgreeOn x p (S : Set Lattice) := hnone
  let R := supportHull D ((T : Set Lattice) ∪ (S : Set Lattice))
  have hRT : (T : Set Lattice) ⊆ R := fun _ hz => subset_supportHull D _ (Or.inl hz)
  have hRQ : R ⊆ Q := by
    intro z hz
    rw [← hQ]
    exact supportHull_mono D (Set.union_subset hTQ hSQ) hz
  have hRf : LongFaces D R := (longFaces_union hTf hSf).supportHull
  have hRagree : AgreeOn x p R :=
    agreement_supportHull_union_of_common_window θ code hcode hs hne hind hann x p hx hp
      D T S W hdirs (latticeConvex_finset_of_region T hTe.latticeConvex)
      (latticeConvex_finset_of_region S hSe.latticeConvex)
      (factor_faces_of_directions hs D hdirs _ hTf)
      (factor_faces_of_directions hs D hdirs _ hSf)
      hW (latticeConvex_finset_of_region W hWe.latticeConvex)
      (factor_faces_of_directions hs D hdirs _ hWf) hWT hWS hagree hSagree
  have hReq := hmax R hRT hRQ (supportHull_idempotent D _) hRf hRagree
  have huS : u ∈ S := by
    apply Finset.mem_union_right
    simp only [mem_recenterWindow,add_neg_cancel]
    exact hzero
  have huR : u ∈ R := subset_supportHull D _ (Or.inr huS)
  rw [hReq] at huR
  exact hout huR

theorem stepWindow_in_bottom_halfPlane (W : Finset Lattice) (u : Lattice)
    (hW : ∀ z ∈ W, 0 ≤ det u z) :
    ∀ z ∈ stepWindow W u, 0 ≤ det u z := by
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · exact hW z hz
  · have hh := hW (z+(-u)) ((mem_recenterWindow W (-u) z).mp hz)
    simpa only [det_add_right,det_neg_right,det_self,neg_zero,add_zero] using hh

end
end NivatTrial.ColleMaximalSeedDefect
