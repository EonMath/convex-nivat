import NivatTrial.ColleMaximalTranslation
import NivatTrial.ColleMaximalAgreementLimit
import NivatTrial.LatticeCoordinates

/-! Finite extension maximality and finite long-window exhaustion move
together with both configurations under translation. -/

namespace NivatTrial.ColleFiniteMaximalTranslation

open NivatTrial.Geometry NivatTrial.Dynamics NivatTrial.Nonexpansive
open NivatTrial.LatticePolygon NivatTrial.LatticeCoordinates
open NivatTrial.ColleEnvelopeTranslation NivatTrial.ColleMaximalTranslation
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleLongFaces
open NivatTrial.ColleMaximalAgreementLimit
open scoped Classical
noncomputable section

theorem latticeConvex_recenterWindow {T : Finset Lattice}
    (hT : IsLatticeConvex T) (c : Lattice) : IsLatticeConvex (recenterWindow T c) := by
  have he : recenterWindow T c = translateWindow (-c) T := by
    ext z
    simp only [mem_recenterWindow,mem_translateWindow,sub_neg_eq_add]
  rw [he]
  exact isLatticeConvex_translateWindow (-c) hT

theorem finiteExtensionMaximal_recenter {A : Type*}
    {D : Finset Lattice} {x p : Lattice → A} {R Q : Set Lattice}
    (hmax : FiniteExtensionMaximal D x p R Q) (c : Lattice) :
    FiniteExtensionMaximal D (shift c x) (shift c p) (recenter R c) (recenter Q c) := by
  intro S W hSc hSf hW hWc hWf hWS hWR hSQ hSa
  have hWn : (recenterWindow W (-c)).Nonempty := by
    obtain ⟨w,hw⟩ := hW
    exact ⟨w+c,by simpa only [mem_recenterWindow,add_neg_cancel_right] using hw⟩
  have hWSn : recenterWindow W (-c) ⊆ recenterWindow S (-c) := by
    intro z hz
    exact (mem_recenterWindow S (-c) z).mpr
      (hWS ((mem_recenterWindow W (-c) z).mp hz))
  have hWRn : (recenterWindow W (-c) : Set Lattice) ⊆ R := by
    intro z hz
    have hh := hWR ((mem_recenterWindow W (-c) z).mp hz)
    simpa only [recenter,Set.mem_ofPred_eq,neg_add_cancel_right] using hh
  have hSQn : (recenterWindow S (-c) : Set Lattice) ⊆ Q := by
    intro z hz
    have hh := hSQ ((mem_recenterWindow S (-c) z).mp hz)
    simpa only [recenter,Set.mem_ofPred_eq,neg_add_cancel_right] using hh
  have hSan : AgreeOn x p (recenterWindow S (-c) : Set Lattice) := by
    intro z hz
    have hh := hSa (z+(-c)) ((mem_recenterWindow S (-c) z).mp hz)
    simpa only [shift_apply,add_comm c,neg_add_cancel_right] using hh
  have hsub := hmax (recenterWindow S (-c)) (recenterWindow W (-c))
    (latticeConvex_recenterWindow hSc (-c)) (longFaces_recenterWindow hSf (-c))
    hWn (latticeConvex_recenterWindow hWc (-c)) (longFaces_recenterWindow hWf (-c))
    hWSn hWRn hSQn hSan
  intro z hz
  exact hsub ((mem_recenterWindow S (-c) (z+c)).mpr (by simpa using hz))

theorem finite_long_exhaustion_recenter
    {D : Finset Lattice} {R : Set Lattice}
    (hexhaust : ∀ F : Finset Lattice, (F : Set Lattice) ⊆ R →
      ∃ W : Finset Lattice, F ⊆ W ∧ (W : Set Lattice) ⊆ R ∧
        IsEnvelope D (W : Set Lattice) ∧ LongFaces D (W : Set Lattice))
    (c : Lattice) (hc : c ∈ R) :
    ∀ F : Finset Lattice, (F : Set Lattice) ⊆ recenter R c →
      ∃ W : Finset Lattice, F ⊆ W ∧ (W : Set Lattice) ⊆ recenter R c ∧
        IsEnvelope D (W : Set Lattice) ∧ LongFaces D (W : Set Lattice) ∧ 0 ∈ W := by
  intro F hF
  let G := insert c (recenterWindow F (-c))
  have hG : (G : Set Lattice) ⊆ R := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hc
    · have hh := hF ((mem_recenterWindow F (-c) z).mp hz)
      simpa only [recenter,Set.mem_ofPred_eq,neg_add_cancel_right] using hh
  obtain ⟨W,hGW,hWR,hWe,hWf⟩ := hexhaust G hG
  refine ⟨recenterWindow W c,?_,?_,isEnvelope_recenterWindow hWe c,
    longFaces_recenterWindow hWf c,?_⟩
  · intro z hz
    apply (mem_recenterWindow W c z).mpr
    apply hGW
    exact Finset.mem_insert_of_mem ((mem_recenterWindow F (-c) (z+c)).mpr (by simpa using hz))
  · intro z hz
    exact hWR ((mem_recenterWindow W c z).mp hz)
  · apply (mem_recenterWindow W c 0).mpr
    simpa only [zero_add] using hGW (Finset.mem_insert_self c _)

end
end NivatTrial.ColleFiniteMaximalTranslation
