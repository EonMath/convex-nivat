import NivatTrial.ColleEnvelopeTranslation
import NivatTrial.ColleHalfStripEnvelope

/-! Maximality of actual agreement regions survives recentering. The
admissible ambient region and both compared configurations move together. -/

namespace NivatTrial.ColleMaximalTranslation

open NivatTrial.Geometry NivatTrial.Dynamics NivatTrial.Nonexpansive
open NivatTrial.RegionGeometry NivatTrial.ColleMaximalEnvelope NivatTrial.ColleLongFaces
open NivatTrial.ColleEnvelopeTranslation NivatTrial.ColleFiniteEnvelope
open scoped Classical
noncomputable section

theorem recenter_recenter (R : Set Lattice) (c d : Lattice) :
    recenter (recenter R c) d = recenter R (c+d) := by
  ext z
  simp only [recenter,Set.mem_ofPred_eq]
  abel_nf

theorem recenter_mono {R S : Set Lattice} (hRS : R ⊆ S) (c : Lattice) :
    recenter R c ⊆ recenter S c := fun _ hz => hRS hz

theorem recenter_forward {R : Set Lattice} {u : Lattice}
    (hu : ForwardInvariant R u) (c : Lattice) : ForwardInvariant (recenter R c) u := by
  intro z hz
  have hh := hu (z+c) hz
  simpa [recenter,add_right_comm] using hh

theorem maximal_agreement_recenter {A : Type*}
    (D : Finset Lattice) (T Q : Set Lattice) (x p : Lattice → A) (c : Lattice)
    (hmax : ∀ R : Set Lattice, T ⊆ R → R ⊆ Q → IsEnvelope D R →
      LongFaces D R → AgreeOn x p R → R = T) :
    ∀ R : Set Lattice, recenter T c ⊆ R → R ⊆ recenter Q c → IsEnvelope D R →
      LongFaces D R → AgreeOn (shift c x) (shift c p) R → R = recenter T c := by
  intro R hTR hRQ hRe hRf hRa
  have hsub : T ⊆ recenter R (-c) := by
    intro z hz
    apply hTR
    simpa [recenter] using hz
  have hamb : recenter R (-c) ⊆ Q := by
    intro z hz
    have he := hRQ hz
    simpa [recenter] using he
  have hagree : AgreeOn x p (recenter R (-c)) := by
    intro z hz
    have he := hRa (z-c) hz
    simpa only [shift_apply,add_sub_cancel] using he
  have heq := hmax (recenter R (-c)) hsub hamb (isEnvelope_recenter hRe (-c))
    (longFaces_recenter hRf (-c)) hagree
  have hh := congrArg (fun S => recenter S c) heq
  change recenter (recenter R (-c)) c = recenter T c at hh
  rw [recenter_recenter,neg_add_cancel] at hh
  simpa only [recenter,add_zero,Set.ofPred_mem_eq] using hh

theorem halfStrip_recenterWindow (T : Finset Lattice) (u c : Lattice) :
    halfStrip (recenterWindow T c) u = recenter (halfStrip T u) c := by
  ext z
  constructor
  · rintro ⟨b,hb,n,rfl⟩
    refine ⟨b+c,(mem_recenterWindow T c b).mp hb,n,?_⟩
    abel
  · rintro ⟨b,hb,n,he⟩
    refine ⟨b-c,(mem_recenterWindow T c (b-c)).mpr (by simpa using hb),n,?_⟩
    have hz : z+c=b+n•u := he
    rw [show z = b+n•u-c by rw [← hz]; abel]
    abel

end
end NivatTrial.ColleMaximalTranslation
