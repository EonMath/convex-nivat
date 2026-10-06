import NivatTrial.ColleLongFaces

/-! Recentring the actual lattice envelopes and their exposed face lengths.
The translation convention matches shifting a configuration by its centre. -/

namespace NivatTrial.ColleEnvelopeTranslation

open NivatTrial.Geometry NivatTrial.Nonexpansive
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleLongFaces
open scoped Classical
noncomputable section

def recenter (R : Set Lattice) (c : Lattice) : Set Lattice := {z | z+c ∈ R}

def recenterWindow (T : Finset Lattice) (c : Lattice) : Finset Lattice :=
  T.image (fun z => z-c)

@[simp] theorem mem_recenterWindow (T : Finset Lattice) (c z : Lattice) :
    z ∈ recenterWindow T c ↔ z+c ∈ T := by
  simp only [recenterWindow,Finset.mem_image]
  constructor
  · rintro ⟨w,hw,rfl⟩
    simpa using hw
  · intro hz
    exact ⟨z+c,hz,by abel⟩

@[simp] theorem coe_recenterWindow (T : Finset Lattice) (c : Lattice) :
    (recenterWindow T c : Set Lattice) = recenter (T : Set Lattice) c := by
  ext z
  exact mem_recenterWindow T c z

theorem supportHull_recenter (D : Finset Lattice) (R : Set Lattice) (c : Lattice) :
    supportHull D (recenter R c) = recenter (supportHull D R) c := by
  ext z
  change z ∈ supportHull D (recenter R c) ↔ z+c ∈ supportHull D R
  rw [mem_supportHull_iff,mem_supportHull_iff]
  constructor
  · intro hz d hd
    obtain ⟨w,hw,hle⟩ := hz d hd
    refine ⟨w+c,hw,?_⟩
    rw [det_add_right,det_add_right]
    omega
  · intro hz d hd
    obtain ⟨w,hw,hle⟩ := hz d hd
    refine ⟨w-c,by simpa [recenter] using hw,?_⟩
    rw [det_sub_right]
    rw [det_add_right] at hle
    omega

theorem isEnvelope_recenter {D : Finset Lattice} {R : Set Lattice}
    (hR : IsEnvelope D R) (c : Lattice) : IsEnvelope D (recenter R c) := by
  change supportHull D (recenter R c) = recenter R c
  rw [supportHull_recenter,hR]

theorem longFaces_recenter {D : Finset Lattice} {R : Set Lattice}
    (hR : LongFaces D R) (c : Lattice) : LongFaces D (recenter R c) := by
  intro d hd z hz hmin
  have hminR : ∀ w ∈ R, det d (z+c) ≤ det d w := by
    intro w hw
    have hwm : w-c ∈ recenter R c := by simpa [recenter] using hw
    have he := hmin (w-c) hwm
    rw [det_sub_right] at he
    rw [det_add_right]
    omega
  obtain ⟨w,hw,hwd,he⟩ := hR d hd (z+c) hz hminR
  refine ⟨w-c,by simpa [recenter] using hw,?_,?_⟩
  · change w-c+d+c ∈ R
    convert hwd using 1
    abel
  · rw [det_add_right] at he
    rw [det_sub_right]
    omega

theorem isEnvelope_recenterWindow {D T : Finset Lattice}
    (hT : IsEnvelope D (T : Set Lattice)) (c : Lattice) :
    IsEnvelope D (recenterWindow T c : Set Lattice) := by
  rw [coe_recenterWindow]
  exact isEnvelope_recenter hT c

theorem longFaces_recenterWindow {D T : Finset Lattice}
    (hT : LongFaces D (T : Set Lattice)) (c : Lattice) :
    LongFaces D (recenterWindow T c : Set Lattice) := by
  rw [coe_recenterWindow]
  exact longFaces_recenter hT c

theorem agreeOn_recenter {A : Type*} {x y : Lattice → A} {R : Set Lattice}
    (hxy : AgreeOn x y R) (c : Lattice) :
    AgreeOn (NivatTrial.Dynamics.shift c x) (NivatTrial.Dynamics.shift c y) (recenter R c) := by
  intro z hz
  simpa [NivatTrial.Dynamics.shift,add_comm] using hxy (z+c) hz

end
end NivatTrial.ColleEnvelopeTranslation
