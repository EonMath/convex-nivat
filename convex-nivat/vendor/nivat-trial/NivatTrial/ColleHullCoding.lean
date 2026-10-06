import NivatTrial.ColleErosionSupport
import NivatTrial.OneSidedRecurrence
import NivatTrial.ColleEnvelopeFiberCoding

/-! Coding a common directional envelope by two overlapping long-faced
windows.  The induction removes one difference factor at a time. -/

namespace NivatTrial.ColleHullCoding

open NivatTrial.Geometry NivatTrial.LatticePolygon
open NivatTrial.ColleEnvelopeGeometry NivatTrial.ColleLongFaces
open NivatTrial.ColleZonotopePlacement NivatTrial.ColleErosionSupport
open NivatTrial.IncrementSupport NivatTrial.PeriodicDifference
open NivatTrial.OneSidedRecurrence
open NivatTrial.ColleEnvelopeFiberCoding
open NivatTrial.ColleMaximalEnvelope NivatTrial.Dynamics NivatTrial.Nonexpansive
open scoped Classical
noncomputable section

def jointEnvelope (hs : List Lattice) (T S : Finset Lattice) : Set Lattice :=
  {z | ∀ d ∈ hs,
    min (lowerSupport T d) (lowerSupport S d) ≤ det d z ∧
    min (lowerSupport T (-d)) (lowerSupport S (-d)) ≤ det (-d) z}

theorem left_subset_jointEnvelope (hs : List Lattice) (T S : Finset Lattice) :
    (T : Set Lattice) ⊆ jointEnvelope hs T S := by
  intro z hz d _
  exact ⟨(min_le_left _ _).trans (lowerSupport_le hz d),
    (min_le_left _ _).trans (lowerSupport_le hz (-d))⟩

theorem right_subset_jointEnvelope (hs : List Lattice) (T S : Finset Lattice) :
    (S : Set Lattice) ⊆ jointEnvelope hs T S := by
  intro z hz d _
  exact ⟨(min_le_right _ _).trans (lowerSupport_le hz d),
    (min_le_right _ _).trans (lowerSupport_le hz (-d))⟩

theorem affine_bound_between (b a r : ℤ) (N n : ℕ) (hn : n ≤ N)
    (hzero : b ≤ a) (hend : b ≤ a+(N:ℤ)*r) : b ≤ a+(n:ℤ)*r := by
  by_cases hr : 0 ≤ r
  · have hh : 0 ≤ (n:ℤ)*r := mul_nonneg (by positivity) hr
    omega
  · have hnn : (n:ℤ) ≤ N := by exact_mod_cast hn
    have hh := mul_le_mul_of_nonpos_right hnn (le_of_lt (lt_of_not_ge hr))
    omega

theorem jointEnvelope_nsmul_between (hs : List Lattice) (T S : Finset Lattice)
    (z u : Lattice) (N : ℕ) (hz : z ∈ jointEnvelope hs T S)
    (hend : z+N•u ∈ jointEnvelope hs T S) (n : ℕ) (hn : n ≤ N) :
    z+n•u ∈ jointEnvelope hs T S := by
  intro d hd
  have hz' := hz d hd
  have he' := hend d hd
  simp only [det_add_right, det_nsmul_right] at he' ⊢
  exact ⟨affine_bound_between _ _ _ N n hn hz'.1 he'.1,
    affine_bound_between _ _ _ N n hn hz'.2 he'.2⟩

theorem common_placement_erodes (hs : List Lattice) (T S : Finset Lattice)
    (u a : Lattice)
    (hplace : ∀ e ∈ offsets (u::hs), a+e ∈ T ∧ a+e ∈ S) :
    ∀ e ∈ offsets hs, a+e ∈ stepErosion T u ∧ a+e ∈ stepErosion S u := by
  intro e he
  have he0 : e ∈ offsets (u::hs) := Finset.mem_union_left _ he
  have heu : u+e ∈ offsets (u::hs) :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e,he,rfl⟩)
  have heq : a+e+u = a+(u+e) := by abel
  exact ⟨(mem_stepErosion T u _).mpr ⟨(hplace e he0).1, by
      rw [heq]; exact (hplace (u+e) heu).1⟩,
    (mem_stepErosion S u _).mpr ⟨(hplace e he0).2, by
      rw [heq]; exact (hplace (u+e) heu).2⟩⟩

theorem eroded_support_bound (T S : Finset Lattice) (u d z : Lattice)
    (hT : T.Nonempty) (hS : S.Nonempty)
    (hTconv : IsLatticeConvex T) (hSconv : IsLatticeConvex S)
    (hTf : LongFaces {u,-u} (T : Set Lattice))
    (hSf : LongFaces {u,-u} (S : Set Lattice))
    (hdu : det d u ≠ 0)
    (hz : min (lowerSupport T d) (lowerSupport S d) ≤ det d z)
    (hzu : min (lowerSupport T d) (lowerSupport S d) ≤ det d (z+u)) :
    min (lowerSupport (stepErosion T u) d) (lowerSupport (stepErosion S u) d)
      ≤ det d z := by
  rw [lowerSupport_stepErosion T u d hT hTconv hTf hdu,
    lowerSupport_stepErosion S u d hS hSconv hSf hdu]
  rw [det_add_right] at hzu
  omega

/-- Every adjacent pair in the large envelope lies in the envelope of the
two eroded windows after the corresponding factor is discarded. -/
theorem adjacent_mem_eroded_jointEnvelope (hs : List Lattice) (T S : Finset Lattice)
    (u z : Lattice) (hT : T.Nonempty) (hS : S.Nonempty)
    (hTconv : IsLatticeConvex T) (hSconv : IsLatticeConvex S)
    (hTf : LongFaces {u,-u} (T : Set Lattice))
    (hSf : LongFaces {u,-u} (S : Set Lattice))
    (hind : ∀ d ∈ hs, det u d ≠ 0)
    (hz : z ∈ jointEnvelope (u::hs) T S)
    (hzu : z+u ∈ jointEnvelope (u::hs) T S) :
    z ∈ jointEnvelope hs (stepErosion T u) (stepErosion S u) := by
  intro d hd
  have hmem : d ∈ u::hs := by simp [hd]
  have hdu : det d u ≠ 0 := by rw [det_swap]; exact neg_ne_zero.mpr (hind d hd)
  have hndu : det (-d) u ≠ 0 := by rw [det_neg_left]; exact neg_ne_zero.mpr hdu
  exact ⟨eroded_support_bound T S u d z hT hS hTconv hSconv hTf hSf hdu
      (hz d hmem).1 (hzu d hmem).1,
    eroded_support_bound T S u (-d) z hT hS hTconv hSconv hTf hSf hndu
      (hz d hmem).2 (hzu d hmem).2⟩

theorem eq_on_nsmul_segment {A : Type*} [AddCommGroup A]
    (hs : List Lattice) (T S : Finset Lattice) (f : Lattice → A)
    (u z : Lattice) (N : ℕ) (hz : z ∈ jointEnvelope hs T S)
    (hend : z+N•u ∈ jointEnvelope hs T S)
    (hinc : ∀ w ∈ jointEnvelope hs T S, w+u ∈ jointEnvelope hs T S →
      increment f u w = 0) : f (z+N•u) = f z := by
  have hall : ∀ n ≤ N, f (z+n•u) = f z := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      have hnN : n ≤ N := by omega
      have hmem := jointEnvelope_nsmul_between hs T S z u N hz hend n hnN
      have hmemp := jointEnvelope_nsmul_between hs T S z u N hz hend (n+1) hn
      have hstep : z+n•u+u = z+(n+1)•u := by rw [add_nsmul, one_nsmul]; abel
      have heq := hinc (z+n•u) hmem (by rwa [hstep])
      change f (z+n•u+u)-f (z+n•u) = 0 at heq
      rw [hstep] at heq
      exact (sub_eq_zero.mp heq).trans (ih hnN)
  exact hall N le_rfl

theorem eq_on_zsmul_segment {A : Type*} [AddCommGroup A]
    (hs : List Lattice) (T S : Finset Lattice) (f : Lattice → A)
    (u z : Lattice) (n : ℤ) (hz : z ∈ jointEnvelope hs T S)
    (hend : z+n•u ∈ jointEnvelope hs T S)
    (hinc : ∀ w ∈ jointEnvelope hs T S, w+u ∈ jointEnvelope hs T S →
      increment f u w = 0) : f (z+n•u) = f z := by
  rcases Int.eq_nat_or_neg n with ⟨N,rfl | rfl⟩
  · simpa only [natCast_zsmul] using eq_on_nsmul_segment hs T S f u z N hz hend hinc
  · have he : z+(-(N:ℤ))•u+N•u = z := by
      rw [neg_smul, natCast_zsmul]
      abel
    have hh := eq_on_nsmul_segment hs T S f u (z+(-(N:ℤ))•u) N hend
      (by rwa [he]) hinc
    rw [he] at hh
    exact hh.symm

theorem zero_mem_offsets (hs : List Lattice) : (0:Lattice) ∈ offsets hs := by
  induction hs with
  | nil => simp [offsets]
  | cons u hs ih => exact Finset.mem_union_left _ ih

/-- Two convex long-faced windows sharing one full subset-sum window code
their common directional envelope. No boundary-shelling assumption is used:
the proof is induction on the actual annihilator factors. -/
theorem zero_on_jointEnvelope {A : Type*} [AddCommGroup A]
    (hs : List Lattice) (hne : ∀ u ∈ hs, u ≠ 0)
    (hind : hs.Pairwise (fun u v => det u v ≠ 0))
    (f : Lattice → A) (hann : iteratedIncrement hs f = 0)
    (T S : Finset Lattice) (hTconv : IsLatticeConvex T) (hSconv : IsLatticeConvex S)
    (hTf : ∀ u ∈ hs, LongFaces {u,-u} (T : Set Lattice))
    (hSf : ∀ u ∈ hs, LongFaces {u,-u} (S : Set Lattice))
    (a : Lattice) (hplace : ∀ e ∈ offsets hs, a+e ∈ T ∧ a+e ∈ S)
    (hzeroT : ∀ z ∈ T, f z = 0) (hzeroS : ∀ z ∈ S, f z = 0) :
    ∀ z ∈ jointEnvelope hs T S, f z = 0 := by
  induction hs generalizing f T S a with
  | nil =>
    intro z _
    exact congrFun hann z
  | cons u hs ih =>
    have ha := hplace 0 (zero_mem_offsets (u::hs))
    simp only [add_zero] at ha
    have hT : T.Nonempty := ⟨a,ha.1⟩
    have hS : S.Nonempty := ⟨a,ha.2⟩
    have huTf := hTf u (by simp)
    have huSf := hSf u (by simp)
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hind
    have htailne : ∀ v ∈ hs, v ≠ 0 := fun v hv => hne v (by simp [hv])
    have hEann : iteratedIncrement hs (increment f u) = 0 := by
      rw [iteratedIncrement_commute]
      exact hann
    have hEzeroT : ∀ z ∈ stepErosion T u, increment f u z = 0 := by
      intro z hz
      obtain ⟨hz,hzu⟩ := (mem_stepErosion T u z).mp hz
      simp only [increment, hzeroT z hz, hzeroT (z+u) hzu, sub_self]
    have hEzeroS : ∀ z ∈ stepErosion S u, increment f u z = 0 := by
      intro z hz
      obtain ⟨hz,hzu⟩ := (mem_stepErosion S u z).mp hz
      simp only [increment, hzeroS z hz, hzeroS (z+u) hzu, sub_self]
    have hE := ih htailne htail (increment f u) hEann
      (stepErosion T u) (stepErosion S u)
      (stepErosion_latticeConvex T u hTconv) (stepErosion_latticeConvex S u hSconv)
      (stepErosion_remaining_faces T u hs hT hTconv hTf hhead)
      (stepErosion_remaining_faces S u hs hS hSconv hSf hhead)
      a (common_placement_erodes hs T S u a hplace) hEzeroT hEzeroS
    have hinc : ∀ w ∈ jointEnvelope (u::hs) T S,
        w+u ∈ jointEnvelope (u::hs) T S → increment f u w = 0 := by
      intro w hw hwu
      exact hE w (adjacent_mem_eroded_jointEnvelope hs T S u w hT hS
        hTconv hSconv huTf huSf hhead hw hwu)
    intro z hz
    obtain ⟨n,hn⟩ := residue_meets_union_of_support_bounds T S u (hne u (by simp))
      hTconv hSconv huTf huSf ⟨a,ha.1,ha.2⟩ z (hz u (by simp)).1 (hz u (by simp)).2
    have hnmem : z+n•u ∈ jointEnvelope (u::hs) T S := by
      rcases Finset.mem_union.mp hn with hn | hn
      · exact left_subset_jointEnvelope (u::hs) T S hn
      · exact right_subset_jointEnvelope (u::hs) T S hn
    have heq := eq_on_zsmul_segment (u::hs) T S f u z n hz hnmem hinc
    rw [← heq]
    rcases Finset.mem_union.mp hn with hn | hn
    · exact hzeroT _ hn
    · exact hzeroS _ hn

theorem supportHull_union_subset_jointEnvelope (D : Finset Lattice)
    (hs : List Lattice) (T S : Finset Lattice)
    (hdirs : ∀ d ∈ hs, d ∈ D ∧ -d ∈ D) :
    supportHull D ((T : Set Lattice) ∪ (S : Set Lattice)) ⊆ jointEnvelope hs T S := by
  intro z hz d hd
  have hb (e : Lattice) (he : e ∈ D) :
      min (lowerSupport T e) (lowerSupport S e) ≤ det e z := by
    apply hz e he
    intro w hw
    rcases hw with hw | hw
    · exact (min_le_left _ _).trans (lowerSupport_le hw e)
    · exact (min_le_right _ _).trans (lowerSupport_le hw e)
  exact ⟨hb d (hdirs d hd).1,hb (-d) (hdirs d hd).2⟩

/-- Alphabet-valued version of the coding theorem for two actual points
in the original language hull. -/
theorem agreement_supportHull_union {A : Type*}
    (θ : Lattice → A) (code : A → ℤ) (hcode : Function.Injective code)
    (hs : List Lattice) (hne : ∀ u ∈ hs, u ≠ 0)
    (hind : hs.Pairwise (fun u v => det u v ≠ 0))
    (hann : iteratedIncrement hs (encode code θ) = 0)
    (x p : Lattice → A) (hx : x ∈ languageHull θ) (hp : p ∈ languageHull θ)
    (D T S : Finset Lattice) (hdirs : ∀ d ∈ hs, d ∈ D ∧ -d ∈ D)
    (hTconv : IsLatticeConvex T) (hSconv : IsLatticeConvex S)
    (hTf : ∀ u ∈ hs, LongFaces {u,-u} (T : Set Lattice))
    (hSf : ∀ u ∈ hs, LongFaces {u,-u} (S : Set Lattice))
    (a : Lattice) (hplace : ∀ e ∈ offsets hs, a+e ∈ T ∧ a+e ∈ S)
    (hagreeT : AgreeOn x p (T : Set Lattice))
    (hagreeS : AgreeOn x p (S : Set Lattice)) :
    AgreeOn x p (supportHull D ((T : Set Lattice) ∪ (S : Set Lattice))) := by
  have hxann := iteratedIncrement_passes_to_languageHull hs (encode code θ)
    (encode code x) (encode_mem_languageHull code hx) hann
  have hpann := iteratedIncrement_passes_to_languageHull hs (encode code θ)
    (encode code p) (encode_mem_languageHull code hp) hann
  have hdann : iteratedIncrement hs (encode code x-encode code p) = 0 := by
    rw [iteratedIncrement_sub, hxann, hpann, sub_self]
  have hzT : ∀ z ∈ T, (encode code x-encode code p) z = 0 := by
    intro z hz
    change code (x z)-code (p z) = 0
    rw [hagreeT z hz, sub_self]
  have hzS : ∀ z ∈ S, (encode code x-encode code p) z = 0 := by
    intro z hz
    change code (x z)-code (p z) = 0
    rw [hagreeS z hz, sub_self]
  have hz := zero_on_jointEnvelope hs hne hind (encode code x-encode code p) hdann
    T S hTconv hSconv hTf hSf a hplace hzT hzS
  intro z hmem
  have heq := hz z (supportHull_union_subset_jointEnvelope D hs T S hdirs hmem)
  exact hcode (sub_eq_zero.mp heq)

/-- A common old long-faced window supplies the required placement
automatically. This is the form used for a fixed early window and a later
member of an increasing maximal-agreement sequence. -/
theorem agreement_supportHull_union_of_common_window {A : Type*}
    (θ : Lattice → A) (code : A → ℤ) (hcode : Function.Injective code)
    (hs : List Lattice) (hne : ∀ u ∈ hs, u ≠ 0)
    (hind : hs.Pairwise (fun u v => det u v ≠ 0))
    (hann : iteratedIncrement hs (encode code θ) = 0)
    (x p : Lattice → A) (hx : x ∈ languageHull θ) (hp : p ∈ languageHull θ)
    (D T S W : Finset Lattice) (hdirs : ∀ d ∈ hs, d ∈ D ∧ -d ∈ D)
    (hTconv : IsLatticeConvex T) (hSconv : IsLatticeConvex S)
    (hTf : ∀ u ∈ hs, LongFaces {u,-u} (T : Set Lattice))
    (hSf : ∀ u ∈ hs, LongFaces {u,-u} (S : Set Lattice))
    (hW : W.Nonempty) (hWconv : IsLatticeConvex W)
    (hWf : ∀ u ∈ hs, LongFaces {u,-u} (W : Set Lattice))
    (hWT : W ⊆ T) (hWS : W ⊆ S)
    (hagreeT : AgreeOn x p (T : Set Lattice))
    (hagreeS : AgreeOn x p (S : Set Lattice)) :
    AgreeOn x p (supportHull D ((T : Set Lattice) ∪ (S : Set Lattice))) := by
  obtain ⟨a,ha⟩ := exists_offsets_placement hs W hW hWconv hWf hind
  exact agreement_supportHull_union θ code hcode hs hne hind hann x p hx hp
    D T S hdirs hTconv hSconv hTf hSf a
    (fun e he => ⟨hWT (ha e he),hWS (ha e he)⟩) hagreeT hagreeS

end
end NivatTrial.ColleHullCoding
