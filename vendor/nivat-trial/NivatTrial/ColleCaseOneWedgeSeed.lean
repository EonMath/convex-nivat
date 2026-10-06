import NivatTrial.ColleWedgeReference
import NivatTrial.ColleEnvelopeTranslation
import NivatTrial.ColleEnvelopeExpansion

/-! Finite long-faced seeds inside an actual periodic wedge. Each finite
forward displacement of the seed admits a common closed long-faced window
which remains inside the same wedge. -/

namespace NivatTrial.ColleCaseOneWedgeSeed

open NivatTrial.Geometry NivatTrial.LatticePolygon NivatTrial.RegionGeometry
open NivatTrial.ColleCaseOne NivatTrial.ColleEnvelopeGeometry
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleLongFaces
open NivatTrial.ColleEnvelopeTranslation NivatTrial.ColleEnvelopeExpansion
open NivatTrial.ColleZonotopeEnvelope
open scoped Classical
noncomputable section

theorem finite_window_translate_into_wedge
    (T : Finset Lattice)
    (u k : Lattice) (huk : 0 < det u k) (c : ℤ) :
    ∃ a : Lattice, ∀ z ∈ T, z+a ∈ wedge u k c := by
  obtain ⟨N,hN⟩ := exists_nat_gt (-(lowerSupport T u))
  obtain ⟨M,hM⟩ := exists_nat_gt (-(lowerSupport T (-k))-c)
  refine ⟨N•k+M•u,?_⟩
  intro z hz
  have hlu := lowerSupport_le hz u
  have hlk := lowerSupport_le hz (-k)
  have hNu : (-(lowerSupport T u):ℤ) < N := hN
  have hMk : (-(lowerSupport T (-k))-c:ℤ) < M := hM
  have hnn : (0:ℤ) ≤ N := by positivity
  have hmm : (0:ℤ) ≤ M := by positivity
  have hku : det k u = -det u k := det_swap k u
  change 0 ≤ det u (z+(N•k+M•u)) ∧ det k (z+(N•k+M•u)) ≤ c
  simp only [det_add_right,det_nsmul_right,det_self,mul_zero,add_zero]
  rw [hku]
  rw [det_neg_left] at hlk
  constructor <;> nlinarith

theorem exists_long_seed_in_wedge {n : ℕ} (hn : 2 ≤ n)
    (v : Fin n → Lattice)
    (hpair : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0)
    (u k : Lattice) (huk : 0 < det u k) (c : ℤ) :
    ∃ W : Finset Lattice, W.Nonempty ∧ IsLatticeConvex W ∧
      IsEnvelope (signedDirections v) (W : Set Lattice) ∧
      LongFaces (signedDirections v) (W : Set Lattice) ∧
      (W : Set Lattice) ⊆ wedge u k c := by
  obtain ⟨T,hzero,hconv,henv,hfaces⟩ :=
    exists_finite_long_envelope hn v hpair ({0} : Finset Lattice)
  have hT : T.Nonempty := ⟨0,hzero (by simp)⟩
  obtain ⟨a,ha⟩ := finite_window_translate_into_wedge T u k huk c
  let W := recenterWindow T (-a)
  have hW : W.Nonempty := by
    obtain ⟨z,hz⟩ := hT
    refine ⟨z+a,?_⟩
    change z+a ∈ recenterWindow T (-a)
    rw [mem_recenterWindow]
    simpa [add_assoc] using hz
  refine ⟨W,hW,?_,isEnvelope_recenterWindow henv (-a),
    longFaces_recenterWindow hfaces (-a),?_⟩
  · exact latticeConvex_finset_of_region W
      ((isEnvelope_recenterWindow henv (-a)).latticeConvex)
  · intro z hz
    have hzT : z-a ∈ T := by
      change z ∈ recenterWindow T (-a) at hz
      rw [mem_recenterWindow] at hz
      simpa [sub_eq_add_neg] using hz
    have hzEq : z-a+a = z := by abel
    rw [← hzEq]
    exact ha (z-a) hzT

theorem wedge_isEnvelope (D : Finset Lattice) (u k : Lattice) (c : ℤ)
    (hu : u ∈ D) (hnk : -k ∈ D) :
    IsEnvelope D (wedge u k c) := by
  apply Set.Subset.antisymm _ (subset_supportHull D _)
  intro z hz
  change 0 ≤ det u z ∧ det k z ≤ c
  have hfirst : (0:ℤ) ≤ det u z :=
    hz u hu 0 (fun w hw => hw.1)
  have hsecond : -c ≤ det (-k) z := by
    apply hz (-k) hnk (-c)
    intro w hw
    have hkw : det k w ≤ c := hw.2
    rw [det_neg_left]
    omega
  rw [det_neg_left] at hsecond
  exact ⟨hfirst,by omega⟩

theorem exists_forward_seed_window
    (D W : Finset Lattice) (u k q : Lattice) (c b : ℤ)
    (huk : 0 < det u k) (hu : u ∈ D) (hnu : -u ∈ D)
    (hk : k ∈ D) (hnk : -k ∈ D)
    (hW : W.Nonempty)
    (hWfaces : LongFaces D (W : Set Lattice))
    (hWsub : (W : Set Lattice) ⊆ wedge u k c)
    (hWbottom : ∀ z ∈ W, b ≤ det u z)
    (hq : ForwardInvariant (wedge u k c) q)
    (hqu : 0 ≤ det u q) (n : ℕ) :
    ∃ T : Finset Lattice, W ⊆ T ∧
      (∀ z ∈ W, z+n•q ∈ T) ∧ T.Nonempty ∧
      IsLatticeConvex T ∧ IsEnvelope D (T : Set Lattice) ∧
      LongFaces D (T : Set Lattice) ∧
      (T : Set Lattice) ⊆ wedge u k c ∧
      ∀ z ∈ T, b ≤ det u z := by
  let V := recenterWindow W (-(n•q))
  let F := W ∪ V
  have hF : F.Nonempty := hW.mono Finset.subset_union_left
  obtain ⟨T,hFT,hconv,heq,_⟩ := exists_finite_envelope D F hF u k
    (ne_of_gt huk) hu hnu hk hnk
  have hVfaces : LongFaces D (V : Set Lattice) :=
    longFaces_recenterWindow hWfaces (-(n•q))
  have hFfaces : LongFaces D (F : Set Lattice) := by
    rw [Finset.coe_union]
    exact longFaces_union hWfaces hVfaces
  have hTfaces : LongFaces D (T : Set Lattice) := by
    rw [heq,← supportHull_finset D F hF]
    exact hFfaces.supportHull
  have hFsub : (F : Set Lattice) ⊆ wedge u k c := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzW | hzV
    · exact hWsub hzW
    · have hbase : z+(-(n•q)) ∈ W := by
        change z ∈ recenterWindow W (-(n•q)) at hzV
        rwa [mem_recenterWindow] at hzV
      have hmem := hq.nsmul n (z+(-(n•q))) (hWsub hbase)
      convert hmem using 1
      abel
  have hTsub : (T : Set Lattice) ⊆ wedge u k c := by
    rw [heq,← supportHull_finset D F hF]
    intro z hz
    rw [← wedge_isEnvelope D u k c hu hnk]
    exact supportHull_mono D hFsub hz
  have hFbottom : ∀ z ∈ F, b ≤ det u z := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzW | hzV
    · exact hWbottom z hzW
    · have hbase : z+(-(n•q)) ∈ W := by
        change z ∈ recenterWindow W (-(n•q)) at hzV
        rwa [mem_recenterWindow] at hzV
      have hscore := hWbottom _ hbase
      have hn : (0:ℤ) ≤ n := by positivity
      have hstep : 0 ≤ (n:ℤ)*det u q := mul_nonneg hn hqu
      have heq : z+(-(n•q))+n•q = z := by abel
      rw [← heq,det_add_right,det_nsmul_right]
      omega
  have hTbottom : ∀ z ∈ T, b ≤ det u z := by
    intro z hz
    change z ∈ (T : Set Lattice) at hz
    rw [heq,← supportHull_finset D F hF] at hz
    exact hz u hu b (fun w hw => hFbottom w hw)
  refine ⟨T,?_,?_,hF.mono hFT,hconv,?_,hTfaces,hTsub,hTbottom⟩
  · exact Finset.Subset.trans Finset.subset_union_left hFT
  · intro z hz
    apply hFT
    apply Finset.mem_union_right
    change z+n•q ∈ recenterWindow W (-(n•q))
    rw [mem_recenterWindow]
    simpa [add_assoc] using hz
  · rw [heq]
    exact envelope_isEnvelope D (lowerSupport F)

end
end NivatTrial.ColleCaseOneWedgeSeed
