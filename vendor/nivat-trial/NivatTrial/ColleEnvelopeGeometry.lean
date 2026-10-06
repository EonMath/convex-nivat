import NivatTrial.ColleGenerating
import NivatTrial.RegionGeometry

/-! Actual lattice envelopes in finitely many prescribed integer directions.
The inequalities give convexity and finite support data. Edge-length bounds
are additional requirements; they are not hidden in this definition. -/

namespace NivatTrial.ColleEnvelopeGeometry

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.LatticePolygon
open NivatTrial.ColleGenerating NivatTrial.RegionGeometry
open scoped Classical
noncomputable section

abbrev Plane := ℝ × ℝ

def envelope (D : Finset Lattice) (b : Lattice → ℤ) : Set Lattice :=
  {z | ∀ h ∈ D, b h ≤ det h z}

@[simp] theorem mem_envelope (D : Finset Lattice) (b : Lattice → ℤ) (z : Lattice) :
    z ∈ envelope D b ↔ ∀ h ∈ D, b h ≤ det h z := Iff.rfl

theorem det_neg_left (h z : Lattice) : det (-h) z = -det h z := by
  simp [det]
  ring

theorem linearScore_embed_det (h z : Lattice) :
    linearScore (embed h) (embed z) = (det h z : ℤ) := by
  simp [linearScore,embed,det]

theorem envelope_antitone (D : Finset Lattice) {b c : Lattice → ℤ}
    (hbc : ∀ h ∈ D, b h ≤ c h) : envelope D c ⊆ envelope D b :=
  fun _ hz h hh => (hbc h hh).trans (hz h hh)

theorem envelope_inter (D : Finset Lattice) (b c : Lattice → ℤ) :
    envelope D (fun h => max (b h) (c h)) = envelope D b ∩ envelope D c := by
  ext z
  simp only [mem_envelope,Set.mem_inter_iff,max_le_iff]
  constructor
  · intro hz
    exact ⟨fun h hh => (hz h hh).1,fun h hh => (hz h hh).2⟩
  · rintro ⟨hb,hc⟩ h hh
    exact ⟨hb h hh,hc h hh⟩

theorem envelope_latticeConvex (D : Finset Lattice) (b : Lattice → ℤ) :
    LatticeConvexRegion (envelope D b) := by
  let C : Set Plane := {x | ∀ h ∈ D, (b h : ℝ) ≤ linearScore (embed h) x}
  have hC : Convex ℝ C := by
    intro x hx y hy a c ha hc hac h hh
    have hx' := hx h hh
    have hy' := hy h hh
    simp only [map_add,map_smul,smul_eq_mul]
    calc
      (b h : ℝ) = a * (b h : ℝ) + c * (b h : ℝ) := by rw [← add_mul,hac,one_mul]
      _ ≤ a * linearScore (embed h) x + c * linearScore (embed h) y :=
        add_le_add (mul_le_mul_of_nonneg_left hx' ha) (mul_le_mul_of_nonneg_left hy' hc)
  refine ⟨C,hC,?_⟩
  ext z
  change (∀ h ∈ D, b h ≤ det h z) ↔
    ∀ h ∈ D, (b h : ℝ) ≤ linearScore (embed h) (embed z)
  simp only [linearScore_embed_det,Int.cast_le]

theorem envelope_finite (D : Finset Lattice) (b : Lattice → ℤ)
    (h k : Lattice) (hind : det h k ≠ 0)
    (hh : h ∈ D) (hnh : -h ∈ D) (hk : k ∈ D) (hnk : -k ∈ D) :
    (envelope D b).Finite := by
  apply (finite_strip_intersection h k hind (b h) (-b (-h)) (b k) (-b (-k))).subset
  intro z hz
  have h1 := hz h hh
  have h2 := hz (-h) hnh
  have h3 := hz k hk
  have h4 := hz (-k) hnk
  rw [det_neg_left] at h2 h4
  exact ⟨⟨h1,by omega⟩,⟨h3,by omega⟩⟩

theorem latticeConvex_finset_of_region (S : Finset Lattice)
    (hS : LatticeConvexRegion (S : Set Lattice)) : IsLatticeConvex S := by
  obtain ⟨C,hC,hSC⟩ := hS
  intro z
  constructor
  · intro hz
    have hsub : embed '' (S : Set Lattice) ⊆ C := by
      rintro _ ⟨w,hw,rfl⟩
      have hm : w ∈ embed ⁻¹' C := by rwa [← hSC]
      exact hm
    have hm : embed z ∈ C := convexHull_min hsub hC hz
    change z ∈ (S : Set Lattice)
    rw [hSC]
    exact hm
  · exact mem_windowHull_of_mem S

def lowerSupport (S : Finset Lattice) (h : Lattice) : ℤ :=
  if hS : S.Nonempty then (S.image (det h)).min' (hS.image _) else 0

theorem lowerSupport_le {S : Finset Lattice} {z : Lattice} (hz : z ∈ S)
    (h : Lattice) : lowerSupport S h ≤ det h z := by
  rw [lowerSupport,dif_pos ⟨z,hz⟩]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨z,hz,rfl⟩)

theorem lowerSupport_attained (S : Finset Lattice) (hS : S.Nonempty) (h : Lattice) :
    ∃ z ∈ S, det h z = lowerSupport S h := by
  obtain ⟨z,hz,he⟩ := Finset.mem_image.mp (Finset.min'_mem (S.image (det h)) (hS.image _))
  exact ⟨z,hz,by simpa [lowerSupport,hS] using he⟩

theorem subset_envelope (D S : Finset Lattice) :
    (S : Set Lattice) ⊆ envelope D (lowerSupport S) :=
  fun _ hz h _ => lowerSupport_le hz h

/-- This is the smallest intersection of the prescribed half-planes that
contains the given nonempty finite set. -/
theorem envelope_minimal (D S : Finset Lattice) (hS : S.Nonempty)
    (b : Lattice → ℤ) (hsub : (S : Set Lattice) ⊆ envelope D b) :
    envelope D (lowerSupport S) ⊆ envelope D b := by
  apply envelope_antitone D
  intro h hh
  obtain ⟨z,hz,he⟩ := lowerSupport_attained S hS h
  rw [← he]
  exact hsub hz h hh

theorem envelope_mono (D : Finset Lattice) {S T : Finset Lattice}
    (hS : S.Nonempty) (hST : S ⊆ T) :
    envelope D (lowerSupport S) ⊆ envelope D (lowerSupport T) :=
  envelope_minimal D S hS _ (fun _ hz => subset_envelope D T (hST hz))

/-- Enclosing a finite set introduces no new support levels in the
prescribed directions: every old supporting face remains attained. -/
theorem exists_finite_envelope (D S : Finset Lattice) (hS : S.Nonempty)
    (h k : Lattice) (hind : det h k ≠ 0)
    (hh : h ∈ D) (hnh : -h ∈ D) (hk : k ∈ D) (hnk : -k ∈ D) :
    ∃ T : Finset Lattice, S ⊆ T ∧ IsLatticeConvex T ∧
      (T : Set Lattice) = envelope D (lowerSupport S) ∧
      ∀ a ∈ D, lowerSupport T a = lowerSupport S a := by
  have hf := envelope_finite D (lowerSupport S) h k hind hh hnh hk hnk
  let T := hf.toFinset
  have hT : (T : Set Lattice) = envelope D (lowerSupport S) := hf.coe_toFinset
  have hST : S ⊆ T := by
    intro z hz
    have hm := subset_envelope D S hz
    rwa [← hT] at hm
  refine ⟨T,hST,latticeConvex_finset_of_region T ?_,hT,?_⟩
  · rw [hT]
    exact envelope_latticeConvex D (lowerSupport S)
  · intro a ha
    apply le_antisymm
    · obtain ⟨z,hz,he⟩ := lowerSupport_attained S hS a
      rw [← he]
      exact lowerSupport_le (hST hz) a
    · obtain ⟨z,hz,he⟩ := lowerSupport_attained T (hS.mono hST) a
      rw [← he]
      have hm : z ∈ envelope D (lowerSupport S) := by rwa [← hT]
      exact hm a ha

theorem envelope_translate (D : Finset Lattice) (b : Lattice → ℤ) (u : Lattice) :
    envelope D (fun h => b h + det h u) = (fun z => z+u) '' envelope D b := by
  ext z
  constructor
  · intro hz
    refine ⟨z-u,?_,by simp⟩
    intro h hh
    rw [det_sub_right]
    have := hz h hh
    dsimp at this
    omega
  · rintro ⟨z,hz,rfl⟩ h hh
    rw [det_add_right]
    have := hz h hh
    dsimp
    omega

theorem envelope_forward (D : Finset Lattice) (b : Lattice → ℤ) (u : Lattice)
    (hu : ∀ h ∈ D, 0 ≤ det h u) : ForwardInvariant (envelope D b) u := by
  intro z hz h hh
  rw [det_add_right]
  exact (hz h hh).trans (le_add_of_nonneg_right (hu h hh))

end
end NivatTrial.ColleEnvelopeGeometry
