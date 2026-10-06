import NivatTrial.ColleEnvelopeGeometry

/-! Maximal agreement in actual envelopes with finitely many normals.
Unbounded envelopes are permitted. The proof takes the union of a chain,
and proves that this union is still an envelope using finiteness of the
normal set and discreteness of the integer support levels. -/

namespace NivatTrial.ColleMaximalEnvelope

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.RegionGeometry
open NivatTrial.ColleGenerating NivatTrial.ColleEnvelopeGeometry
open NivatTrial.Nonexpansive
open scoped Classical
noncomputable section

abbrev Plane := ℝ × ℝ

def supportHull (D : Finset Lattice) (R : Set Lattice) : Set Lattice :=
  {z | ∀ h ∈ D, ∀ b : ℤ, (∀ w ∈ R, b ≤ det h w) → b ≤ det h z}

def IsEnvelope (D : Finset Lattice) (R : Set Lattice) : Prop := supportHull D R = R

theorem subset_supportHull (D : Finset Lattice) (R : Set Lattice) :
    R ⊆ supportHull D R := fun z hz _ _ _ hb => hb z hz

theorem supportHull_mono (D : Finset Lattice) {R T : Set Lattice} (hRT : R ⊆ T) :
    supportHull D R ⊆ supportHull D T :=
  fun _ hz h hh b hb => hz h hh b (fun w hw => hb w (hRT hw))

theorem mem_supportHull_iff (D : Finset Lattice) (R : Set Lattice) (z : Lattice) :
    z ∈ supportHull D R ↔ ∀ h ∈ D, ∃ w ∈ R, det h w ≤ det h z := by
  constructor
  · intro hz h hh
    by_contra hn
    have hbound : ∀ w ∈ R, det h z + 1 ≤ det h w := by
      intro w hw
      have hlt : ¬det h w ≤ det h z := fun he => hn ⟨w,hw,he⟩
      omega
    have := hz h hh (det h z+1) hbound
    omega
  · intro hz h hh b hb
    obtain ⟨w,hw,hle⟩ := hz h hh
    exact (hb w hw).trans hle

theorem supportHull_idempotent (D : Finset Lattice) (R : Set Lattice) :
    IsEnvelope D (supportHull D R) := by
  apply Set.Subset.antisymm _ (subset_supportHull D _)
  intro z hz h hh b hb
  exact hz h hh b (fun w hw => hw h hh b hb)

theorem envelope_isEnvelope (D : Finset Lattice) (b : Lattice → ℤ) :
    IsEnvelope D (envelope D b) := by
  apply Set.Subset.antisymm _ (subset_supportHull D _)
  intro z hz h hh
  exact hz h hh (b h) (fun w hw => hw h hh)

theorem supportHull_finset (D B : Finset Lattice) (hB : B.Nonempty) :
    supportHull D (B : Set Lattice) = envelope D (lowerSupport B) := by
  ext z
  constructor
  · intro hz h hh
    exact hz h hh (lowerSupport B h) (fun w hw => lowerSupport_le hw h)
  · intro hz h hh t ht
    obtain ⟨w,hw,he⟩ := lowerSupport_attained B hB h
    exact (by rw [← he]; exact ht w hw : t ≤ lowerSupport B h).trans (hz h hh)

theorem IsEnvelope.eq_finite_envelope {D B : Finset Lattice}
    (hB : B.Nonempty) (hclosed : IsEnvelope D (B : Set Lattice)) :
    (B : Set Lattice) = envelope D (lowerSupport B) := by
  rw [← supportHull_finset D B hB]
  exact hclosed.symm

theorem supportHull_latticeConvex (D : Finset Lattice) (R : Set Lattice) :
    LatticeConvexRegion (supportHull D R) := by
  let C : Set Plane := {x | ∀ h ∈ D, ∀ b : ℤ,
    (∀ w ∈ R, b ≤ det h w) → (b:ℝ) ≤ linearScore (embed h) x}
  have hC : Convex ℝ C := by
    intro x hx y hy a c ha hc hac h hh b hb
    have hx' := hx h hh b hb
    have hy' := hy h hh b hb
    simp only [map_add,map_smul,smul_eq_mul]
    calc
      (b:ℝ) = a*(b:ℝ)+c*(b:ℝ) := by rw [← add_mul,hac,one_mul]
      _ ≤ a*linearScore (embed h) x+c*linearScore (embed h) y :=
        add_le_add (mul_le_mul_of_nonneg_left hx' ha) (mul_le_mul_of_nonneg_left hy' hc)
  refine ⟨C,hC,?_⟩
  ext z
  change (∀ h ∈ D, ∀ b : ℤ, (∀ w ∈ R, b ≤ det h w) → b ≤ det h z) ↔
    ∀ h ∈ D, ∀ b : ℤ, (∀ w ∈ R, b ≤ det h w) →
      (b:ℝ) ≤ linearScore (embed h) (embed z)
  simp only [linearScore_embed_det,Int.cast_le]

theorem IsEnvelope.latticeConvex {D : Finset Lattice} {R : Set Lattice}
    (hR : IsEnvelope D R) : LatticeConvexRegion R := by
  rw [← hR]
  exact supportHull_latticeConvex D R

/-- A single member of a chain contains support witnesses for every
direction in a finite set. -/
theorem exists_common_support_witnesses (D : Finset Lattice)
    (c : Set (Set Lattice)) (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty)
    (z : Lattice)
    (hw : ∀ h ∈ D, ∃ R ∈ c, ∃ w ∈ R, det h w ≤ det h z) :
    ∃ R ∈ c, ∀ h ∈ D, ∃ w ∈ R, det h w ≤ det h z := by
  induction D using Finset.induction_on with
  | empty =>
    obtain ⟨R,hR⟩ := hne
    exact ⟨R,hR,by simp⟩
  | @insert h D hnot ih =>
    obtain ⟨R,hR,hRW⟩ := ih (fun k hk => hw k (by simp [hk]))
    obtain ⟨T,hT,w,hwT,hwdet⟩ := hw h (by simp)
    rcases hc.total hR hT with hRT | hTR
    · refine ⟨T,hT,?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact ⟨w,hwT,hwdet⟩
      · obtain ⟨u,hu,hudet⟩ := hRW k hk
        exact ⟨u,hRT hu,hudet⟩
    · refine ⟨R,hR,?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact ⟨w,hTR hwT,hwdet⟩
      · exact hRW k hk

theorem isEnvelope_sUnion_chain (D : Finset Lattice)
    (c : Set (Set Lattice)) (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty)
    (henv : ∀ R ∈ c, IsEnvelope D R) : IsEnvelope D (⋃₀ c) := by
  apply Set.Subset.antisymm _ (subset_supportHull D _)
  intro z hz
  have hw (h : Lattice) (hh : h ∈ D) : ∃ R ∈ c, ∃ w ∈ R, det h w ≤ det h z := by
    obtain ⟨w,hw,hle⟩ := (mem_supportHull_iff D (⋃₀ c) z).mp hz h hh
    obtain ⟨R,hR,hwR⟩ := Set.mem_sUnion.mp hw
    exact ⟨R,hR,w,hwR,hle⟩
  obtain ⟨R,hR,hwR⟩ := exists_common_support_witnesses D c hc hne z hw
  have hzR : z ∈ supportHull D R := (mem_supportHull_iff D R z).mpr hwR
  rw [henv R hR] at hzR
  exact Set.mem_sUnion.mpr ⟨R,hR,hzR⟩

/-- The maximal agreement region is obtained by Zorn from actual pointwise
agreement, not supplied as a premise. No finiteness or edge length is claimed. -/
theorem exists_maximal_agreement_envelope {A : Type*}
    (D : Finset Lattice) (x y : Lattice → A) (B Q : Set Lattice)
    (hB : IsEnvelope D B) (hBQ : B ⊆ Q) (hagree : AgreeOn x y B) :
    ∃ R : Set Lattice, B ⊆ R ∧ R ⊆ Q ∧ IsEnvelope D R ∧ AgreeOn x y R ∧
      ∀ T : Set Lattice, R ⊆ T → T ⊆ Q → IsEnvelope D T → AgreeOn x y T → T = R := by
  let C : Set (Set Lattice) := {R | B ⊆ R ∧ R ⊆ Q ∧ IsEnvelope D R ∧ AgreeOn x y R}
  have hBC : B ∈ C := ⟨Set.Subset.rfl,hBQ,hB,hagree⟩
  have hchain (c : Set (Set Lattice)) (hc : c ⊆ C)
      (hlinear : IsChain (· ⊆ ·) c) (hne : c.Nonempty) :
      ∃ R ∈ C, ∀ T ∈ c, T ⊆ R := by
    refine ⟨⋃₀ c,?_,fun T hT z hz => Set.mem_sUnion.mpr ⟨T,hT,hz⟩⟩
    refine ⟨?_,?_,isEnvelope_sUnion_chain D c hlinear hne (fun T hT => (hc hT).2.2.1),?_⟩
    · obtain ⟨T,hT⟩ := hne
      intro z hz
      exact Set.mem_sUnion.mpr ⟨T,hT,(hc hT).1 hz⟩
    · rintro z ⟨T,hT,hz⟩
      exact (hc hT).2.1 hz
    · rintro z ⟨T,hT,hz⟩
      exact (hc hT).2.2.2 z hz
  obtain ⟨R,hBR,hmax⟩ := zorn_subset_nonempty C hchain B hBC
  have hR := hmax.prop
  refine ⟨R,hBR,hR.2.1,hR.2.2.1,hR.2.2.2,?_⟩
  intro T hRT hTQ hTenv hTxy
  exact (hmax.eq_of_subset ⟨hBR.trans hRT,hTQ,hTenv,hTxy⟩ hRT).symm

end
end NivatTrial.ColleMaximalEnvelope
