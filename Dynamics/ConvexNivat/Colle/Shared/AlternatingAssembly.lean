import ConvexNivat.Colle.Shared.SequenceDefinitions
import ConvexNivat.Colle.Shared.MaximalWindows
import ConvexNivat.Colle.Shared.RowCoordinates
import ConvexNivat.Colle.Shared.PositionedWindows

namespace ConvexNivat.Colle
noncomputable section

private theorem row_membership (B : Finset Lattice) (v z : Lattice) :
    z ∈ supportRow B v ↔ z ∈ B ∧ ∀ q ∈ B, det v z ≤ det v q := by
  have hemb (q : Lattice) : realDot (embed q) (normal v) = (det v q : ℝ) := by
    simp only [realDot, embed, normal, det, Int.cast_sub, Int.cast_mul]
    ring
  simp only [supportRow, supportFace, Finset.mem_filter, hemb]
  constructor
  · rintro ⟨hz, hq⟩
    exact ⟨hz, fun q hmem => by exact_mod_cast hq q hmem⟩
  · rintro ⟨hz, hq⟩
    exact ⟨hz, fun q hmem => by exact_mod_cast hq q hmem⟩

private theorem positioned_window_lower (B : Finset Lattice) (v : Lattice)
    (hB : B.Nonempty) (hposition : ∀ z ∈ supportRow B v, det v z = -1) :
    (∃ p ∈ B, det v p = -1) ∧ ∀ z ∈ B, -1 ≤ det v z := by
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image B (det v) hB
  have hrow : p ∈ supportRow B v := (row_membership B v p).mpr ⟨hp, hmin⟩
  have hpheight := hposition p hrow
  exact ⟨⟨p, hp, hpheight⟩, fun z hz => hpheight ▸ hmin z hz⟩

private theorem positioned_halfStrip_lower (B : Finset Lattice) (v : Lattice)
    (hB : B.Nonempty) (hposition : ∀ z ∈ supportRow B v, det v z = -1) :
    ∀ z ∈ halfStrip B v, -1 ≤ det v z := by
  rintro z ⟨g, hg, t, rfl⟩
  have h := (positioned_window_lower B v hB hposition).2 g hg
  change -1 ≤ height v (g + (t : ℤ) • v)
  rw [height_add, height_zsmul, height_self, mul_zero, add_zero]
  exact h

private theorem maximal_window_positioned (S B A : Finset Lattice) (v : Lattice)
    (x y : Configuration ℤ) (hB : B.Nonempty)
    (hposition : ∀ z ∈ supportRow B v, det v z = -1)
    (hmax : maximalAgreementWindow S B A v x y) :
    (∀ z ∈ supportRow A v, det v z = -1) ∧ ∀ z ∈ A, -1 ≤ det v z := by
  have hlow : ∀ z ∈ A, -1 ≤ det v z := fun z hz =>
    positioned_halfStrip_lower B v hB hposition z (hmax.2.2.1 hz)
  refine ⟨?_, hlow⟩
  obtain ⟨p, hp, hpheight⟩ := (positioned_window_lower B v hB hposition).1
  intro z hz
  obtain ⟨hzA, hmin⟩ := (row_membership A v z).mp hz
  have hhi := hmin p (hmax.2.1 hp)
  rw [hpheight] at hhi
  exact le_antisymm hhi (hlow z hzA)

private theorem terminal_difference_nat {S A B : Finset Lattice} {m : ℕ}
    {C : AntipodalEdgeCycle S m} (i : ℤ) (DA : AlignedBoundary C A)
    (DB : AlignedBoundary C B) (hAB : A ⊆ B)
    (hAposition : ∀ z ∈ supportRow A (C.direction i), det (C.direction i) z = -1)
    (hBlower : ∀ z ∈ B, -1 ≤ det (C.direction i) z) :
    ∃ n : ℕ, DB.vertex (i + 1) - (n : ℤ) • C.direction i = DA.vertex (i + 1) := by
  let z := DA.vertex (i + 1)
  have hzA := (row_membership A (C.direction i) z).mp (DA.terminal i)
  have hzB : z ∈ B := hAB hzA.1
  have hrowB : z ∈ supportRow B (C.direction i) := by
    apply (row_membership B (C.direction i) z).mpr
    refine ⟨hzB, ?_⟩
    rw [hAposition z (DA.terminal i)]
    exact hBlower
  have hsegment := (DB.segment_eq i z).mp hrowB
  have hterminal : DB.vertex i + (DB.length i : ℤ) • C.direction i = DB.vertex (i + 1) := by
    rw [add_comm]
    exact (sub_eq_iff_eq_add.mp (DB.edge_eq i)).symm
  have hcoord := (primitive_row_coordinates (C.direction i) (C.primitive i)).2.2
    (DB.vertex i) 0 (DB.length i : ℤ) (by positivity) z
  simp only [zero_smul, add_zero, hterminal] at hcoord
  obtain ⟨k, hk0, hklen, hk⟩ := hcoord.mp hsegment
  let n := ((DB.length i : ℤ) - k).toNat
  refine ⟨n, ?_⟩
  have hn : (n : ℤ) = (DB.length i : ℤ) - k := Int.toNat_of_nonneg (by omega)
  rw [hn, ← hterminal, sub_smul]
  change _ = z
  rw [hk]
  abel

private structure StageData (ξ xper : Configuration ℤ) {S : Finset Lattice}
    {m : ℕ} (C : AntipodalEdgeCycle S m) (i : ℤ) (j : ℕ) where
  B : Finset Lattice
  A : Finset Lattice
  shift : Lattice
  boundary : AlignedBoundary C A
  envB : EnvelopedWindow S B
  envA : EnvelopedWindow S A
  posB : ∀ z ∈ supportRow B (C.direction i), det (C.direction i) z = -1
  exhaustion : ∀ z ∈ integerSquare j, -1 ≤ det (C.direction i) z → z ∈ B
  maximal : maximalAgreementWindow S B A (C.direction i) (translate shift ξ) xper
  mismatch : ¬ AgreesOn (translate shift ξ) xper (halfStrip B (C.direction i))

private theorem rc18_generic
    (ξ xper : Configuration ℤ) (alphabet : Finset ℤ) (_halphabet : ∀ z, ξ z ∈ alphabet)
    (S : Finset Lattice) (_hS : GeneratingSet ξ S) (m : ℕ)
    (C : AntipodalEdgeCycle S m) (i : ℤ) (hxper : xper ∈ OrbitClosure ξ)
    (hperiod : ∃ a : ℤ, a ≠ 0 ∧ HasPeriod xper (a • C.direction i))
    (hmismatch : UnboundedHalfStripMismatch ξ xper S (C.direction i))
    (hmaxProducer : ∀ (B : Finset Lattice), EnvelopedWindow S B →
      (∀ z ∈ supportRow B (C.direction i), det (C.direction i) z = -1) →
      ∀ (x y : Configuration ℤ), x ∈ OrbitClosure ξ → y ∈ OrbitClosure ξ →
      (∃ a : ℤ, a ≠ 0 ∧ HasPeriod y (a • C.direction i)) →
      AgreesOn x y (B : Set Lattice) →
      ¬ AgreesOn x y (halfStrip B (C.direction i)) →
      ∃ A : Finset Lattice, maximalAgreementWindow S B A (C.direction i) x y ∧
        Nonempty (AlignedBoundary C A)) :
    Nonempty (AlternatingWindows ξ xper C i) := by
  classical
  obtain ⟨e, he, hBenvelop, hBmono, hBpos, hBrow, hBleft, hBright, hBunion, hBcapture⟩ :=
    positioned_integer_homothetic_windows C i
  let Bhom (N : ℕ) := positionedHomothetyWindow C i e N
  have hBhom_env (N : ℕ) : EnvelopedWindow S (Bhom N) := hBenvelop N
  have hBhom_pos (N : ℕ) : ∀ z ∈ supportRow (Bhom N) (C.direction i),
      det (C.direction i) z = -1 := hBpos N
  have produce (j : ℕ) (F : Finset Lattice)
      (hF : ∀ z ∈ F, -1 ≤ det (C.direction i) z) :
      ∃ st : StageData ξ xper C i j, F ⊆ st.B := by
    let patch := (integerSquare j).filter (fun z => -1 ≤ det (C.direction i) z)
    have hFpatch : ∀ z ∈ F ∪ patch, -1 ≤ det (C.direction i) z := by
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact hF z hz
      · exact (Finset.mem_filter.mp hz).2
    obtain ⟨N, hN⟩ := hBcapture (F ∪ patch) hFpatch
    obtain ⟨B, hBsub, hBenv, hBpos, u, huagree, hufail⟩ :=
      hmismatch (Bhom N) (hBhom_env N) (hBhom_pos N)
    obtain ⟨A, hAmax, hAbound⟩ := hmaxProducer B hBenv hBpos
      (translate u ξ) xper (orbitClosure_translate_member ξ ξ (orbitClosure_contains_self ξ) u)
      hxper hperiod huagree hufail
    obtain ⟨D⟩ := hAbound
    refine ⟨{
      B := B, A := A, shift := u, boundary := D, envB := hBenv, envA := hAmax.1,
      posB := hBpos, exhaustion := ?_, maximal := hAmax, mismatch := hufail }, ?_⟩
    · intro z hz h
      exact hBsub (hN (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hz, h⟩))))
    · intro z hz
      exact hBsub (hN (Finset.mem_union.mpr (Or.inl hz)))
  obtain ⟨initial, hinitial⟩ := produce 0 ∅ (by simp)
  have step (j : ℕ) (prev : StageData ξ xper C i j) :
      ∃ next : StageData ξ xper C i (j + 1), prev.A ⊆ next.B := by
    apply produce (j + 1) prev.A
    exact (maximal_window_positioned S prev.B prev.A (C.direction i)
      (translate prev.shift ξ) xper prev.envB.1 prev.posB prev.maximal).2
  let state : ∀ j, StageData ξ xper C i j :=
    fun j => Nat.rec initial (fun j prev => (step j prev).choose) j
  have hnest (j : ℕ) : (state j).A ⊆ (state (j + 1)).B :=
    (step j (state j)).choose_spec
  have hmono : Monotone (fun j => (state j).A) := by
    apply monotone_nat_of_le_succ
    intro j
    exact (hnest j).trans (state (j + 1)).maximal.2.1
  have hpositions (j : ℕ) := maximal_window_positioned S (state j).B (state j).A
    (C.direction i) (translate (state j).shift ξ) xper (state j).envB.1 (state j).posB (state j).maximal
  have hnormalise (j : ℕ) : ∃ n : ℕ,
      (state j).boundary.vertex (i + 1) - (n : ℤ) • C.direction i =
        (state 0).boundary.vertex (i + 1) :=
    terminal_difference_nat i (state 0).boundary (state j).boundary
      (hmono (Nat.zero_le j)) (hpositions 0).1 (hpositions j).2
  let normalise (j : ℕ) := (hnormalise j).choose
  have hn (j : ℕ) := (hnormalise j).choose_spec
  have hzero : normalise 0 = 0 := by
    have hsmul : (normalise 0 : ℤ) • C.direction i = 0 := by
      have h := hn 0
      change (state 0).boundary.vertex (i + 1) - (normalise 0 : ℤ) • C.direction i =
        (state 0).boundary.vertex (i + 1) at h
      exact sub_eq_self.mp h
    have hdir := primitive_ne_zero (C.direction i) (C.primitive i)
    have hnormalZ : (normalise 0 : ℤ) = 0 := (smul_eq_zero.mp hsmul).resolve_right hdir
    exact_mod_cast hnormalZ
  refine ⟨{
    B := fun j => (state j).B, A := fun j => (state j).A,
    shift := fun j => (state j).shift, normalise := normalise,
    anchor := (state 0).boundary.vertex (i + 1),
    B_enveloped := fun j => (state j).envB,
    A_enveloped := fun j => (state j).envA,
    boundary := fun j => (state j).boundary,
    base_in_maximal := fun j => (state j).maximal.2.1,
    nesting := hnest,
    positioned := fun j => (state j).posB,
    exhaustion := fun j => (state j).exhaustion,
    maximal := fun j => (state j).maximal,
    mismatch := fun j => (state j).mismatch,
    terminal := hn,
    first_normalise := hzero }⟩

theorem alternating_windows_terminal_normalisation (ξ xper : Configuration ℤ)
    (alphabet : Finset ℤ) (halphabet : ∀ z, ξ z ∈ alphabet)
    (S : Finset Lattice) (hS : GeneratingSet ξ S) (m : ℕ)
    (C : AntipodalEdgeCycle S m) (i : ℤ) (hxper : xper ∈ OrbitClosure ξ)
    (hperiod : ∃ a : ℤ, a ≠ 0 ∧ HasPeriod xper (a • C.direction i))
    (hmismatch : UnboundedHalfStripMismatch ξ xper S (C.direction i)) :
    Nonempty (AlternatingWindows ξ xper C i) := by
  exact rc18_generic ξ xper alphabet halphabet S hS m C i hxper hperiod hmismatch
    (maximal_agreement_enveloped_window ξ alphabet halphabet S hS m C i)

end
end ConvexNivat.Colle
