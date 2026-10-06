import NivatTrial.RowDetermination
import NivatTrial.BalancedTransforms

/-! The actual ambiguity propagation argument of Appendix D.7 in horizontal
coordinates. Language-hull membership equals membership in the usual orbit
closure for the finite discrete alphabet. -/

namespace NivatTrial.BalancedPropagation

open NivatTrial.Dynamics NivatTrial.Periodicity NivatTrial.MorseHedlund
open NivatTrial.AmbiguityPropagation NivatTrial.RowDetermination
open NivatTrial.BalancedWindows
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ

def height : G →+ ℤ := AddMonoidHom.snd ℤ ℤ

def strip (a b : ℤ) : Set G := {z | a ≤ z.2 ∧ z.2 ≤ b}

def StripPeriod {A : Type*} (θ : G → A) (a b : ℤ) (Q : ℕ) : Prop :=
  ∀ z ∈ strip a b, θ (z + step (Q : ℤ)) = θ z

variable {A : Type*} [Fintype A]

def PlusAmbiguity (θ : G → A) (a b : ℤ) : Prop :=
  ∃ x ∈ languageHull θ,
    (∀ z : G, a ≤ z.2 → z.2 < b → x z = θ z) ∧
    ∃ z : G, z.2 = b ∧ x z ≠ θ z

theorem point_on_row (e z : G) (hz : z.2 = e.2) :
    e + step (z.1 - e.1) = z := by
  ext <;> simp [step, hz]

theorem row_period_iff (θ : G → A) (e : G) (Q : ℕ) :
    IsPeriod (rowSequence θ e horizontal) (Q : ℤ) ↔
      ∀ z : G, z.2 = e.2 → θ (z + step (Q : ℤ)) = θ z := by
  constructor
  · intro hp z hz
    have h := hp (z.1 - e.1)
    simp only [rowSequence_horizontal_apply] at h
    rw [step_add, ← add_assoc, point_on_row e z hz] at h
    exact h
  · intro hp i
    have h := hp (e + step i) (by simp [step])
    simpa [rowSequence_horizontal_apply, step,
      add_assoc, add_comm, add_left_comm] using h

theorem StripPeriod.multiple {θ : G → A} {a b : ℤ} {Q q : ℕ}
    (hp : StripPeriod θ a b Q) (hdiv : Q ∣ q) : StripPeriod θ a b q := by
  obtain ⟨m, rfl⟩ := hdiv
  intro z hz
  have hr : IsPeriod (rowSequence θ z horizontal) (Q : ℤ) :=
    (row_period_iff θ z Q).mpr (fun w hw => hp w (by simpa [strip, hw] using hz))
  have h := hr.nsmul m 0
  simpa only [rowSequence_horizontal_apply, zero_add, step_zero, add_zero,
    nsmul_eq_mul, Nat.cast_mul, mul_comm] using h

theorem sequence_eq_of_phase (ξ : ℤ → A) (Q : ℕ)
    (hp : IsPeriod ξ (Q : ℤ)) (i j : ℤ) (hij : (i : ZMod Q) = (j : ZMod Q)) : ξ i = ξ j := by
  obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub i j Q).mp hij
  have h := hp.zsmul m i
  have heq : i + m • (Q : ℤ) = j := by
    change i + m * (Q : ℤ) = j
    nlinarith [hm]
  simpa only [heq] using h.symm

theorem base_bounds {B : Finset G} {z : G} (hz : z ∈ base B) :
    lower B ≤ z.2 ∧ z.2 < upper B := by
  have hb := Finset.mem_sdiff.mp hz
  have hlo := lower_le_of_mem hb.1
  have hup := le_upper_of_mem hb.1
  have hne : z.2 ≠ upper B := fun he => hb.2 ((mem_row _ _ _).mpr ⟨hb.1, he⟩)
  exact ⟨hlo, by omega⟩

theorem edge_rules {θ : G → A} {B : Finset G} (hB : PlusBalanced θ B) :
    ∃ e : G, e.2 = upper B ∧ topEdge B = rowSegment e (topEdge B).card ∧
      Nonempty (Rules θ (base B) e (topEdge B).card) := by
  obtain ⟨l, hl⟩ := row_run hB.latticeConvex (upper B) (topEdge_nonempty hB.nonempty)
  let e : G := (l, upper B)
  have he : topEdge B = rowSegment e (topEdge B).card := by
    simpa only [e, rowSegment, step, topEdge, Prod.mk_add_mk, add_zero] using hl
  have hfull : base B ∪ rowSegment e (topEdge B).card = B := by
    rw [← he]
    exact Finset.sdiff_union_of_subset (row_subset B (upper B))
  refine ⟨e, rfl, he, exists_rules θ (base B) e _ ?_⟩
  simpa only [hfull] using hB.edge_budget

/-- The ambiguity witness differs from theta at every full-window directional
anchor; agreement at one determining block would force the entire row. -/
theorem full_patterns_differ {θ x : G → A} {B : Finset G}
    (hB : PlusBalanced θ B) (hx : x ∈ languageHull θ)
    (hagree : ∀ z : G, lower B ≤ z.2 → z.2 < upper B → x z = θ z)
    (hdiffer : ∃ z : G, z.2 = upper B ∧ x z ≠ θ z) :
    ∀ i : ℤ, patternAt x B (i • horizontal) ≠ patternAt θ B (i • horizontal) := by
  obtain ⟨e, heheight, hedge, hR⟩ := edge_rules hB
  let R := Classical.choice hR
  have hbase : ∀ i : ℤ, patternAt x (base B) (0 + step i) =
      patternAt θ (base B) (0 + step i) := by
    intro i
    funext p
    obtain ⟨hl, hu⟩ := base_bounds p.property
    exact hagree _ (by simpa [step] using hl) (by simpa [step] using hu)
  intro i hi
  have hsmall : base B ∪ rowSegment e R.forwardLength ⊆ B := by
    calc
      base B ∪ rowSegment e R.forwardLength ⊆ base B ∪ rowSegment e (topEdge B).card :=
        Finset.union_subset_union_right (rowSegment_mono e R.forward_lt.le)
      _ = B := by rw [← hedge]; exact Finset.sdiff_union_of_subset (row_subset B (upper B))
  have hs : patternAt x (base B ∪ rowSegment e R.forwardLength) (0 + step i) =
      patternAt θ (base B ∪ rowSegment e R.forwardLength) (0 + step i) := by
    funext p
    have h := congrFun hi ⟨p.val, hsmall p.property⟩
    simpa only [patternAt, zsmul_horizontal, zero_add] using h
  have hrow := rows_eq_of_pattern R hx (self_mem_languageHull θ) 0 0 hbase i hs
  obtain ⟨z, hz, hne⟩ := hdiffer
  have h := congrFun hrow (z.1 - e.1)
  have hez : z.2 = e.2 := hz.trans heheight.symm
  apply hne
  simp only [rowSequence_horizontal_apply, add_zero] at h
  rw [point_on_row e z hez] at h
  exact h

theorem directional_base_bound {θ x : G → A} {B : Finset G}
    (hB : PlusBalanced θ B) (hx : x ∈ languageHull θ)
    (hagree : ∀ z : G, lower B ≤ z.2 → z.2 < upper B → x z = θ z)
    (hdiffer : ∃ z : G, z.2 = upper B ∧ x z ≠ θ z) :
    directionalComplexity θ (base B) horizontal < (topEdge B).card := by
  apply directional_ambiguity_budget θ (Finset.sdiff_subset) horizontal _ hB.edge_budget hx
  · intro i
    funext p
    obtain ⟨hl, hu⟩ := base_bounds p.property
    exact hagree _ (by simpa [horizontal, patternAt] using hl)
      (by simpa [horizontal, patternAt] using hu)
  · exact full_patterns_differ hB hx hagree hdiffer

/-- Morse--Hedlund gives an actual common period on all rows below the edge. -/
theorem below_edge_period {θ : G → A} {B : Finset G} (hB : PlusBalanced θ B)
    (hbound : directionalComplexity θ (base B) horizontal < (topEdge B).card) :
    ∃ Q : ℕ, 0 < Q ∧ StripPeriod θ (lower B) (upper B - 1) Q := by
  let n := (topEdge B).card
  have hn : 2 ≤ n := by
    have hp := directionalComplexity_pos θ (base B) horizontal
    dsimp [n]
    omega
  let I := Finset.Icc (lower B) (upper B - 1)
  have hex (t : I) : ∃ l : ℤ, wordComplexity (rowSequence θ (l, t.val) horizontal) (n - 1) ≤ n - 1 := by
    have ht := Finset.mem_Icc.mp t.property
    have hc := hB.row_card t.val ht.1 (by omega)
    have hne : (row B t.val).Nonempty := Finset.card_pos.mp (by dsimp [n] at hn; omega)
    obtain ⟨l, hl⟩ := row_run hB.latticeConvex t.val hne
    have hsite : ∀ j : Fin (n - 1), (l, t.val) + (j.val : ℤ) • horizontal ∈ base B := by
      intro j
      apply Finset.mem_sdiff.mpr
      have hrow : (l + (j.val : ℤ), t.val) ∈ row B t.val := by
        rw [hl]
        exact Finset.mem_image.mpr ⟨j.val, Finset.mem_range.mpr (lt_of_lt_of_le j.isLt hc), rfl⟩
      refine ⟨?_, ?_⟩
      · simpa [horizontal] using row_subset B t.val hrow
      · intro h
        have hheight := ((mem_row _ _ _).mp h).2
        simp [horizontal] at hheight
        omega
    have hw := row_wordComplexity_le_directional θ (base B) (l, t.val) horizontal (n - 1) hsite
    exact ⟨l, by dsimp [n] at *; omega⟩
  choose l hl using hex
  obtain ⟨Q, hQ, hperiod⟩ := common_row_period_of_complexity
    (fun t : I => rowSequence θ (l t, t.val) horizontal) (fun _ => n - 1) hl
  refine ⟨Q, hQ, ?_⟩
  intro z hz
  let t : I := ⟨z.2, Finset.mem_Icc.mpr hz⟩
  exact (row_period_iff θ (l t, t.val) Q).mp (hperiod t) z rfl

/-- The old strip supplies the phase data for both actual row rules. -/
theorem extend_one_row {θ : G → A} {B : Finset G} (hB : PlusBalanced θ B)
    (R : ℤ) (hR : upper B ≤ R) (Q : ℕ) (hQ : 0 < Q)
    (hp : StripPeriod θ (lower B) (R - 1) Q) :
    ∃ q : ℕ, 0 < q ∧ Q ∣ q ∧ StripPeriod θ (lower B) R q := by
  obtain ⟨e, heheight, _, hRules⟩ := edge_rules hB
  let rules := Classical.choice hRules
  let w : G := (0, R - upper B)
  have hbase_height (p : base B) :
      lower B ≤ (w + p.val).2 ∧ (w + p.val).2 ≤ R - 1 := by
    obtain ⟨hl, hu⟩ := base_bounds p.property
    simp only [w, Prod.snd_add]
    omega
  have hphase : ∀ i j : ℤ, (i : ZMod Q) = (j : ZMod Q) →
      patternAt θ (base B) (w + step i) = patternAt θ (base B) (w + step j) := by
    intro i j hij
    funext p
    have hs : IsPeriod (rowSequence θ (w + p.val) horizontal) (Q : ℤ) :=
      (row_period_iff θ _ Q).mpr (fun z hz => hp z (by
        simpa [strip, hz] using hbase_height p))
    have h := sequence_eq_of_phase _ Q hs i j hij
    simpa [patternAt, rowSequence_horizontal_apply, add_assoc, add_comm, add_left_comm] using h
  obtain ⟨q, hq, hdiv, hnew⟩ := row_period_multiple rules w Q hQ hphase
  refine ⟨q, hq, hdiv, ?_⟩
  intro z hz
  by_cases hold : z.2 ≤ R - 1
  · exact hp.multiple hdiv z ⟨hz.1, hold⟩
  · have hzR : z.2 = R := by have := hz.2; omega
    apply (row_period_iff θ (e + w) q).mp hnew z
    simpa [w, heheight] using hzR

theorem extend_finitely {θ : G → A} {B : Finset G} (hB : PlusBalanced θ B)
    (Q : ℕ) (hQ : 0 < Q) (hp : StripPeriod θ (lower B) (upper B - 1) Q) :
    ∀ m : ℕ, ∃ q : ℕ, 0 < q ∧ StripPeriod θ (lower B) (upper B - 1 + m) q := by
  intro m
  induction m with
  | zero => exact ⟨Q, hQ, by simpa using hp⟩
  | succ m ih =>
    obtain ⟨q, hq, hper⟩ := ih
    obtain ⟨q', hq', _, hper'⟩ := extend_one_row hB (upper B + m) (by omega) q hq
      (by convert hper using 1 <;> omega)
    exact ⟨q', hq', by convert hper' using 1 <;> push_cast; omega⟩

section TwoComponents

variable [AddCommGroup A]

/-- D.7 with the balanced edge already placed on the ambiguous row. All
propagation and counting premises are derived from the balanced window. -/
theorem aligned_propagation (θ₁ θ₂ : G → A) (c₁ : ℕ) (h₂ : G)
    (hc₁ : 0 < c₁) (h₁per : IsPeriod θ₁ (c₁ • horizontal))
    (h₂per : IsPeriod θ₂ h₂) (htransverse : 0 < h₂.2)
    (B : Finset G) (hB : PlusBalanced (θ₁ + θ₂) B)
    {x : G → A} (hx : x ∈ languageHull (θ₁ + θ₂))
    (hagree : ∀ z : G, lower B ≤ z.2 → z.2 < upper B → x z = (θ₁ + θ₂) z)
    (hdiffer : ∃ z : G, z.2 = upper B ∧ x z ≠ (θ₁ + θ₂) z) :
    IsPeriodic (θ₁ + θ₂) := by
  have hbound := directional_base_bound hB hx hagree hdiffer
  obtain ⟨Q, hQ, hp⟩ := below_edge_period hB hbound
  let m := (lower B + h₂.2 - (upper B - 1)).toNat
  obtain ⟨q, hq, hstrip⟩ := extend_finitely hB Q hQ hp m
  have hupper : lower B + h₂.2 ≤ upper B - 1 + (m : ℤ) := by
    dsimp [m]
    omega
  apply periodic_of_strip_for_two_components θ₁ θ₂ height horizontal h₂
    (by simp [horizontal]) c₁ q hc₁ hq h₁per h₂per (by simp [height, horizontal])
    htransverse (lower B) (lower B + h₂.2) (by change h₂.2 ≤ lower B + h₂.2 - lower B; omega)
  intro z hz
  change lower B ≤ z.2 ∧ z.2 ≤ lower B + h₂.2 at hz
  simpa only [nsmul_horizontal] using hstrip z ⟨hz.1, hz.2.trans hupper⟩

/-- Lemma D.7, with the original arbitrary ambiguity strip. -/
theorem propagation (θ₁ θ₂ : G → A) (c₁ : ℕ) (h₂ : G)
    (hc₁ : 0 < c₁) (h₁per : IsPeriod θ₁ (c₁ • horizontal))
    (h₂per : IsPeriod θ₂ h₂) (htransverse : 0 < h₂.2)
    (B : Finset G) (hB : PlusBalanced (θ₁ + θ₂) B) (a b : ℤ)
    (hfit : upper B - lower B ≤ b - a) (hamb : PlusAmbiguity (θ₁ + θ₂) a b) :
    IsPeriodic (θ₁ + θ₂) := by
  let w : G := (0, b - upper B)
  let C := translateWindow w B
  have hC : PlusBalanced (θ₁ + θ₂) C := hB.translate w
  have htop : upper C = b := by
    dsimp [C]
    rw [upper_translateWindow w hB.nonempty]
    dsimp [w]
    omega
  have hbottom : a ≤ lower C := by
    dsimp [C]
    rw [lower_translateWindow w hB.nonempty]
    dsimp [w]
    omega
  obtain ⟨x, hx, hagree, hdiffer⟩ := hamb
  apply aligned_propagation θ₁ θ₂ c₁ h₂ hc₁ h₁per h₂per htransverse C hC hx
  · intro z hzlo hzhi
    exact hagree z (hbottom.trans hzlo) (by omega)
  · simpa only [htop] using hdiffer

theorem extend_agreement (θ₁ θ₂ : G → A) (c₁ : ℕ) (h₂ : G)
    (hc₁ : 0 < c₁) (h₁per : IsPeriod θ₁ (c₁ • horizontal))
    (h₂per : IsPeriod θ₂ h₂) (htransverse : 0 < h₂.2)
    (B : Finset G) (hB : PlusBalanced (θ₁ + θ₂) B)
    (haperiodic : ¬IsPeriodic (θ₁ + θ₂)) (a b : ℤ)
    (hfit : upper B - lower B ≤ b - a)
    {x : G → A} (hx : x ∈ languageHull (θ₁ + θ₂))
    (hagree : ∀ z : G, a ≤ z.2 → z.2 < b → x z = (θ₁ + θ₂) z) :
    ∀ z ∈ strip a b, x z = (θ₁ + θ₂) z := by
  intro z hz
  by_cases hlt : z.2 < b
  · exact hagree z hz.1 hlt
  · by_contra hne
    apply haperiodic
    apply propagation θ₁ θ₂ c₁ h₂ hc₁ h₁per h₂per htransverse B hB a b hfit
    exact ⟨x, hx, hagree, z, by have := hz.2; omega, hne⟩

/-- The contrapositive of D.7 propagates an actual wide-strip agreement to
the entire upper half-plane. -/
theorem halfplane_eq_of_strip (θ₁ θ₂ : G → A) (c₁ : ℕ) (h₂ : G)
    (hc₁ : 0 < c₁) (h₁per : IsPeriod θ₁ (c₁ • horizontal))
    (h₂per : IsPeriod θ₂ h₂) (htransverse : 0 < h₂.2)
    (B : Finset G) (hB : PlusBalanced (θ₁ + θ₂) B)
    (haperiodic : ¬IsPeriodic (θ₁ + θ₂)) (a b : ℤ)
    (hfit : upper B - lower B - 1 ≤ b - a)
    {x : G → A} (hx : x ∈ languageHull (θ₁ + θ₂))
    (hagree : ∀ z ∈ strip a b, x z = (θ₁ + θ₂) z) :
    ∀ z : G, a ≤ z.2 → x z = (θ₁ + θ₂) z := by
  have hsteps : ∀ m : ℕ, ∀ z ∈ strip a (b + m), x z = (θ₁ + θ₂) z := by
    intro m
    induction m with
    | zero => simpa using hagree
    | succ m ih =>
      apply extend_agreement θ₁ θ₂ c₁ h₂ hc₁ h₁per h₂per htransverse B hB
        haperiodic a (b + (m + 1 : ℕ)) (by push_cast; omega) hx
      intro z hzlo hzhi
      exact ih z ⟨hzlo, by push_cast at hzhi; omega⟩
  intro z hz
  exact hsteps (z.2 - b).toNat z ⟨hz, by omega⟩

end TwoComponents

end

end NivatTrial.BalancedPropagation
