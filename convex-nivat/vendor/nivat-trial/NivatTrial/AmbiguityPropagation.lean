import NivatTrial.MorseHedlund
import NivatTrial.LatticePolygon

/-! Actual pattern extensions and horizontal row propagation for Appendix D. -/

namespace NivatTrial.AmbiguityPropagation

open NivatTrial.Dynamics NivatTrial.Periodicity NivatTrial.MorseHedlund
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ

variable {A : Type*} [Fintype A]

/-- A bijective restriction of actual patterns also determines extensions in
every member of the actual language hull. -/
theorem unique_extension_in_languageHull (θ : G → A) {S T : Finset G}
    (hST : S ⊆ T) (hcard : patternComplexity θ S = patternComplexity θ T)
    {x y : G → A} (hx : x ∈ languageHull θ) (hy : y ∈ languageHull θ)
    (u v : G) (hs : patternAt x S u = patternAt y S v) :
    patternAt x T u = patternAt y T v := by
  let px : patternSet θ T := ⟨patternAt x T u,
    patternSet_subset_of_mem_languageHull hx T ⟨u, rfl⟩⟩
  let py : patternSet θ T := ⟨patternAt y T v,
    patternSet_subset_of_mem_languageHull hy T ⟨v, rfl⟩⟩
  have heq : patternRestriction θ hST px = patternRestriction θ hST py :=
    Subtype.ext hs
  exact congrArg Subtype.val (patternRestriction_injective_of_card_eq θ hST hcard heq)

/-- Determination concerns actual configurations and actual finite patterns. -/
def Determines (θ : G → A) (S : Finset G) (p : G) : Prop :=
  ∀ x ∈ languageHull θ, ∀ y ∈ languageHull θ, ∀ u v : G,
    patternAt x S u = patternAt y S v → x (u + p) = y (v + p)

theorem determines_of_plateau (θ : G → A) (S : Finset G) (p : G)
    (hcard : patternComplexity θ S = patternComplexity θ (insert p S)) :
    Determines θ S p := by
  intro x hx y hy u v hs
  have h := unique_extension_in_languageHull θ (Finset.subset_insert p S) hcard hx hy u v hs
  exact congrFun h ⟨p, Finset.mem_insert_self p S⟩

/-- Only anchors on the given one-dimensional subgroup are used. -/
def directionalPatternAt (θ : G → A) (S : Finset G) (u : G) (i : ℤ) : patternSet θ S :=
  ⟨patternAt θ S (i • u), ⟨i • u, rfl⟩⟩

def directionalPatternSet (θ : G → A) (S : Finset G) (u : G) : Set (patternSet θ S) :=
  Set.range (directionalPatternAt θ S u)

instance directionalPatternSetFintype (θ : G → A) (S : Finset G) (u : G) :
    Fintype (directionalPatternSet θ S u) := Fintype.ofFinite _

def directionalComplexity (θ : G → A) (S : Finset G) (u : G) : ℕ :=
  Nat.card (directionalPatternSet θ S u)

theorem directionalComplexity_pos (θ : G → A) (S : Finset G) (u : G) :
    0 < directionalComplexity θ S u := by
  let p : directionalPatternSet θ S u := ⟨directionalPatternAt θ S u 0, ⟨0, rfl⟩⟩
  haveI : Nonempty (directionalPatternSet θ S u) := ⟨p⟩
  simpa [directionalComplexity, Nat.card_eq_fintype_card] using
    Fintype.card_pos (α := directionalPatternSet θ S u)

theorem directionalComplexity_le (θ : G → A) (S : Finset G) (u : G) :
    directionalComplexity θ S u ≤ patternComplexity θ S := by
  simpa [directionalComplexity, patternComplexity, Nat.card_eq_fintype_card] using
    Fintype.card_le_of_injective
      (Subtype.val : directionalPatternSet θ S u → patternSet θ S) Subtype.val_injective

def directionalWordMap (θ : G → A) (S : Finset G) (w u : G) (n : ℕ)
    (hsite : ∀ j : Fin n, w + (j.val : ℤ) • u ∈ S) :
    directionalPatternSet θ S u → wordSet (rowSequence θ w u) n := fun p => by
  refine ⟨fun j => p.val.val ⟨w + (j.val : ℤ) • u, hsite j⟩, ?_⟩
  obtain ⟨i, hi⟩ := p.property
  refine ⟨i, ?_⟩
  funext j
  have h := congrArg (fun q : patternSet θ S =>
    q.val ⟨w + (j.val : ℤ) • u, hsite j⟩) hi
  simpa [directionalPatternAt, patternAt, rowSequence, wordAt,
    add_smul, add_assoc, add_comm, add_left_comm] using h

theorem directionalWordMap_surjective (θ : G → A) (S : Finset G) (w u : G) (n : ℕ)
    (hsite : ∀ j : Fin n, w + (j.val : ℤ) • u ∈ S) :
    Function.Surjective (directionalWordMap θ S w u n hsite) := by
  rintro ⟨q, i, rfl⟩
  refine ⟨⟨directionalPatternAt θ S u i, ⟨i, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  funext j
  simp [directionalWordMap, directionalPatternAt, patternAt, wordAt,
    rowSequence, add_smul, add_assoc, add_comm, add_left_comm]

/-- Restriction to a row counts only the directional anchor family, rather
than all two-dimensional translates of the row window. -/
theorem row_wordComplexity_le_directional (θ : G → A) (S : Finset G) (w u : G) (n : ℕ)
    (hsite : ∀ j : Fin n, w + (j.val : ℤ) • u ∈ S) :
    wordComplexity (rowSequence θ w u) n ≤ directionalComplexity θ S u := by
  simpa [wordComplexity, directionalComplexity, Nat.card_eq_fintype_card] using
    Fintype.card_le_of_surjective (directionalWordMap θ S w u n hsite)
      (directionalWordMap_surjective θ S w u n hsite)

/-- Two different extensions at every directional anchor consume the actual
restriction-map surplus. -/
theorem directional_ambiguity_budget (θ : G → A) {S T : Finset G} (hST : S ⊆ T)
    (u : G) (n : ℕ) (hbudget : patternComplexity θ T < patternComplexity θ S + n)
    {x : G → A} (hx : x ∈ languageHull θ)
    (hbase : ∀ i : ℤ, patternAt x S (i • u) = patternAt θ S (i • u))
    (hdiffer : ∀ i : ℤ, patternAt x T (i • u) ≠ patternAt θ T (i • u)) :
    directionalComplexity θ S u < n := by
  let Γ : Finset (patternSet θ S) := (directionalPatternSet θ S u).toFinite.toFinset
  have hΓ : ∀ p ∈ Γ, ∃ q q' : patternSet θ T,
      patternRestriction θ hST q = p ∧ patternRestriction θ hST q' = p ∧ q ≠ q' := by
    intro p hp
    obtain ⟨i, hi⟩ := (Set.Finite.mem_toFinset _).mp hp
    let q : patternSet θ T := ⟨patternAt x T (i • u),
      patternSet_subset_of_mem_languageHull hx T ⟨i • u, rfl⟩⟩
    let q' : patternSet θ T := ⟨patternAt θ T (i • u), ⟨i • u, rfl⟩⟩
    refine ⟨q, q', ?_, ?_, ?_⟩
    · apply Subtype.ext
      change patternAt x S (i • u) = p.val
      exact (hbase i).trans (congrArg Subtype.val hi)
    · exact hi
    · intro h
      exact hdiffer i (congrArg Subtype.val h)
  have h := ambiguity_budget θ hST n Γ hbudget hΓ
  have hcard : Γ.card = directionalComplexity θ S u := by
    simp [Γ, directionalComplexity, Nat.card_eq_fintype_card]
  exact hcard ▸ h

theorem next_cross_word (ξ η : ℤ → A) (n : ℕ) (i : ℤ)
    (hblock : wordAt ξ n i = wordAt η n i) (hletter : ξ (i + n) = η (i + n)) :
    wordAt ξ n (i + 1) = wordAt η n (i + 1) := by
  funext j
  by_cases hj : j.val + 1 < n
  · have h := congrFun hblock ⟨j.val + 1, hj⟩
    simpa [wordAt, add_assoc, add_comm, add_left_comm] using h
  · have heq : j.val + 1 = n := by omega
    simpa [wordAt, ← heq, add_assoc, add_comm, add_left_comm] using hletter

theorem prev_cross_word (ξ η : ℤ → A) (n : ℕ) (i : ℤ)
    (hblock : wordAt ξ n i = wordAt η n i) (hletter : ξ (i - 1) = η (i - 1)) :
    wordAt ξ n (i - 1) = wordAt η n (i - 1) := by
  funext j
  by_cases hj : j.val = 0
  · simpa [wordAt, hj] using hletter
  · have h := congrFun hblock ⟨j.val - 1, by omega⟩
    have hcast : ((j.val - 1 : ℕ) : ℤ) = (j.val : ℤ) - 1 := Int.ofNat_sub (by omega)
    simpa [wordAt, hcast, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h

/-- A common block, together with forward and backward determination, forces
two bi-infinite rows to coincide. The zero-length rules are included. -/
theorem row_eq_of_two_sided_rules (ξ η : ℤ → A) (k k' : ℕ)
    (hnext : ∀ i, wordAt ξ k i = wordAt η k i → ξ (i + k) = η (i + k))
    (hprev : ∀ i, wordAt ξ k' i = wordAt η k' i → ξ (i - 1) = η (i - 1))
    (hblock : ∃ i, wordAt ξ k i = wordAt η k i) : ξ = η := by
  by_cases hk : k = 0
  · subst k
    funext i
    simpa using hnext i (by ext j; exact Fin.elim0 j)
  obtain ⟨i₀, hi₀⟩ := hblock
  have hforward : ∀ m : ℕ, wordAt ξ k (i₀ + m) = wordAt η k (i₀ + m) := by
    intro m
    induction m with
    | zero => simpa using hi₀
    | succ m ih =>
      simpa [Nat.cast_add, add_assoc] using next_cross_word ξ η k _ ih (hnext _ ih)
  have hright : ∀ s : ℤ, i₀ ≤ s → ξ s = η s := by
    intro s hs
    let m := (s - i₀).toNat
    have hm : (m : ℤ) = s - i₀ := Int.toNat_of_nonneg (sub_nonneg.mpr hs)
    have h := congrFun (hforward m) ⟨0, Nat.pos_of_ne_zero hk⟩
    simpa [wordAt, hm] using h
  by_cases hk' : k' = 0
  · subst k'
    funext s
    simpa using hprev (s + 1) (by ext j; exact Fin.elim0 j)
  have hstart : wordAt ξ k' i₀ = wordAt η k' i₀ := by
    funext j
    exact hright _ (by omega)
  have hbackward : ∀ m : ℕ, wordAt ξ k' (i₀ - m) = wordAt η k' (i₀ - m) := by
    intro m
    induction m with
    | zero => simpa using hstart
    | succ m ih =>
      simpa [Nat.cast_add, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        prev_cross_word ξ η k' _ ih (hprev _ ih)
  funext s
  by_cases hs : i₀ ≤ s
  · exact hright s hs
  · let m := (i₀ - s).toNat
    have hm : (m : ℤ) = i₀ - s := Int.toNat_of_nonneg (by omega)
    have h := congrFun (hbackward m) ⟨0, Nat.pos_of_ne_zero hk'⟩
    simpa [wordAt, hm] using h

end

end NivatTrial.AmbiguityPropagation
