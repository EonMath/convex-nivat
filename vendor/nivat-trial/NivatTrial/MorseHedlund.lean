import NivatTrial.Periodicity

/-! A complete Morse--Hedlund argument for bi-infinite words. -/

namespace NivatTrial.MorseHedlund

open Periodicity

variable {A B : Type*} [Fintype A]

/-- The length-`n` word beginning at an integer position. -/
def wordAt (ξ : ℤ → A) (n : ℕ) (z : ℤ) : Fin n → A :=
  fun i => ξ (z + (i.val : ℤ))

/-- Only words that actually occur are counted. -/
def wordSet (ξ : ℤ → A) (n : ℕ) : Set (Fin n → A) := Set.range (wordAt ξ n)

noncomputable instance wordSetFintype (ξ : ℤ → A) (n : ℕ) : Fintype (wordSet ξ n) :=
  Fintype.ofFinite _

noncomputable def wordComplexity (ξ : ℤ → A) (n : ℕ) : ℕ := Nat.card (wordSet ξ n)

theorem wordSet_nonempty (ξ : ℤ → A) (n : ℕ) : (wordSet ξ n).Nonempty :=
  ⟨wordAt ξ n 0, ⟨0, rfl⟩⟩

theorem wordComplexity_pos (ξ : ℤ → A) (n : ℕ) : 0 < wordComplexity ξ n := by
  classical
  haveI : Nonempty (wordSet ξ n) := (wordSet_nonempty ξ n).to_subtype
  simpa [wordComplexity, Nat.card_eq_fintype_card] using
    Fintype.card_pos (α := wordSet ξ n)

theorem wordComplexity_zero (ξ : ℤ → A) : wordComplexity ξ 0 = 1 := by
  classical
  letI : Unique (wordSet ξ 0) :=
    { default := ⟨wordAt ξ 0 0, ⟨0, rfl⟩⟩
      uniq := fun _ => Subsingleton.elim _ _ }
  rw [wordComplexity, Nat.card_eq_fintype_card]
  exact Fintype.card_unique

theorem wordComplexity_le_all (ξ : ℤ → A) (n : ℕ) :
    wordComplexity ξ n ≤ Fintype.card A ^ n := by
  classical
  have h := Fintype.card_le_of_injective
    (Subtype.val : wordSet ξ n → Fin n → A) Subtype.val_injective
  simpa [wordComplexity, Nat.card_eq_fintype_card] using h

/-- Delete the last letter. -/
def blockPrefix {n : ℕ} (w : Fin (n + 1) → A) : Fin n → A := fun i => w i.castSucc

/-- Delete the first letter. -/
def suffix {n : ℕ} (w : Fin (n + 1) → A) : Fin n → A := fun i => w i.succ

theorem prefix_wordAt (ξ : ℤ → A) (n : ℕ) (z : ℤ) :
    blockPrefix (wordAt ξ (n + 1) z) = wordAt ξ n z := rfl

theorem suffix_wordAt (ξ : ℤ → A) (n : ℕ) (z : ℤ) :
    suffix (wordAt ξ (n + 1) z) = wordAt ξ n (z + 1) := by
  funext i
  simp [suffix, wordAt, add_assoc, add_comm, add_left_comm]

def prefixMap (ξ : ℤ → A) (n : ℕ) : wordSet ξ (n + 1) → wordSet ξ n :=
  fun p => ⟨blockPrefix p.val, by
    rcases p.property with ⟨z, hz⟩
    exact ⟨z, by rw [← hz]; exact (prefix_wordAt ξ n z).symm⟩⟩

def suffixMap (ξ : ℤ → A) (n : ℕ) : wordSet ξ (n + 1) → wordSet ξ n :=
  fun p => ⟨suffix p.val, by
    rcases p.property with ⟨z, hz⟩
    exact ⟨z + 1, by rw [← hz]; exact (suffix_wordAt ξ n z).symm⟩⟩

theorem prefixMap_surjective (ξ : ℤ → A) (n : ℕ) :
    Function.Surjective (prefixMap ξ n) := by
  rintro ⟨p, z, rfl⟩
  exact ⟨⟨wordAt ξ (n + 1) z, ⟨z, rfl⟩⟩, rfl⟩

theorem suffixMap_surjective (ξ : ℤ → A) (n : ℕ) :
    Function.Surjective (suffixMap ξ n) := by
  rintro ⟨p, z, rfl⟩
  refine ⟨⟨wordAt ξ (n + 1) (z - 1), ⟨z - 1, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change suffix (wordAt ξ (n + 1) (z - 1)) = wordAt ξ n z
  rw [suffix_wordAt, sub_add_cancel]

theorem wordComplexity_step (ξ : ℤ → A) (n : ℕ) :
    wordComplexity ξ n ≤ wordComplexity ξ (n + 1) := by
  classical
  simpa [wordComplexity, Nat.card_eq_fintype_card] using
    Fintype.card_le_of_surjective _ (prefixMap_surjective ξ n)

theorem wordComplexity_monotone (ξ : ℤ → A) : Monotone (wordComplexity ξ) :=
  monotone_nat_of_le_succ (wordComplexity_step ξ)

theorem prefixMap_injective_of_plateau (ξ : ℤ → A) (n : ℕ)
    (hcard : wordComplexity ξ n = wordComplexity ξ (n + 1)) :
    Function.Injective (prefixMap ξ n) := by
  classical
  exact ((Fintype.bijective_iff_surjective_and_card _).mpr
    ⟨prefixMap_surjective ξ n,
      by simpa [wordComplexity, Nat.card_eq_fintype_card] using hcard.symm⟩).1

theorem suffixMap_injective_of_plateau (ξ : ℤ → A) (n : ℕ)
    (hcard : wordComplexity ξ n = wordComplexity ξ (n + 1)) :
    Function.Injective (suffixMap ξ n) := by
  classical
  exact ((Fintype.bijective_iff_surjective_and_card _).mpr
    ⟨suffixMap_surjective ξ n,
      by simpa [wordComplexity, Nat.card_eq_fintype_card] using hcard.symm⟩).1

/-- At a complexity plateau, a prefix determines its next letter. -/
theorem prefix_determines (ξ : ℤ → A) (n : ℕ)
    (hcard : wordComplexity ξ n = wordComplexity ξ (n + 1)) {i j : ℤ}
    (hij : wordAt ξ n i = wordAt ξ n j) :
    wordAt ξ (n + 1) i = wordAt ξ (n + 1) j := by
  have h := prefixMap_injective_of_plateau ξ n hcard
    (show prefixMap ξ n ⟨wordAt ξ (n + 1) i, ⟨i, rfl⟩⟩ =
      prefixMap ξ n ⟨wordAt ξ (n + 1) j, ⟨j, rfl⟩⟩ from Subtype.ext hij)
  exact congrArg Subtype.val h

/-- At the same plateau, a suffix determines its previous letter. -/
theorem suffix_determines (ξ : ℤ → A) (n : ℕ)
    (hcard : wordComplexity ξ n = wordComplexity ξ (n + 1)) {i j : ℤ}
    (hij : wordAt ξ n (i + 1) = wordAt ξ n (j + 1)) :
    wordAt ξ (n + 1) i = wordAt ξ (n + 1) j := by
  have hs : suffix (wordAt ξ (n + 1) i) = suffix (wordAt ξ (n + 1) j) := by
    simpa only [suffix_wordAt] using hij
  have h := suffixMap_injective_of_plateau ξ n hcard
    (show suffixMap ξ n ⟨wordAt ξ (n + 1) i, ⟨i, rfl⟩⟩ =
      suffixMap ξ n ⟨wordAt ξ (n + 1) j, ⟨j, rfl⟩⟩ from Subtype.ext hs)
  exact congrArg Subtype.val h

theorem plateau_forward_determinacy (ξ : ℤ → A) (n : ℕ)
    (hcard : wordComplexity ξ n = wordComplexity ξ (n + 1))
    {i j : ℤ} (hij : wordAt ξ n i = wordAt ξ n j) :
    wordAt ξ n (i + 1) = wordAt ξ n (j + 1) := by
  have h := congrArg (suffix (n := n)) (prefix_determines ξ n hcard hij)
  simpa only [suffix_wordAt] using h

theorem plateau_backward_determinacy (ξ : ℤ → A) (n : ℕ)
    (hcard : wordComplexity ξ n = wordComplexity ξ (n + 1))
    {i j : ℤ} (hij : wordAt ξ n i = wordAt ξ n j) :
    wordAt ξ n (i - 1) = wordAt ξ n (j - 1) := by
  have h' : wordAt ξ n ((i - 1) + 1) = wordAt ξ n ((j - 1) + 1) := by
    simpa only [sub_add_cancel] using hij
  exact congrArg (blockPrefix (n := n)) (suffix_determines ξ n hcard h')

/-- The actual block process is a finite bi-infinite state sequence. -/
def blockState (ξ : ℤ → A) (n : ℕ) (i : ℤ) : wordSet ξ n :=
  ⟨wordAt ξ n i, ⟨i, rfl⟩⟩

theorem blockState_periodic_of_plateau (ξ : ℤ → A) (n : ℕ)
    (hcard : wordComplexity ξ n = wordComplexity ξ (n + 1)) :
    ∃ q : ℕ, 0 < q ∧ ∀ i : ℤ, blockState ξ n (i + q) = blockState ξ n i := by
  apply finite_state_periodic (blockState ξ n)
  · intro i j hij
    exact Subtype.ext (plateau_forward_determinacy ξ n hcard (congrArg Subtype.val hij))
  · intro i j hij
    exact Subtype.ext (plateau_backward_determinacy ξ n hcard (congrArg Subtype.val hij))

theorem periodic_of_plateau (ξ : ℤ → A) (n : ℕ)
    (hcard : wordComplexity ξ n = wordComplexity ξ (n + 1)) :
    ∃ q : ℕ, 0 < q ∧ IsPeriod ξ (q : ℤ) := by
  obtain ⟨q, hq, hstate⟩ := blockState_periodic_of_plateau ξ n hcard
  refine ⟨q, hq, ?_⟩
  intro i
  have h := prefix_determines ξ n hcard (congrArg Subtype.val (hstate i))
  simpa only [wordAt, Fin.val_zero, Nat.cast_zero, add_zero] using congrFun h 0

/-- Strict growth at every step would force the complexity above the diagonal. -/
theorem plateau_of_diagonal_bound (p : ℕ → ℕ) (hzero : p 0 = 1)
    (hmono : Monotone p) {n : ℕ} (hbound : p n ≤ n) :
    ∃ k < n, p k = p (k + 1) := by
  by_contra hn
  have hstep : ∀ k < n, p k + 1 ≤ p (k + 1) := by
    intro k hk
    have hne : p k ≠ p (k + 1) := fun h => hn ⟨k, hk, h⟩
    have hle := hmono (Nat.le_succ k)
    change p k ≤ p (k + 1) at hle
    omega
  have hgrowth : ∀ k ≤ n, k + 1 ≤ p k := by
    intro k
    induction k with
    | zero => intro _; omega
    | succ k ih =>
      intro hk
      have hprev := ih (Nat.le_of_succ_le hk)
      have hs := hstep k (Nat.lt_of_succ_le hk)
      omega
  have h := hgrowth n le_rfl
  omega

/-- Morse--Hedlund for a bi-infinite sequence over a finite alphabet. -/
theorem morse_hedlund (ξ : ℤ → A) {n : ℕ} (hbound : wordComplexity ξ n ≤ n) :
    ∃ q : ℕ, 0 < q ∧ IsPeriod ξ (q : ℤ) := by
  obtain ⟨k, hk, hplateau⟩ := plateau_of_diagonal_bound (wordComplexity ξ)
    (wordComplexity_zero ξ) (wordComplexity_monotone ξ) hbound
  exact periodic_of_plateau ξ k hplateau

/-- The contrapositive form used to prove lower complexity bounds. -/
theorem aperiodic_complexity_lower_bound (ξ : ℤ → A)
    (haper : ¬∃ q : ℕ, 0 < q ∧ IsPeriod ξ (q : ℤ)) (n : ℕ) :
    n + 1 ≤ wordComplexity ξ n := by
  by_contra hn
  exact haper (morse_hedlund ξ (n := n) (by omega))

section Converse

theorem wordAt_eq_of_period_difference (ξ : ℤ → A) (n : ℕ) {i j : ℤ}
    (hp : IsPeriod ξ (i - j)) : wordAt ξ n i = wordAt ξ n j := by
  funext k
  change ξ (i + k.val) = ξ (j + k.val)
  apply IsPeriod.eq_of_sub
  convert hp using 1
  omega

/-- A period bounds every block complexity by the number of residue classes. -/
theorem wordComplexity_le_period (ξ : ℤ → A) {q : ℕ} (hq : 0 < q)
    (hp : IsPeriod ξ (q : ℤ)) (n : ℕ) : wordComplexity ξ n ≤ q := by
  classical
  let R : Finset ℤ := Finset.Ico 0 q
  let f : R → wordSet ξ n := fun r => ⟨wordAt ξ n r.val, ⟨r.val, rfl⟩⟩
  have hnz : 0 < (q : ℤ) := by exact_mod_cast hq
  have hf : Function.Surjective f := by
    rintro ⟨p, z, rfl⟩
    have hr : z % (q : ℤ) ∈ R := Finset.mem_Ico.mpr
      ⟨Int.emod_nonneg _ (ne_of_gt hnz), Int.emod_lt_of_pos _ hnz⟩
    refine ⟨⟨z % q, hr⟩, ?_⟩
    apply Subtype.ext
    apply wordAt_eq_of_period_difference
    have hzp := hp.zsmul (z / q)
    have heq : z - z % q = (z / q) * q := by
      nlinarith [Int.emod_add_mul_ediv z (q : ℤ)]
    have hp' : IsPeriod ξ (z - z % q) := by simpa [heq, smul_eq_mul] using hzp
    simpa only [neg_sub] using hp'.neg
  have hcard := Fintype.card_le_of_surjective f hf
  simpa [wordComplexity, Nat.card_eq_fintype_card, R] using hcard

/-- The usual equivalence, including the easy periodic-to-low-complexity direction. -/
theorem periodic_iff_low_word_complexity (ξ : ℤ → A) :
    (∃ q : ℕ, 0 < q ∧ IsPeriod ξ (q : ℤ)) ↔
      ∃ n : ℕ, 0 < n ∧ wordComplexity ξ n ≤ n := by
  constructor
  · rintro ⟨q, hq, hp⟩
    exact ⟨q, hq, wordComplexity_le_period ξ hq hp q⟩
  · rintro ⟨n, hn, hcomplex⟩
    exact morse_hedlund ξ hcomplex

end Converse

section LatticeRows

/-- Reading one lattice line as a bi-infinite word. -/
def rowSequence (θ : Lattice → A) (w u : Lattice) : ℤ → A :=
  fun z => θ (w + z • u)

/-- The finite run used to read a block of a lattice row. -/
def rowWindow (u : Lattice) (n : ℕ) : Finset Lattice :=
  (Finset.range n).image (fun i => i • u)

theorem mem_rowWindow (u : Lattice) {n i : ℕ} (hi : i < n) : i • u ∈ rowWindow u n :=
  Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi)

noncomputable def rowWordToPattern (θ : Lattice → A) (w u : Lattice) (n : ℕ) :
    wordSet (rowSequence θ w u) n → patternSet θ (rowWindow u n) := fun p =>
  ⟨patternAt θ (rowWindow u n) (w + p.property.choose • u),
    ⟨w + p.property.choose • u, rfl⟩⟩

theorem rowWordToPattern_injective (θ : Lattice → A) (w u : Lattice) (n : ℕ) :
    Function.Injective (rowWordToPattern θ w u n) := by
  intro p q h
  apply Subtype.ext
  rw [← p.property.choose_spec, ← q.property.choose_spec]
  funext i
  have hpq := congrFun (congrArg
    (fun p : patternSet θ (rowWindow u n) => p.val) h)
    ⟨i.val • u, mem_rowWindow u i.isLt⟩
  change θ ((w + p.property.choose • u) + i.val • u) =
    θ ((w + q.property.choose • u) + i.val • u) at hpq
  simpa only [wordAt, rowSequence, add_zsmul, natCast_zsmul, add_assoc] using hpq

/-- Only a subfamily of lattice translates is used when reading one row. -/
theorem row_wordComplexity_le (θ : Lattice → A) (w u : Lattice) (n : ℕ) :
    wordComplexity (rowSequence θ w u) n ≤ patternComplexity θ (rowWindow u n) := by
  classical
  simpa [wordComplexity, patternComplexity, Nat.card_eq_fintype_card] using
    Fintype.card_le_of_injective _ (rowWordToPattern_injective θ w u n)

theorem periodic_row_of_pattern_bound (θ : Lattice → A) (w u : Lattice) {n : ℕ}
    (hcomplexity : patternComplexity θ (rowWindow u n) ≤ n) :
    ∃ q : ℕ, 0 < q ∧ IsPeriod (rowSequence θ w u) (q : ℤ) :=
  morse_hedlund _ ((row_wordComplexity_le θ w u n).trans hcomplexity)

theorem row_period_iff (θ : Lattice → A) (w u : Lattice) (q : ℤ) :
    IsPeriod (rowSequence θ w u) q ↔
      ∀ z : ℤ, θ (w + z • u + q • u) = θ (w + z • u) := by
  simp only [IsPeriod, rowSequence, add_zsmul, add_assoc]

/-- A lattice period in the row direction induces a word period. -/
theorem row_period_of_lattice_period (θ : Lattice → A) (w u : Lattice) (q : ℤ)
    (hp : IsPeriod θ (q • u)) : IsPeriod (rowSequence θ w u) q := by
  rw [row_period_iff]
  intro z
  exact hp (w + z • u)

end LatticeRows

section PhasedFiniteStates

variable [Fintype B]

/-- Store a phase and a finite row block; both are part of the actual state. -/
def phaseBlockState (phase : ℤ → B) (ξ : ℤ → A) (K : ℕ) (i : ℤ) : B × (Fin K → A) :=
  (phase i, wordAt ξ K i)

/-- A block can store all shorter prefixes used by the local rules. -/
theorem wordAt_prefix_of_eq (ξ : ℤ → A) {K k : ℕ} (hk : k ≤ K) {i j : ℤ}
    (h : wordAt ξ K i = wordAt ξ K j) : wordAt ξ k i = wordAt ξ k j := by
  funext l
  exact congrFun h ⟨l.val, lt_of_lt_of_le l.isLt hk⟩

theorem wordAt_next_of_eq (ξ : ℤ → A) {K : ℕ} {i j : ℤ}
    (hblock : wordAt ξ K i = wordAt ξ K j) (hletter : ξ (i + K) = ξ (j + K)) :
    wordAt ξ K (i + 1) = wordAt ξ K (j + 1) := by
  funext l
  by_cases hl : l.val + 1 < K
  · have h := congrFun hblock ⟨l.val + 1, hl⟩
    simpa [wordAt, add_assoc, add_comm, add_left_comm] using h
  · have heq : l.val + 1 = K := by omega
    simpa [wordAt, ← heq, add_assoc, add_comm, add_left_comm] using hletter

theorem wordAt_prev_of_eq (ξ : ℤ → A) {K : ℕ} {i j : ℤ}
    (hblock : wordAt ξ K i = wordAt ξ K j) (hletter : ξ (i - 1) = ξ (j - 1)) :
    wordAt ξ K (i - 1) = wordAt ξ K (j - 1) := by
  funext l
  by_cases hl : l.val = 0
  · simpa [wordAt, hl] using hletter
  · have h := congrFun hblock ⟨l.val - 1, by omega⟩
    have hlpos : 1 ≤ l.val := by omega
    have hcast : ((l.val - 1 : ℕ) : ℤ) = (l.val : ℤ) - 1 := Int.ofNat_sub hlpos
    simpa [wordAt, hcast, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h

/-- The forward rule of Appendix D may use a shorter block than the stored state. -/
theorem phaseBlockState_forward (phase : ℤ → B) (ξ : ℤ → A) {K k : ℕ}
    (hk : k ≤ K) (hphase : ∀ i j, phase i = phase j → phase (i + 1) = phase (j + 1))
    (hnext : ∀ i j, phase i = phase j → wordAt ξ k i = wordAt ξ k j →
      ξ (i + k) = ξ (j + k)) {i j : ℤ}
    (hstate : phaseBlockState phase ξ K i = phaseBlockState phase ξ K j) :
    phaseBlockState phase ξ K (i + 1) = phaseBlockState phase ξ K (j + 1) := by
  have hp : phase i = phase j := congrArg Prod.fst hstate
  have hw : wordAt ξ K i = wordAt ξ K j := congrArg Prod.snd hstate
  apply Prod.ext (hphase i j hp)
  apply wordAt_next_of_eq ξ hw
  have hphases : ∀ d : ℕ, phase (i + d) = phase (j + d) := by
    intro d
    induction d with
    | zero => simpa using hp
    | succ d ih =>
      simpa [Nat.cast_add, add_assoc] using hphase (i + d) (j + d) ih
  have hwords : wordAt ξ k (i + (K - k : ℕ)) = wordAt ξ k (j + (K - k : ℕ)) := by
    funext l
    have h := congrFun hw ⟨K - k + l.val, by omega⟩
    simpa [wordAt, Nat.cast_add, add_assoc] using h
  have h := hnext (i + (K - k : ℕ)) (j + (K - k : ℕ)) (hphases _) hwords
  have heq : K - k + k = K := Nat.sub_add_cancel hk
  simpa only [add_assoc, ← Nat.cast_add, heq] using h

theorem phaseBlockState_backward (phase : ℤ → B) (ξ : ℤ → A) {K k : ℕ}
    (hk : k ≤ K) (hphase : ∀ i j, phase i = phase j → phase (i - 1) = phase (j - 1))
    (hprev : ∀ i j, phase i = phase j → wordAt ξ k i = wordAt ξ k j →
      ξ (i - 1) = ξ (j - 1)) {i j : ℤ}
    (hstate : phaseBlockState phase ξ K i = phaseBlockState phase ξ K j) :
    phaseBlockState phase ξ K (i - 1) = phaseBlockState phase ξ K (j - 1) := by
  have hp : phase i = phase j := congrArg Prod.fst hstate
  have hw : wordAt ξ K i = wordAt ξ K j := congrArg Prod.snd hstate
  exact Prod.ext (hphase i j hp)
    (wordAt_prev_of_eq ξ hw (hprev i j hp (wordAt_prefix_of_eq ξ hk hw)))

/-- This is the finite-state step used to extend a periodic strip by one row. -/
theorem phased_finite_state_periodic (phase : ℤ → B) (ξ : ℤ → A)
    (K k k' : ℕ) (hK : 0 < K) (hk : k ≤ K) (hk' : k' ≤ K)
    (hphaseForward : ∀ i j, phase i = phase j → phase (i + 1) = phase (j + 1))
    (hphaseBackward : ∀ i j, phase i = phase j → phase (i - 1) = phase (j - 1))
    (hnext : ∀ i j, phase i = phase j → wordAt ξ k i = wordAt ξ k j →
      ξ (i + k) = ξ (j + k))
    (hprev : ∀ i j, phase i = phase j → wordAt ξ k' i = wordAt ξ k' j →
      ξ (i - 1) = ξ (j - 1)) :
    ∃ q : ℕ, 0 < q ∧ (∀ i : ℤ, phase (i + q) = phase i) ∧
      IsPeriod ξ (q : ℤ) := by
  obtain ⟨q, hq, hstate⟩ := finite_state_periodic (phaseBlockState phase ξ K)
    (fun i j h => phaseBlockState_forward phase ξ hk hphaseForward hnext h)
    (fun i j h => phaseBlockState_backward phase ξ hk' hphaseBackward hprev h)
  refine ⟨q, hq, fun i => congrArg Prod.fst (hstate i), ?_⟩
  intro i
  have h := congrFun (congrArg Prod.snd (hstate i)) ⟨0, hK⟩
  simpa [phaseBlockState, wordAt] using h

end PhasedFiniteStates

section PeriodicPhase

/-- The period obtained while extending a row is a multiple of the old phase period. -/
theorem phased_row_period_multiple (ξ : ℤ → A) (Q k k' : ℕ) (hQ : 0 < Q)
    (hnext : ∀ i j : ℤ, (i : ZMod Q) = (j : ZMod Q) →
      wordAt ξ k i = wordAt ξ k j → ξ (i + k) = ξ (j + k))
    (hprev : ∀ i j : ℤ, (i : ZMod Q) = (j : ZMod Q) →
      wordAt ξ k' i = wordAt ξ k' j → ξ (i - 1) = ξ (j - 1)) :
    ∃ q : ℕ, 0 < q ∧ Q ∣ q ∧ IsPeriod ξ (q : ℤ) := by
  letI : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  let phase : ℤ → ZMod Q := fun i => i
  let K := max (max k k') 1
  have hK : 0 < K := by omega
  have hk : k ≤ K := by omega
  have hk' : k' ≤ K := by omega
  have hf : ∀ i j, phase i = phase j → phase (i + 1) = phase (j + 1) := by
    intro i j hij
    simpa [phase] using congrArg (fun x : ZMod Q => x + 1) hij
  have hb : ∀ i j, phase i = phase j → phase (i - 1) = phase (j - 1) := by
    intro i j hij
    simpa [phase] using congrArg (fun x : ZMod Q => x - 1) hij
  obtain ⟨q, hq, hphase, hperiod⟩ := phased_finite_state_periodic phase ξ K k k'
    hK hk hk' hf hb hnext hprev
  have hz : (q : ZMod Q) = 0 := by simpa [phase] using hphase 0
  exact ⟨q, hq, (ZMod.natCast_eq_zero_iff q Q).mp hz, hperiod⟩

end PeriodicPhase

section CommonRowPeriods

variable {ι : Type*} [Fintype ι]

/-- Finitely many periodic rows possess a common positive period. -/
theorem common_row_period (ξ : ι → ℤ → A)
    (hrows : ∀ t, ∃ q : ℕ, 0 < q ∧ IsPeriod (ξ t) (q : ℤ)) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ t, IsPeriod (ξ t) (Q : ℤ) := by
  classical
  choose q hq hperiod using hrows
  let Q := ∏ t, q t
  have hQ : 0 < Q := Finset.prod_pos (fun t _ => hq t)
  refine ⟨Q, hQ, ?_⟩
  intro t
  have hdiv : q t ∣ Q := Finset.dvd_prod_of_mem q (Finset.mem_univ t)
  obtain ⟨k, hk⟩ := hdiv
  have hper := (hperiod t).nsmul k
  rw [hk]
  simpa [nsmul_eq_mul, Nat.cast_mul, mul_comm] using hper

/-- Apply the common-period construction directly to rows with the Morse--Hedlund bound. -/
theorem common_row_period_of_complexity (ξ : ι → ℤ → A) (n : ι → ℕ)
    (hcomplex : ∀ t, wordComplexity (ξ t) (n t) ≤ n t) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ t, IsPeriod (ξ t) (Q : ℤ) :=
  common_row_period ξ (fun t => morse_hedlund (ξ t) (hcomplex t))

end CommonRowPeriods

end NivatTrial.MorseHedlund
