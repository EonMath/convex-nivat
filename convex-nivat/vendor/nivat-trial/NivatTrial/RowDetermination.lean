import NivatTrial.AmbiguityPropagation

/-! The two actual determination rules on a finite horizontal edge, and their
consequences for equality and for periodic extension of a row. -/

namespace NivatTrial.RowDetermination

open NivatTrial.Dynamics NivatTrial.Periodicity NivatTrial.MorseHedlund
open NivatTrial.AmbiguityPropagation
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ

def horizontal : G := (1, 0)

def step (i : ℤ) : G := (i, 0)

@[simp] theorem step_zero : step 0 = 0 := rfl
@[simp] theorem step_add (i j : ℤ) : step (i + j) = step i + step j := rfl
@[simp] theorem step_sub (i j : ℤ) : step (i - j) = step i - step j := rfl
@[simp] theorem zsmul_horizontal (i : ℤ) : i • horizontal = step i := by
  ext <;> simp [horizontal, step]
@[simp] theorem nsmul_horizontal (i : ℕ) : i • horizontal = step i := by
  ext <;> simp [horizontal, step]

@[simp] theorem rowSequence_horizontal_apply {A : Type*} (θ : G → A) (e : G) (i : ℤ) :
    rowSequence θ e horizontal i = θ (e + step i) := by
  simp only [rowSequence, zsmul_horizontal]

def rowSegment (e : G) (n : ℕ) : Finset G :=
  (Finset.range n).image (fun j : ℕ => e + step (j : ℤ))

theorem mem_rowSegment (e : G) (n : ℕ) (z : G) :
    z ∈ rowSegment e n ↔ ∃ j : ℕ, j < n ∧ z = e + step (j : ℤ) := by
  simp [rowSegment, eq_comm]

theorem mem_rowSegment_iff (e : G) (n : ℕ) (z : G) :
    z ∈ rowSegment e n ↔ z.2 = e.2 ∧ e.1 ≤ z.1 ∧ z.1 < e.1 + n := by
  rw [mem_rowSegment]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj' : (j : ℤ) < n := by exact_mod_cast hj
    simp only [step, Prod.fst_add, Prod.snd_add, add_zero]
    exact ⟨trivial, le_add_of_nonneg_right (Int.natCast_nonneg j), by omega⟩
  · rintro ⟨hy, hl, hu⟩
    let j := (z.1 - e.1).toNat
    have hj : (j : ℤ) = z.1 - e.1 := Int.toNat_of_nonneg (by omega)
    refine ⟨j, by omega, ?_⟩
    ext <;> simp [step, hj, hy]

@[simp] theorem rowSegment_zero (e : G) : rowSegment e 0 = ∅ := by simp [rowSegment]

theorem rowSegment_succ (e : G) (n : ℕ) :
    rowSegment e (n + 1) = insert (e + step (n : ℤ)) (rowSegment e n) := by
  simp [rowSegment, Finset.range_add_one]

theorem rowSegment_mono (e : G) {m n : ℕ} (h : m ≤ n) :
    rowSegment e m ⊆ rowSegment e n := by
  intro z hz
  obtain ⟨j, hj, he⟩ := (mem_rowSegment e m z).mp hz
  exact (mem_rowSegment e n z).mpr ⟨j, hj.trans_le h, he⟩

def rowSuffix (e : G) (n k : ℕ) : Finset G :=
  rowSegment (e + step ((n - k : ℕ) : ℤ)) k

theorem mem_rowSuffix_iff (e : G) {n k : ℕ} (hk : k ≤ n) (z : G) :
    z ∈ rowSuffix e n k ↔
      z.2 = e.2 ∧ e.1 + (n : ℤ) - k ≤ z.1 ∧ z.1 < e.1 + n := by
  rw [rowSuffix, mem_rowSegment_iff]
  simp only [step, Prod.fst_add, Prod.snd_add, add_zero, Int.ofNat_sub hk]
  constructor <;> intro h <;> rcases h with ⟨h₁, h₂, h₃⟩ <;> constructor
  · exact h₁
  · constructor <;> linarith
  · exact h₁
  · constructor <;> linarith

@[simp] theorem rowSuffix_zero (e : G) (n : ℕ) : rowSuffix e n 0 = ∅ := by
  simp [rowSuffix]

@[simp] theorem rowSuffix_self (e : G) (n : ℕ) : rowSuffix e n n = rowSegment e n := by
  simp [rowSuffix]

theorem rowSuffix_mono (e : G) {n k l : ℕ} (hkl : k ≤ l) (hln : l ≤ n) :
    rowSuffix e n k ⊆ rowSuffix e n l := by
  intro z hz
  rw [mem_rowSuffix_iff e (hkl.trans hln)] at hz
  rw [mem_rowSuffix_iff e hln]
  exact ⟨hz.1, by omega, hz.2.2⟩

theorem rowSuffix_succ (e : G) {n k : ℕ} (hk : k < n) :
    rowSuffix e n (k + 1) =
      insert (e + step ((n - k - 1 : ℕ) : ℤ)) (rowSuffix e n k) := by
  ext z
  rw [mem_rowSuffix_iff e (by omega), Finset.mem_insert, mem_rowSuffix_iff e (by omega)]
  have hcast : ((n - k - 1 : ℕ) : ℤ) = (n : ℤ) - k - 1 := by omega
  constructor
  · rintro ⟨hy, hl, hu⟩
    by_cases hz : z.1 = e.1 + (n : ℤ) - k - 1
    · left
      ext <;> simp [step, hcast, hy, hz] <;> ring
    · right
      exact ⟨hy, by omega, hu⟩
  · rintro (rfl | ⟨hy, hl, hu⟩)
    · simp [step, hcast]
      omega
    · exact ⟨hy, by omega, hu⟩

variable {A : Type*} [Fintype A]

structure Rules (θ : G → A) (base : Finset G) (e : G) (n : ℕ) where
  forwardLength : ℕ
  backwardLength : ℕ
  forward_lt : forwardLength < n
  backward_lt : backwardLength < n
  forward : Determines θ (base ∪ rowSegment e forwardLength)
    (e + step (forwardLength : ℤ))
  backward : Determines θ (base ∪ rowSuffix e n backwardLength)
    (e + step ((n - backwardLength - 1 : ℕ) : ℤ))

/-- The strict edge budget supplies actual forward and backward rules. -/
theorem exists_rules (θ : G → A) (base : Finset G) (e : G) (n : ℕ)
    (hbudget : patternComplexity θ (base ∪ rowSegment e n) < patternComplexity θ base + n) :
    Nonempty (Rules θ base e n) := by
  let D : ℕ → Finset G := fun i => base ∪ rowSegment e i
  have hstep : ∀ i < n, patternComplexity θ (D i) ≤ patternComplexity θ (D (i + 1)) :=
    fun i _ => patternComplexity_mono θ
      (Finset.union_subset_union_right (rowSegment_mono e (by omega)))
  obtain ⟨k, hk, hplateau⟩ := exists_plateau_from_growth_budget
    (fun i => patternComplexity θ (D i)) hstep (by simpa [D] using hbudget)
  have hforward : Determines θ (base ∪ rowSegment e k) (e + step (k : ℤ)) := by
    apply determines_of_plateau
    simpa [D, rowSegment_succ, Finset.union_insert] using hplateau
  let D' : ℕ → Finset G := fun i => base ∪ rowSuffix e n i
  have hstep' : ∀ i < n, patternComplexity θ (D' i) ≤ patternComplexity θ (D' (i + 1)) :=
    fun i hi => patternComplexity_mono θ
      (Finset.union_subset_union_right (rowSuffix_mono e (by omega) (by omega)))
  obtain ⟨k', hk', hplateau'⟩ := exists_plateau_from_growth_budget
    (fun i => patternComplexity θ (D' i)) hstep'
    (by simpa [D'] using hbudget)
  have hbackward : Determines θ (base ∪ rowSuffix e n k')
      (e + step ((n - k' - 1 : ℕ) : ℤ)) := by
    apply determines_of_plateau
    simpa [D', rowSuffix_succ e hk', Finset.union_insert] using hplateau'
  exact ⟨⟨k, k', hk, hk', hforward, hbackward⟩⟩

variable {θ : G → A} {base : Finset G} {e : G} {n : ℕ}

theorem next_of_rule (R : Rules θ base e n) {x y : G → A}
    (hx : x ∈ languageHull θ) (hy : y ∈ languageHull θ) (v w : G) (i j : ℤ)
    (hbase : patternAt x base (v + step i) = patternAt y base (w + step j))
    (hword : wordAt (rowSequence x (e + v) horizontal) R.forwardLength i =
      wordAt (rowSequence y (e + w) horizontal) R.forwardLength j) :
    rowSequence x (e + v) horizontal (i + R.forwardLength) =
      rowSequence y (e + w) horizontal (j + R.forwardLength) := by
  have hp : patternAt x (base ∪ rowSegment e R.forwardLength) (v + step i) =
      patternAt y (base ∪ rowSegment e R.forwardLength) (w + step j) := by
    funext p
    rcases Finset.mem_union.mp p.property with hb | hr
    · exact congrFun hbase ⟨p.val, hb⟩
    · obtain ⟨l, hl, heq⟩ := (mem_rowSegment _ _ _).mp hr
      have h := congrFun hword ⟨l, hl⟩
      simpa [patternAt, wordAt, rowSequence_horizontal_apply, heq, step,
        add_assoc, add_comm, add_left_comm] using h
  have h := R.forward x hx y hy (v + step i) (w + step j) hp
  simpa [rowSequence_horizontal_apply, step, add_assoc, add_comm, add_left_comm] using h

theorem prev_of_rule (R : Rules θ base e n) {x y : G → A}
    (hx : x ∈ languageHull θ) (hy : y ∈ languageHull θ) (v w : G) (i j : ℤ)
    (hbase : patternAt x base (v + step (i - (n - R.backwardLength : ℕ))) =
      patternAt y base (w + step (j - (n - R.backwardLength : ℕ))))
    (hword : wordAt (rowSequence x (e + v) horizontal) R.backwardLength i =
      wordAt (rowSequence y (e + w) horizontal) R.backwardLength j) :
    rowSequence x (e + v) horizontal (i - 1) =
      rowSequence y (e + w) horizontal (j - 1) := by
  let a : ℤ := (n - R.backwardLength : ℕ)
  have hp : patternAt x (base ∪ rowSuffix e n R.backwardLength) (v + step (i - a)) =
      patternAt y (base ∪ rowSuffix e n R.backwardLength) (w + step (j - a)) := by
    funext p
    rcases Finset.mem_union.mp p.property with hb | hr
    · exact congrFun hbase ⟨p.val, hb⟩
    · obtain ⟨l, hl, heq⟩ := (mem_rowSegment _ _ _).mp hr
      have h := congrFun hword ⟨l, hl⟩
      simpa [patternAt, wordAt, rowSequence_horizontal_apply, rowSuffix, heq, a, step,
        sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  have h := R.backward x hx y hy (v + step (i - a)) (w + step (j - a)) hp
  have hcast : ((n - R.backwardLength - 1 : ℕ) : ℤ) = a - 1 := by
    dsimp [a]
    have := R.backward_lt
    omega
  simpa [rowSequence_horizontal_apply, hcast, step,
    sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h

theorem rows_eq_of_block (R : Rules θ base e n) {x y : G → A}
    (hx : x ∈ languageHull θ) (hy : y ∈ languageHull θ) (v w : G)
    (hbase : ∀ i : ℤ, patternAt x base (v + step i) = patternAt y base (w + step i))
    (hblock : ∃ i : ℤ, wordAt (rowSequence x (e + v) horizontal) R.forwardLength i =
      wordAt (rowSequence y (e + w) horizontal) R.forwardLength i) :
    rowSequence x (e + v) horizontal = rowSequence y (e + w) horizontal := by
  exact row_eq_of_two_sided_rules _ _ _ _
    (fun i hi => next_of_rule R hx hy v w i i (hbase i) hi)
    (fun i hi => prev_of_rule R hx hy v w i i (hbase _) hi) hblock

theorem rows_eq_of_pattern (R : Rules θ base e n) {x y : G → A}
    (hx : x ∈ languageHull θ) (hy : y ∈ languageHull θ) (v w : G)
    (hbase : ∀ i : ℤ, patternAt x base (v + step i) = patternAt y base (w + step i))
    (i : ℤ) (hp : patternAt x (base ∪ rowSegment e R.forwardLength) (v + step i) =
      patternAt y (base ∪ rowSegment e R.forwardLength) (w + step i)) :
    rowSequence x (e + v) horizontal = rowSequence y (e + w) horizontal := by
  apply rows_eq_of_block R hx hy v w hbase
  refine ⟨i, ?_⟩
  funext l
  have hs : e + step (l.val : ℤ) ∈ base ∪ rowSegment e R.forwardLength :=
    Finset.mem_union_right _ ((mem_rowSegment _ _ _).mpr ⟨l.val, l.isLt, rfl⟩)
  have h := congrFun hp ⟨e + step (l.val : ℤ), hs⟩
  simpa [patternAt, rowSequence_horizontal_apply, wordAt, step,
    add_assoc, add_comm, add_left_comm] using h

/-- The periodic phase is the actual base pattern, so the new row period is
a multiple of the old strip period. -/
theorem row_period_multiple (R : Rules θ base e n) (w : G) (Q : ℕ) (hQ : 0 < Q)
    (hphase : ∀ i j : ℤ, (i : ZMod Q) = (j : ZMod Q) →
      patternAt θ base (w + step i) = patternAt θ base (w + step j)) :
    ∃ q : ℕ, 0 < q ∧ Q ∣ q ∧ IsPeriod (rowSequence θ (e + w) horizontal) (q : ℤ) := by
  apply phased_row_period_multiple _ Q R.forwardLength R.backwardLength hQ
  · intro i j hij hword
    exact next_of_rule R (self_mem_languageHull θ) (self_mem_languageHull θ)
      w w i j (hphase i j hij) hword
  · intro i j hij hword
    apply prev_of_rule R (self_mem_languageHull θ) (self_mem_languageHull θ) w w i j _ hword
    apply hphase
    simpa only [Int.cast_sub] using
      congrArg (fun z : ZMod Q => z - ((n - R.backwardLength : ℕ) : ℤ)) hij

end

end NivatTrial.RowDetermination
