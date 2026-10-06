import ConvexNivat.ReductionDefinitions
import ConvexNivat.CorePatterns
namespace ConvexNivat
private def mhWord {A : Type*} (x : ℤ → A) (n : ℕ) (s : ℤ) : Fin n → A :=
  fun j => x (s + (j : ℕ))
private theorem mh_prefix_image {A : Type*} (x : ℤ → A) (n : ℕ) :
    (fun w : Fin (n + 1) → A => fun j : Fin n => w j.castSucc) '' Set.range (mhWord x (n+1)) =
      Set.range (mhWord x n) := by
  ext w
  constructor
  · rintro ⟨v, ⟨s, rfl⟩, rfl⟩
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨mhWord x (n+1) s, ⟨s, rfl⟩, rfl⟩
private theorem mh_suffix_image {A : Type*} (x : ℤ → A) (n : ℕ) :
    (fun w : Fin (n + 1) → A => fun j : Fin n => w j.succ) '' Set.range (mhWord x (n+1)) =
      Set.range (mhWord x n) := by
  ext w
  constructor
  · rintro ⟨v, ⟨s, rfl⟩, rfl⟩
    refine ⟨s+1, ?_⟩
    funext j
    simp [mhWord, Nat.cast_add, add_assoc, add_comm, add_left_comm]
  · rintro ⟨s, rfl⟩
    refine ⟨mhWord x (n+1) (s-1), ⟨s-1, rfl⟩, ?_⟩
    funext j
    simp [mhWord, Nat.cast_add]
private theorem mh_count_zero {A : Type*} (x : ℤ → A) :
    (Set.range (mhWord x 0)).ncard = 1 := by
  have he : Set.range (mhWord x 0) = {mhWord x 0 0} := by
    ext w
    constructor
    · rintro ⟨s, rfl⟩
      simp only [Set.mem_singleton_iff]
      funext j
      exact Fin.elim0 j
    · rintro rfl
      exact ⟨0, rfl⟩
  simp [he]
private theorem mh_count_mono {A : Type*} [Finite A] (x : ℤ → A) (n : ℕ) :
    (Set.range (mhWord x n)).ncard ≤ (Set.range (mhWord x (n+1))).ncard := by
  rw [← mh_prefix_image]
  exact Set.ncard_image_le (Set.toFinite _)
private theorem mh_plateau {A : Type*} [Finite A] (x : ℤ → A)
    (m : ℕ) (hm : 0 < m) (h : (Set.range (mhWord x m)).ncard ≤ m) :
    ∃ n < m, (Set.range (mhWord x (n+1))).ncard = (Set.range (mhWord x n)).ncard := by
  by_contra hn
  have hne : ∀ n < m, (Set.range (mhWord x n)).ncard <
      (Set.range (mhWord x (n+1))).ncard := by
    intro n hn'
    apply lt_of_le_of_ne (mh_count_mono x n)
    intro he
    exact hn ⟨n, hn', he.symm⟩
  have hb : ∀ n ≤ m, n+1 ≤ (Set.range (mhWord x n)).ncard := by
    intro n
    induction n with
    | zero => intro hn'; rw [mh_count_zero]
    | succ n ih =>
      intro hn'
      have hi := ih (by omega)
      have hg := hne n (by omega)
      omega
  have hb' := hb m le_rfl
  omega
private theorem mh_deterministic {A : Type*} [Finite A] (x : ℤ → A) (n : ℕ)
    (h : (Set.range (mhWord x (n+1))).ncard = (Set.range (mhWord x n)).ncard) :
    (∀ s t, mhWord x n s = mhWord x n t → mhWord x n (s+1) = mhWord x n (t+1)) ∧
    (∀ s t, mhWord x n (s+1) = mhWord x n (t+1) → mhWord x n s = mhWord x n t) := by
  have hp : Set.InjOn (fun w : Fin (n+1) → A => fun j : Fin n => w j.castSucc)
      (Set.range (mhWord x (n+1))) := by
    apply Set.injOn_of_ncard_image_eq (hs := Set.toFinite _)
    rw [mh_prefix_image, h]
  have hs : Set.InjOn (fun w : Fin (n+1) → A => fun j : Fin n => w j.succ)
      (Set.range (mhWord x (n+1))) := by
    apply Set.injOn_of_ncard_image_eq (hs := Set.toFinite _)
    rw [mh_suffix_image, h]
  constructor
  · intro s t he
    have he' := hp (Set.mem_range_self s) (Set.mem_range_self t) he
    funext j
    have hj := congrFun he' j.succ
    simpa [mhWord, Nat.cast_add, add_assoc, add_comm, add_left_comm] using hj
  · intro s t he
    have he0 : (fun j : Fin n => mhWord x (n+1) s j.succ) =
        (fun j : Fin n => mhWord x (n+1) t j.succ) := by
      funext j
      simpa [mhWord, Nat.cast_add, add_assoc, add_comm, add_left_comm] using congrFun he j
    have he' := hs (Set.mem_range_self s) (Set.mem_range_self t) he0
    funext j
    exact congrFun he' j.castSucc
-- Reversible finite trajectory proof copied from finite_state/FiniteState.lean;
-- that sealed artifact proves the same private implementation for Lemma 8.8.
private theorem mh_finite_trajectory {S : Type*} [Finite S] (x : ℕ → S)
    (hf : ∀ a b, x a = x b → x (a + 1) = x (b + 1))
    (hb : ∀ a b, x (a + 1) = x (b + 1) → x a = x b) :
    ∃ q : ℕ, 0 < q ∧ ∀ n, x (n + q) = x n := by
  classical
  obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite x
  have rewind : ∀ a d, x (a + d) = x a → x d = x 0 := by
    intro a
    induction a with
    | zero => intro d h; simpa using h
    | succ a ih =>
      intro d h
      apply ih d
      apply hb (a + d) a
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have finish : ∀ q, 0 < q → x q = x 0 →
      ∃ q : ℕ, 0 < q ∧ ∀ n, x (n + q) = x n := by
    intro q hq hx
    refine ⟨q, hq, ?_⟩
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf _ _ ih
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · apply finish (b - a) (by omega)
    apply rewind a
    simpa [Nat.add_sub_of_le (Nat.le_of_lt hlt)] using heq.symm
  · apply finish (a - b) (by omega)
    apply rewind b
    simpa [Nat.add_sub_of_le (Nat.le_of_lt hlt)] using heq
private theorem mh_bi_period {S : Type*} [Finite S] (x : ℤ → S)
    (hf : ∀ s t, x s = x t → x (s+1) = x (t+1))
    (hb : ∀ s t, x (s+1) = x (t+1) → x s = x t) :
    ∃ q : ℤ, 1 ≤ q ∧ ∀ s, x (s+q) = x s := by
  obtain ⟨q, hq, he⟩ := mh_finite_trajectory (fun n : ℕ => x n)
    (by intro a b h; simpa only [Nat.cast_add, Nat.cast_one] using hf a b h)
    (by intro a b h; apply hb a b; simpa only [Nat.cast_add, Nat.cast_one] using h)
  refine ⟨q, by omega, ?_⟩
  have hnegative : ∀ n : ℕ, x (-(n : ℤ) + q) = x (-(n : ℤ)) := by
    intro n
    induction n with
    | zero => simpa using he 0
    | succ n ih =>
      apply hb
      simpa [Nat.cast_add, Nat.cast_one, neg_add_rev, add_assoc, add_comm, add_left_comm] using ih
  intro s
  by_cases hs : 0 ≤ s
  · have ht : (s.toNat : ℤ) = s := Int.toNat_of_nonneg hs
    simpa only [Nat.cast_add, ht] using he s.toNat
  · have ht : ((-s).toNat : ℤ) = -s := Int.toNat_of_nonneg (by omega)
    simpa only [ht, neg_neg] using hnegative (-s).toNat
theorem morseHedlund_obligation {A : Type*} [Finite A] (x : ℤ → A)
    (m : ℕ) (hm : 0 < m)
    (hcomplexity : (Set.range (fun s : ℤ => fun j : Fin m => x (s + (j : ℕ)))).ncard ≤ m) :
    ∃ q : ℤ, 1 ≤ q ∧ ∀ s, x (s + q) = x s := by
  obtain ⟨n, hn, hplateau⟩ := mh_plateau x m hm hcomplexity
  obtain ⟨hf, hb⟩ := mh_deterministic x n hplateau
  have hfull : ∀ s t, mhWord x n s = mhWord x n t →
      mhWord x (n+1) s = mhWord x (n+1) t := by
    have hp : Set.InjOn (fun w : Fin (n+1) → A => fun j : Fin n => w j.castSucc)
        (Set.range (mhWord x (n+1))) := by
      apply Set.injOn_of_ncard_image_eq (hs := Set.toFinite _)
      rw [mh_prefix_image, hplateau]
    intro s t he
    exact hp (Set.mem_range_self s) (Set.mem_range_self t) he
  obtain ⟨q, hq, hp⟩ := mh_bi_period (mhWord x n) hf hb
  refine ⟨q, hq, ?_⟩
  intro s
  simpa [mhWord] using congrFun (hfull (s+q) s (hp s)) ⟨0, by omega⟩
end ConvexNivat
