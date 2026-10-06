import ConvexNivat.AppendixBalanced

namespace ConvexNivat
open scoped BigOperators

private theorem d_rule_agreement {A : Type*} (x y : ℤ → A) (k k' : ℕ)
    (hf : ∀ s : ℤ, (∀ j : ℕ, j < k → x (s+j)=y (s+j)) → x (s+k)=y (s+k))
    (hb : ∀ s : ℤ, (∀ j : ℕ, j < k' → x (s+j)=y (s+j)) → x (s-1)=y (s-1))
    (i : ℤ) (hi : ∀ j : ℕ, j < k → x (i+j)=y (i+j)) : x = y := by
  by_cases hk : k = 0
  · funext s
    simpa only [hk,Nat.cast_zero,add_zero] using hf s (by simp [hk])
  have hfuture : ∀ n : ℕ, x (i+n)=y (i+n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < k
      · exact hi n hn
      · have he := hf (i+((n-k : ℕ) : ℤ)) (by
          intro j hj
          have hnj : n-k+j < n := by omega
          have he' := ih (n-k+j) hnj
          simpa only [Nat.cast_add,add_assoc] using he')
        convert he using 1 <;> congr 1 <;> omega
  have hpast : ∀ n : ℕ, x (i-n)=y (i-n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n=0
      · simpa only [hn,Nat.cast_zero,sub_zero,add_zero] using hfuture 0
      · have he := hb (i-(n : ℤ)+1) (by
          intro j hj
          by_cases hnj : n ≤ j+1
          · have he' := hfuture (j+1-n)
            convert he' using 1 <;> congr 1 <;> omega
          · have he' := ih (n-1-j) (by omega)
            convert he' using 1 <;> congr 1 <;> omega)
        simpa only [add_sub_cancel_right] using he
  funext s
  by_cases hs : i ≤ s
  · have he := hfuture (s-i).toNat
    have hc : ((s-i).toNat : ℤ)=s-i := Int.toNat_of_nonneg (by omega)
    simpa only [hc,add_sub_cancel] using he
  · have he := hpast (i-s).toNat
    have hc : ((i-s).toNat : ℤ)=i-s := Int.toNat_of_nonneg (by omega)
    simpa only [hc,sub_sub_cancel] using he
private theorem d_disagreement {A : Type*} [Finite A]
    (θ x : Configuration A) (hx : x ∈ OrbitClosure θ)
    (u e w : Lattice) (D : Finset Lattice) (n k k' : ℕ)
    (hk : k < n) (hk' : k' < n)
    (hleft : PatternDetermines θ
      (D ∪ (Finset.range k).image (fun j : ℕ => e + (j : ℤ) • u)) (e+(k : ℤ)•u))
    (hright : PatternDetermines θ
      (D ∪ (Finset.range k').image (fun j : ℕ => e+((n-1-j : ℕ) : ℤ)•u))
      (e+((n-1-k' : ℕ) : ℤ)•u))
    (hagrees : ∀ i : ℤ, ∀ z ∈ D, x (z+w+i•u)=θ (z+w+i•u))
    (hdefect : ∃ s : ℤ, x (e+w+s•u) ≠ θ (e+w+s•u)) :
    ∀ i : ℤ, ¬ (∀ j : ℕ, j < k → x (e+w+(i+j)•u)=θ (e+w+(i+j)•u)) := by
  classical
  let a : ℤ → A := fun s => x (e+w+s•u)
  let b : ℤ → A := fun s => θ (e+w+s•u)
  have hf : ∀ s : ℤ, (∀ j : ℕ, j < k → a (s+j)=b (s+j)) → a (s+k)=b (s+k) := by
    intro s hs
    have he := hleft x hx θ (orbitClosure_self θ) (w+s•u) (by
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · simpa only [add_assoc] using hagrees s z hz
      · rcases Finset.mem_image.mp hz with ⟨j,hj,rfl⟩
        have hj' := Finset.mem_range.mp hj
        have he := hs j hj'
        simpa only [a,b,add_smul,add_assoc,add_comm,add_left_comm] using he)
    simpa only [a,b,add_smul,add_assoc,add_comm,add_left_comm] using he
  have hb : ∀ s : ℤ, (∀ j : ℕ, j < k' → a (s+j)=b (s+j)) → a (s-1)=b (s-1) := by
    intro s hs
    let r : ℤ := s - ((n-k' : ℕ) : ℤ)
    have he := hright x hx θ (orbitClosure_self θ) (w+r•u) (by
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · simpa only [add_assoc] using hagrees r z hz
      · rcases Finset.mem_image.mp hz with ⟨j,hj,rfl⟩
        have hj' := Finset.mem_range.mp hj
        have hindex : k'-1-j < k' := by omega
        have he := hs (k'-1-j) hindex
        have hcoord : ((n-1-j : ℕ) : ℤ) + r = s + ((k'-1-j : ℕ) : ℤ) := by
          dsimp [r]
          omega
        have hcoord' : r + ((n-1-j : ℕ) : ℤ) = s + ((k'-1-j : ℕ) : ℤ) := by
          dsimp [r]
          omega
        have hpoint : e + ((n-1-j : ℕ) : ℤ) • u + (w+r•u) =
            e+w+(s+((k'-1-j : ℕ) : ℤ))•u := by
          rw [← hcoord',add_smul]
          abel
        simpa only [a,b,hpoint] using he)
    have hcoord : ((n-1-k' : ℕ) : ℤ)+r=s-1 := by dsimp [r]; omega
    have hpoint : e+((n-1-k' : ℕ) : ℤ)•u+(w+r•u)=e+w+(s-1)•u := by
      rw [← hcoord,add_smul]
      abel
    simpa only [a,b,hpoint] using he
  intro i hi
  have heq := d_rule_agreement a b k k' hf hb i hi
  obtain ⟨s,hs⟩ := hdefect
  exact hs (congrFun heq s)

private theorem d_extension_count {P Q : Type*} [Finite P] [Finite Q]
    (r : P → Q) (hsurj : Function.Surjective r) (Γ : Set Q)
    (hΓ : ∀ γ ∈ Γ, ∃ a b : P, a ≠ b ∧ r a=γ ∧ r b=γ) :
    Nat.card Q + Γ.ncard ≤ Nat.card P := by
  classical
  let base : Q → P := Function.surjInv hsurj
  have hbase : ∀ q, r (base q)=q := Function.rightInverse_surjInv hsurj
  have hextra : ∀ γ : Γ, ∃ a : P, a ≠ base γ.val ∧ r a=γ.val := by
    intro γ
    obtain ⟨a,b,hab,ha,hb⟩ := hΓ γ.val γ.property
    by_cases he : a=base γ.val
    · exact ⟨b,by intro h; exact hab (he.trans h.symm),hb⟩
    · exact ⟨a,he,ha⟩
  let extra : Γ → P := fun γ => (hextra γ).choose
  have hextra_ne : ∀ γ, extra γ ≠ base γ.val := fun γ => (hextra γ).choose_spec.1
  have hextra_r : ∀ γ, r (extra γ)=γ.val := fun γ => (hextra γ).choose_spec.2
  let f : Q ⊕ Γ → P := Sum.elim base extra
  have hinj : Function.Injective f := by
    intro a b he
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have h := congrArg r he
        dsimp [f] at h
        rw [hbase,hbase] at h
        exact congrArg Sum.inl h
      | inr b =>
        have h := congrArg r he
        dsimp [f] at h he
        rw [hbase,hextra_r] at h
        subst a
        exact (hextra_ne b he.symm).elim
    | inr a =>
      cases b with
      | inl b =>
        have h := congrArg r he
        dsimp [f] at h he
        rw [hextra_r,hbase] at h
        subst b
        exact (hextra_ne a he).elim
      | inr b =>
        have h := congrArg r he
        dsimp [f] at h
        rw [hextra_r,hextra_r] at h
        exact congrArg Sum.inr (Subtype.ext h)
  have hc := Nat.card_le_card_of_injective f hinj
  simpa only [Nat.card_sum,Set.ncard_eq_toFinset_card',Nat.card_coe_set_eq] using hc
private theorem d_pattern_count {A : Type*} [Finite A]
    (θ x : Configuration A) (hx : x ∈ OrbitClosure θ)
    (B D : Finset Lattice) (hDB : D ⊆ B) (u w : Lattice)
    (hagrees : ∀ i : ℤ, ∀ z ∈ D, x (w+i•u+z)=θ (w+i•u+z))
    (hdifferent : ∀ i : ℤ, pattern x B (w+i•u) ≠ pattern θ B (w+i•u)) :
    complexity θ D + (Set.range (fun i : ℤ => pattern θ D (w+i•u))).ncard ≤ complexity θ B := by
  classical
  let P := patternSet θ B
  let Q := patternSet θ D
  let r₀ : Pattern A B → Pattern A D := fun p z => p ⟨z.val,hDB z.property⟩
  have hr : ∀ p ∈ P, r₀ p ∈ Q := by
    rintro p ⟨s,rfl⟩
    exact ⟨s,rfl⟩
  let r : P → Q := fun p => ⟨r₀ p.val,hr p.val p.property⟩
  have hsurj : Function.Surjective r := by
    rintro ⟨q,s,rfl⟩
    exact ⟨⟨pattern θ B s,Set.mem_range_self s⟩,rfl⟩
  let γ : ℤ → Q := fun i => ⟨pattern θ D (w+i•u),Set.mem_range_self _⟩
  let Γ := Set.range γ
  have hc := d_extension_count r hsurj Γ (by
    rintro q ⟨i,rfl⟩
    let a : P := ⟨pattern x B (w+i•u),
      orbitClosure_patternSet_subset θ x hx B (Set.mem_range_self _)⟩
    let b : P := ⟨pattern θ B (w+i•u),Set.mem_range_self _⟩
    refine ⟨a,b,?_,?_,rfl⟩
    · intro he
      exact hdifferent i (congrArg Subtype.val he)
    · apply Subtype.ext
      funext z
      exact hagrees i z.val z.property)
  have hΓ : Subtype.val '' Γ = Set.range (fun i : ℤ => pattern θ D (w+i•u)) := by
    ext z
    constructor
    · rintro ⟨q,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨γ i,Set.mem_range_self i,rfl⟩
  have hΓcard : Γ.ncard = (Set.range (fun i : ℤ => pattern θ D (w+i•u))).ncard := by
    rw [← hΓ]
    exact (Set.ncard_image_of_injective _ Subtype.val_injective).symm
  simpa only [Nat.card_coe_set_eq,hΓcard,P,Q,complexity] using hc

private theorem d_row_coordinates (u v w z : Lattice) (hv : det u v = 1)
    (hrow : det u z = det u w) : ∃ s : ℤ, z=w+s•u := by
  refine ⟨det z v-det w v,?_⟩
  have hb : ∀ z : Lattice, z=det z v•u+det u z•v := by
    intro z
    have he : det u v•z=det z v•u+det u z•v := by
      ext <;> simp [det] <;> ring
    simpa only [hv,one_smul] using he
  calc
    z = det z v • u + det u z • v := hb z
    _ = (det w v • u + det u w • v) + (det z v-det w v) • u := by
      rw [hrow,sub_smul]
      abel
    _ = w+(det z v-det w v)•u := by rw [← hb w]
private theorem d_low_row {A : Type*} [Finite A]
    (θ : Configuration A) (u : Lattice) (hu : Primitive u) (D : Finset Lattice)
    (hconvex : LatticeConvex D) (w : Lattice) (m : ℕ) (hm : 0 < m)
    (hlow : (Set.range (fun i : ℤ => pattern θ D (w+i•u))).ncard ≤ m)
    (t : ℤ) (hrow : m ≤ (D.filter (fun z => det u z=t)).card) :
    ∃ q : ℤ, 1 ≤ q ∧ ∀ z, det u z=t+det u w → θ (z+q•u)=θ z := by
  classical
  have hne : (D.filter (fun z => det u z=t)).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨e,he,henum⟩ := row_is_consecutive u hu D hconvex t hne
  let x : ℤ → A := fun s => θ (e+w+s•u)
  let r : Pattern A D → Fin m → A := fun p j =>
    p ⟨e+(j.val : ℤ)•u,((henum _).mpr ⟨j.val,by omega,rfl⟩).1⟩
  have hrange : r '' Set.range (fun i : ℤ => pattern θ D (w+i•u)) =
      Set.range (fun s : ℤ => fun j : Fin m => x (s+j.val)) := by
    ext a
    constructor
    · rintro ⟨p,⟨i,rfl⟩,rfl⟩
      refine ⟨i,?_⟩
      funext j
      simp only [r,pattern,x,add_smul,add_assoc,add_comm,add_left_comm]
    · rintro ⟨i,rfl⟩
      refine ⟨pattern θ D (w+i•u),Set.mem_range_self i,?_⟩
      funext j
      simp only [r,pattern,x,add_smul,add_assoc,add_comm,add_left_comm]
  have hwords : (Set.range (fun s : ℤ => fun j : Fin m => x (s+j.val))).ncard ≤ m := by
    rw [← hrange]
    exact (Set.ncard_image_le (Set.toFinite _)).trans hlow
  obtain ⟨q,hq,hperiod⟩ := morseHedlund_obligation x m hm hwords
  obtain ⟨v,hv⟩ := primitive_height_surjective u hu 1
  change det u v=1 at hv
  refine ⟨q,hq,?_⟩
  intro z hz
  have hew : det u (e+w)=t+det u w := by
    change height u (e+w)=t+height u w
    rw [height_add]
    exact congrArg (fun a => a+height u w) he
  obtain ⟨s,rfl⟩ := d_row_coordinates u v (e+w) z hv (hz.trans hew.symm)
  simpa only [x,add_smul,add_assoc] using hperiod s

private theorem d_common_period {A : Type*} (θ : Configuration A) (u : Lattice)
    (T : Finset ℤ) (hrows : ∀ t ∈ T, ∃ q : ℤ, 1 ≤ q ∧
      ∀ z, det u z=t → θ (z+q•u)=θ z) :
    ∃ q : ℤ, 1 ≤ q ∧ ∀ z, det u z ∈ T → θ (z+q•u)=θ z := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1,le_rfl,by simp⟩
  | @insert t T ht ih =>
    obtain ⟨q,hq,hqp⟩ := hrows t (Finset.mem_insert_self _ _)
    obtain ⟨r,hr,hrp⟩ := ih (fun s hs => hrows s (Finset.mem_insert_of_mem hs))
    have hmultiples : ∀ q : ℤ, ∀ V : Set ℤ,
        (∀ z, det u z ∈ V → θ (z+q•u)=θ z) →
        ∀ n : ℕ, ∀ z, det u z ∈ V → θ (z+(n : ℤ)•(q•u))=θ z := by
      intro q V hp n
      induction n with
      | zero => intro z hz; simp
      | succ n ih =>
        intro z hz
        have hz' : det u (z+(n : ℤ)•(q•u)) ∈ V := by
          change height u (z+(n : ℤ)•(q•u)) ∈ V
          rw [height_add,height_zsmul,height_zsmul,height_self,mul_zero,mul_zero,add_zero]
          exact hz
        calc
          θ (z+((n+1 : ℕ) : ℤ)•(q•u))=θ ((z+(n : ℤ)•(q•u))+q•u) := by
            simp only [Nat.cast_add,Nat.cast_one,add_smul,one_smul,add_assoc]
          _=θ (z+(n : ℤ)•(q•u)) := hp _ hz'
          _=θ z := ih z hz
    refine ⟨q*r,by nlinarith,?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with hz | hz
    · have he := hmultiples q {t} (by intro z hz; exact hqp z hz) r.toNat z hz
      have hc : (r.toNat : ℤ)=r := Int.toNat_of_nonneg (by omega)
      simpa only [hc,smul_smul,mul_comm r q] using he
    · have he := hmultiples r (T : Set ℤ) hrp q.toNat z hz
      have hc : (q.toNat : ℤ)=q := Int.toNat_of_nonneg (by omega)
      simpa only [hc,smul_smul] using he

-- Same reversible trajectory implementation as the sealed finite_state package.
private theorem d_finite_trajectory {S : Type*} [Finite S] (x : ℕ → S)
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

private theorem d_bi_period {S : Type*} [Finite S] (x : ℤ → S)
    (hf : ∀ s t, x s = x t → x (s+1) = x (t+1))
    (hb : ∀ s t, x (s+1) = x (t+1) → x s = x t) :
    ∃ q : ℤ, 1 ≤ q ∧ ∀ s, x (s+q) = x s := by
  obtain ⟨q, hq, he⟩ := d_finite_trajectory (fun n : ℕ => x n)
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

private theorem d_upper_row {A : Type*} [Finite A] (y : ℤ → A)
    (Q : ℕ) (hQ : 0 < Q) (k k' : ℕ)
    (hf : ∀ s t : ℤ, (s : ZMod Q) = (t : ZMod Q) →
      (∀ j : ℕ, j < k → y (s+j)=y (t+j)) → y (s+k)=y (t+k))
    (hb : ∀ s t : ℤ, (s : ZMod Q) = (t : ZMod Q) →
      (∀ j : ℕ, j < k' → y (s+j)=y (t+j)) → y (s-1)=y (t-1)) :
    ∃ q : ℤ, 1 ≤ q ∧ (Q : ℤ) ∣ q ∧ ∀ s, y (s+q)=y s := by
  let : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  let K := max (max k k') 1
  have hk : k ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hk' : k' ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  have hK : 0 < K := by dsimp [K]; omega
  let state : ℤ → ZMod Q × (Fin K → A) := fun s => ((s : ZMod Q), fun j => y (s+j))
  have forward : ∀ s t, state s = state t → state (s+1)=state (t+1) := by
    intro s t he
    have hphase : (s : ZMod Q) = (t : ZMod Q) := congrArg Prod.fst he
    have hword : ∀ j : ℕ, j < K → y (s+j)=y (t+j) := by
      intro j hj
      exact congrFun (congrArg Prod.snd he) ⟨j,hj⟩
    apply Prod.ext
    · change ((s+1 : ℤ) : ZMod Q) = ((t+1 : ℤ) : ZMod Q)
      simp only [Int.cast_add,Int.cast_one,hphase]
    · funext j
      change y (s+1+j.val)=y (t+1+j.val)
      by_cases hj : j.val+1 < K
      · simpa only [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using hword (j.val+1) hj
      · have hjK : j.val+1=K := by omega
        have hphase' : ((s+((K-k : ℕ) : ℤ) : ℤ) : ZMod Q) = ((t+((K-k : ℕ) : ℤ) : ℤ) : ZMod Q) := by
          simp only [Int.cast_add,hphase]
        have hlast := hf (s+((K-k : ℕ) : ℤ)) (t+((K-k : ℕ) : ℤ)) hphase' (by
          intro i hi
          have hiK : K-k+i < K := by omega
          have hpoint := hword (K-k+i) hiK
          simpa only [Nat.cast_add,add_assoc] using hpoint)
        have hkj : ((K-k : ℕ) : ℤ) + k = j.val+1 := by omega
        convert hlast using 1 <;> congr 1 <;> omega
  have backward : ∀ s t, state (s+1)=state (t+1) → state s=state t := by
    intro s t he
    have hphase : ((s+1 : ℤ) : ZMod Q) = ((t+1 : ℤ) : ZMod Q) := congrArg Prod.fst he
    have hword : ∀ j : ℕ, j < K → y (s+1+j)=y (t+1+j) := by
      intro j hj
      exact congrFun (congrArg Prod.snd he) ⟨j,hj⟩
    apply Prod.ext
    · dsimp only [state]
      simpa only [Int.cast_add,Int.cast_one,add_left_inj] using hphase
    · funext j
      change y (s+j.val)=y (t+j.val)
      by_cases hj : j.val=0
      · have he0 := hb (s+1) (t+1) hphase (fun i hi => hword i (by omega))
        simpa only [add_sub_cancel_right,hj,Nat.cast_zero,add_zero] using he0
      · have hj0 : 0 < j.val := by omega
        have he1 := hword (j.val-1) (by omega)
        have he2 : ((j.val-1 : ℕ) : ℤ)+1=j.val := by omega
        convert he1 using 1 <;> congr 1 <;> omega
  obtain ⟨q,hq,hperiod⟩ := d_bi_period state forward backward
  refine ⟨q,hq,?_,?_⟩
  · have he := congrArg Prod.fst (hperiod 0)
    have hc : (q : ZMod Q)=0 := by simpa [state] using he
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd q Q).mp hc
  · intro s
    simpa [state] using congrFun (congrArg Prod.snd (hperiod s)) ⟨0,hK⟩

private theorem d_strip_multiple {A : Type*} (θ : Configuration A) (u : Lattice)
    (a b q : ℤ) (hp : ∀ z ∈ latticeStrip u a b, θ (z+q•u)=θ z) :
    ∀ r : ℤ, ∀ z ∈ latticeStrip u a b, θ (z+r•(q•u))=θ z := by
  have hnat : ∀ n : ℕ, ∀ z ∈ latticeStrip u a b, θ (z+(n : ℤ)•(q•u))=θ z := by
    intro n
    induction n with
    | zero => intro z hz; simp
    | succ n ih =>
      intro z hz
      have hz' : z+(n : ℤ)•(q•u) ∈ latticeStrip u a b := by
        simpa only [smul_smul] using strip_invariant u a b ((n : ℤ)*q) z hz
      calc
        θ (z+((n+1 : ℕ) : ℤ)•(q•u))=θ ((z+(n : ℤ)•(q•u))+q•u) := by
          simp only [Nat.cast_add,Nat.cast_one,add_smul,one_smul,add_assoc]
        _=θ (z+(n : ℤ)•(q•u)) := hp _ hz'
        _=θ z := ih z hz
  intro r z hz
  rcases r with n | n
  · exact hnat n z hz
  · have hz' : z+(Int.negSucc n)•(q•u) ∈ latticeStrip u a b := by
      simpa only [smul_smul] using strip_invariant u a b ((Int.negSucc n)*q) z hz
    have he := hnat (n+1) (z+(Int.negSucc n)•(q•u)) hz'
    have hpoint : z+(Int.negSucc n)•(q•u)+((n+1 : ℕ) : ℤ)•(q•u)=z := by
      rw [add_assoc,← add_smul]
      simp
    exact (hpoint ▸ he).symm

private theorem d_strip_phase {A : Type*} (θ : Configuration A) (u : Lattice)
    (a b q : ℤ) (hq : 1≤q) (hp : ∀ z ∈ latticeStrip u a b, θ (z+q•u)=θ z)
    (s t : ℤ) (hphase : (s : ZMod q.toNat)=(t : ZMod q.toNat)) :
    ∀ z ∈ latticeStrip u a b, θ (z+s•u)=θ (z+t•u) := by
  have hc : (q.toNat : ℤ)=q := Int.toNat_of_nonneg (by omega)
  have hdvd : q ∣ t-s := by
    rw [← hc]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub s t q.toNat).mp hphase
  obtain ⟨r,hr⟩ := hdvd
  intro z hz
  have he := d_strip_multiple θ u a b q hp r (z+s•u) (strip_invariant u a b s z hz)
  have hpoint : z+s•u+r•(q•u)=z+t•u := by
    rw [smul_smul,mul_comm r q,← hr]
    rw [add_assoc,← add_smul]
    congr 1
    congr 1
    ring
  exact (hpoint ▸ he).symm

private theorem d_extend_row {A : Type*} [Finite A] (θ : Configuration A)
    (u : Lattice) (hu : Primitive u) (e w : Lattice)
    (D : Finset Lattice) (n k k' : ℕ) (hk : k<n) (hk' : k'<n)
    (a R q : ℤ) (hq : 1≤q)
    (hplace : ∀ z ∈ D, z+w ∈ latticeStrip u a (R-1))
    (hew : det u (e+w)=R)
    (hleft : PatternDetermines θ
      (D ∪ (Finset.range k).image (fun j : ℕ => e+(j : ℤ)•u)) (e+(k : ℤ)•u))
    (hright : PatternDetermines θ
      (D ∪ (Finset.range k').image (fun j : ℕ => e+((n-1-j : ℕ) : ℤ)•u))
      (e+((n-1-k' : ℕ) : ℤ)•u))
    (hp : ∀ z ∈ latticeStrip u a (R-1), θ (z+q•u)=θ z) :
    ∃ q' : ℤ, 1≤q' ∧ ∀ z ∈ latticeStrip u a R, θ (z+q'•u)=θ z := by
  let y : ℤ → A := fun s => θ (e+w+s•u)
  have hf : ∀ s t : ℤ, (s : ZMod q.toNat)=(t : ZMod q.toNat) →
      (∀ j : ℕ, j<k → y (s+j)=y (t+j)) → y (s+k)=y (t+k) := by
    intro s t hphase hs
    have he := hleft (translate (s•u) θ) (orbitClosure_translate θ (s•u))
      (translate (t•u) θ) (orbitClosure_translate θ (t•u)) w (by
        intro z hz
        rcases Finset.mem_union.mp hz with hz | hz
        · exact d_strip_phase θ u a (R-1) q hq hp s t hphase (z+w) (hplace z hz)
        · rcases Finset.mem_image.mp hz with ⟨j,hj,rfl⟩
          have he := hs j (Finset.mem_range.mp hj)
          simpa only [translate,y,add_smul,add_assoc,add_comm,add_left_comm] using he)
    simpa only [translate,y,add_smul,add_assoc,add_comm,add_left_comm] using he
  have hb : ∀ s t : ℤ, (s : ZMod q.toNat)=(t : ZMod q.toNat) →
      (∀ j : ℕ, j<k' → y (s+j)=y (t+j)) → y (s-1)=y (t-1) := by
    intro s t hphase hs
    let r : ℤ := -((n-k' : ℕ) : ℤ)
    have he := hright (translate (s•u) θ) (orbitClosure_translate θ (s•u))
      (translate (t•u) θ) (orbitClosure_translate θ (t•u)) (w+r•u) (by
        intro z hz
        rcases Finset.mem_union.mp hz with hz | hz
        · have he := d_strip_phase θ u a (R-1) q hq hp s t hphase
            ((z+w)+r•u) (strip_invariant u a (R-1) r (z+w) (hplace z hz))
          simpa only [translate,add_assoc] using he
        · rcases Finset.mem_image.mp hz with ⟨j,hj,rfl⟩
          have hj' := Finset.mem_range.mp hj
          have hjk : k'-1-j<k' := by omega
          have he := hs (k'-1-j) hjk
          have hcoord : ((n-1-j : ℕ) : ℤ)+r=((k'-1-j : ℕ) : ℤ) := by
            dsimp [r]
            omega
          have hpoint : e+((n-1-j : ℕ) : ℤ)•u+(w+r•u)=e+w+((k'-1-j : ℕ) : ℤ)•u := by
            rw [← hcoord,add_smul]
            abel
          simpa only [translate,y,hpoint,add_smul,add_assoc,add_comm,add_left_comm] using he)
    have hcoord : ((n-1-k' : ℕ) : ℤ)+r= -1 := by dsimp [r]; omega
    have hpoint : e+((n-1-k' : ℕ) : ℤ)•u+(w+r•u)=e+w+(-1 : ℤ)•u := by
      rw [← hcoord,add_smul]
      abel
    simpa only [translate,y,hpoint,sub_eq_add_neg,add_smul,add_assoc,add_comm,add_left_comm] using he
  have hQ : 0<q.toNat := by omega
  obtain ⟨q',hq',hdvd,hrow⟩ := d_upper_row y q.toNat hQ k k' hf hb
  have hc : (q.toNat : ℤ)=q := Int.toNat_of_nonneg (by omega)
  rw [hc] at hdvd
  obtain ⟨r,hr⟩ := hdvd
  obtain ⟨v,hv⟩ := primitive_height_surjective u hu 1
  change det u v=1 at hv
  refine ⟨q',hq',?_⟩
  intro z hz
  by_cases hbelow : det u z≤R-1
  · have he := d_strip_multiple θ u a (R-1) q hp r z ⟨hz.1,hbelow⟩
    simpa only [hr,smul_smul,mul_comm r q] using he
  · have hzrow : det u z=R := by have := hz.2; omega
    obtain ⟨s,rfl⟩ := d_row_coordinates u v (e+w) z hv (hzrow.trans hew.symm)
    simpa only [y,add_smul,add_assoc] using hrow s

/-- D.7: the ambient two-periodic-component hypothesis comes from D.1 and
is retained here instead of treating θ as an arbitrary configuration. -/
theorem lemmaD_7 (p : ℕ) (hp : p.Prime) (θ₁ θ₂ : Configuration (ZMod p))
    (u h₁ h₂ : Lattice) (hu : Primitive u) (c₁ : ℤ) (hc₁ : 1 ≤ c₁)
    (hh₁ : h₁ = c₁ • u) (hperiod₁ : HasPeriod θ₁ h₁)
    (hperiod₂ : HasPeriod θ₂ h₂) (hΔ : 0 < det u h₂)
    (B : Finset Lattice) (hB : BalancedSet (fun z => θ₁ z + θ₂ z) u 1 B)
    (a b : ℤ) (hambiguity : AmbiguityStrip (fun z => θ₁ z + θ₂ z) u a b)
    (hfits : rowHeight u B hB.nonempty ≤ b - a) :
    Periodic (fun z => θ₁ z + θ₂ z)  := by
  classical
  let : NeZero p := ⟨hp.ne_zero⟩
  let θ : Configuration (ZMod p) := fun z => θ₁ z+θ₂ z
  let E := extremeRow 1 u B hB.nonempty
  let D := B \ E
  let n := E.card
  let lo := rowMinimum u B hB.nonempty
  let hi := rowMaximum u B hB.nonempty
  have hEne : E.Nonempty := by
    obtain ⟨z,hz,he⟩ := Finset.exists_mem_eq_sup' hB.nonempty (det u)
    exact ⟨z,Finset.mem_filter.mpr ⟨hz,by simpa [E,extremeRow,rowMaximum] using he.symm⟩⟩
  obtain ⟨e,he,henum⟩ := row_is_consecutive u hu B hB.convex hi hEne
  have hen : ∀ z, z ∈ E ↔ ∃ j : ℕ, j<n ∧ z=e+(j : ℤ)•u := by
    intro z
    simpa [E,n,hi,extremeRow] using henum z
  obtain ⟨k,k',hk,hk',hleft,hright⟩ := balanced_two_determination_rules θ u hu B hB e hen
  change k<n at hk
  change k'<n at hk'
  obtain ⟨hab,x,hx,hagree,z,hzb,hdefect⟩ := hambiguity
  obtain ⟨w,hw⟩ := primitive_height_surjective u hu (b-hi)
  change det u w=b-hi at hw
  obtain ⟨v,hv⟩ := primitive_height_surjective u hu 1
  change det u v=1 at hv
  have hew : det u (e+w)=b := by
    change height u (e+w)=b
    rw [height_add]
    change det u e+det u w=b
    rw [he,hw]
    ring
  obtain ⟨s,hs⟩ := d_row_coordinates u v (e+w) z hv (hzb.trans hew.symm)
  have htopdefect : ∃ s : ℤ, x (e+w+s•u) ≠ θ (e+w+s•u) := by
    exact ⟨s,by simpa only [← hs,θ] using hdefect⟩
  have hlowpoints : ∀ i : ℤ, ∀ z ∈ D, z+w+i•u ∈ latticeStrip u a (b-1) := by
    intro i z hz
    have hzD := Finset.mem_sdiff.mp hz
    have hzlo : lo ≤ det u z := Finset.inf'_le _ hzD.1
    have hzhi : det u z ≤ hi := Finset.le_sup' _ hzD.1
    have hzne : det u z ≠ hi := by
      intro h
      exact hzD.2 (Finset.mem_filter.mpr ⟨hzD.1,by simpa [E,extremeRow] using h⟩)
    change a ≤ height u (z+w+i•u) ∧ height u (z+w+i•u) ≤ b-1
    rw [height_add,height_add,height_zsmul,height_self,mul_zero,add_zero]
    change a ≤ det u z+det u w ∧ det u z+det u w ≤ b-1
    rw [hw]
    have hfit : hi-lo ≤ b-a := hfits
    omega
  have hlowagree : ∀ i : ℤ, ∀ z ∈ D, x (z+w+i•u)=θ (z+w+i•u) := by
    intro i z hz
    exact hagree _ (hlowpoints i z hz)
  have hdis := d_disagreement θ x hx u e w D n k k' hk hk' hleft hright hlowagree htopdefect
  have hpattern_ne : ∀ i : ℤ, pattern x B (w+i•u) ≠ pattern θ B (w+i•u) := by
    intro i hpatt
    apply hdis i
    intro j hj
    have hjn : j<n := by omega
    have hmem : e+(j : ℤ)•u ∈ B := (Finset.mem_filter.mp ((hen _).mpr ⟨j,hjn,rfl⟩)).1
    have hp := congrFun hpatt ⟨e+(j : ℤ)•u,hmem⟩
    simpa only [pattern,add_smul,add_assoc,add_comm,add_left_comm] using hp
  have hcount := d_pattern_count θ x hx B D Finset.sdiff_subset u w
    (by intro i z hz; simpa only [add_assoc,add_comm,add_left_comm] using hlowagree i z hz)
    hpattern_ne
  let Γ := Set.range (fun i : ℤ => pattern θ D (w+i•u))
  have hΓpos : 0 < Γ.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨_,Set.mem_range_self 0⟩
  have hΓbound : Γ.ncard ≤ n-1 := by
    have hg : complexity θ B < complexity θ D+n := hB.strict_growth
    change complexity θ D+Γ.ncard ≤ complexity θ B at hcount
    omega
  have hn : 0<n-1 := by omega
  have hDconvex : LatticeConvex D := delete_extreme_row_convex u B hB.nonempty hB.convex 1 (Or.inl rfl)
  have hDrow : ∀ t : ℤ, t<hi → D.filter (fun z => det u z=t)=B.filter (fun z => det u z=t) := by
    intro t ht
    ext z
    simp only [D,E,extremeRow,ite_true,Finset.mem_filter,Finset.mem_sdiff]
    constructor
    · intro hz; exact ⟨hz.1.1,hz.2⟩
    · intro hz; exact ⟨⟨hz.1,by intro h; have h' : det u z=hi := h.2; omega⟩,hz.2⟩
  have hrowperiod : ∀ t ∈ Finset.Icc (lo+det u w) (b-1), ∃ q : ℤ, 1≤q ∧
      ∀ z, det u z=t → θ (z+q•u)=θ z := by
    intro t ht
    obtain ⟨htlo,hthi⟩ := Finset.mem_Icc.mp ht
    let r := t-det u w
    have hrlo : lo≤r := by dsimp [r]; omega
    have hrhi : r<hi := by dsimp [r]; rw [hw]; omega
    have hrow : n-1 ≤ (D.filter (fun z => det u z=r)).card := by
      rw [hDrow r hrhi]
      exact hB.every_row r hrlo (by omega)
    obtain ⟨q,hq,hperiod⟩ := d_low_row θ u hu D hDconvex w (n-1) hn hΓbound r hrow
    exact ⟨q,hq,by intro z hz; apply hperiod z; dsimp [r]; omega⟩
  obtain ⟨Q,hQ,hinit⟩ := d_common_period θ u (Finset.Icc (lo+det u w) (b-1)) hrowperiod
  have hinitstrip : ∀ z ∈ latticeStrip u (lo+det u w) (b-1), θ (z+Q•u)=θ z := by
    intro z hz
    exact hinit z (Finset.mem_Icc.mpr hz)
  -- Atomic remaining producer: extend these strip periods through finitely many
  -- upper rows using d_upper_row and the two determination rules.
  have hsteps : ∀ N : ℕ, ∃ q : ℤ, 1≤q ∧
      ∀ z ∈ latticeStrip u (lo+det u w) (b+(N : ℤ)-1), θ (z+q•u)=θ z := by
    intro N
    induction N with
    | zero => exact ⟨Q,hQ,by simpa using hinitstrip⟩
    | succ N ih =>
      obtain ⟨q,hq,hprev⟩ := ih
      let R : ℤ := b+N
      let w' : Lattice := w+(N : ℤ)•v
      have hw' : det u w'=det u w+N := by
        change height u (w+(N : ℤ)•v)=height u w+N
        rw [height_add,height_zsmul]
        change det u w+(N : ℤ)*det u v=det u w+N
        rw [hv,mul_one]
      have hplace : ∀ z ∈ D, z+w' ∈ latticeStrip u (lo+det u w) (R-1) := by
        intro z hz
        have hzD := Finset.mem_sdiff.mp hz
        have hzlo : lo≤det u z := Finset.inf'_le _ hzD.1
        have hzhi : det u z≤hi := Finset.le_sup' _ hzD.1
        have hzne : det u z≠hi := by
          intro h
          exact hzD.2 (Finset.mem_filter.mpr ⟨hzD.1,by simpa [E,extremeRow] using h⟩)
        change lo+det u w≤height u (z+w') ∧ height u (z+w')≤R-1
        rw [height_add]
        change lo+det u w≤det u z+det u w' ∧ det u z+det u w'≤R-1
        rw [hw',hw]
        dsimp [R]
        omega
      have hew' : det u (e+w')=R := by
        change height u (e+w')=R
        rw [height_add]
        change det u e+det u w'=R
        rw [he,hw',hw]
        dsimp [R]
        ring
      obtain ⟨q',hq',heq⟩ := d_extend_row θ u hu e w' D n k k' hk hk'
        (lo+det u w) R q hq hplace hew' hleft hright hprev
      have hbN : b+((N+1 : ℕ) : ℤ)-1=R := by dsimp [R]; omega
      exact ⟨q',hq',by rw [hbN]; exact heq⟩
  have hwide : ∃ q : ℤ, 1≤q ∧ ∀ z ∈ latticeStrip u (lo+det u w) (lo+det u w+det u h₂),
      θ (z+q•u)=θ z := by
    let N := (lo+det u w+det u h₂-b+1).toNat
    obtain ⟨q,hq,hperiod⟩ := hsteps N
    refine ⟨q,hq,?_⟩
    intro z hz
    apply hperiod z
    exact ⟨hz.1,by have := hz.2; dsimp [N]; omega⟩
  obtain ⟨q,hq,hwide⟩ := hwide
  refine ⟨q•h₁,?_,?_⟩
  · have hu0 := primitive_ne_zero u hu
    intro hzero
    have hc : q*c₁ ≠ 0 := mul_ne_zero (by omega) (by omega)
    apply hu0
    have hz : (q*c₁)•u=0 := by simpa only [hh₁,smul_smul] using hzero
    exact (smul_eq_zero.mp hz).resolve_left hc
  · exact lemmaD_3 p hp θ₁ θ₂ u h₁ h₂ hu c₁ hc₁ hh₁ hperiod₁ hperiod₂ hΔ
      (lo+det u w) (lo+det u w+det u h₂) q (by omega) hq hwide


end ConvexNivat
