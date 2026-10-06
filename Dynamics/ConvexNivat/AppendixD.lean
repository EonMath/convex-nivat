import ConvexNivat.AppendixPropagation
namespace ConvexNivat
private theorem d_primitive_factor (h : Lattice) (hh : h ≠ 0) :
    ∃ u : Lattice, ∃ c : ℤ, Primitive u ∧ 1≤c ∧ h=c•u := by
  have hg : 0<Int.gcd h.1 h.2 := by
    apply Nat.pos_of_ne_zero
    intro hg
    have hzero := Int.gcd_eq_zero_iff.mp hg
    exact hh (Prod.ext hzero.1 hzero.2)
  obtain ⟨a,b,hab,ha,hb⟩ := Int.exists_gcd_one hg
  refine ⟨(a,b),Int.gcd h.1 h.2,hab,by omega,?_⟩
  ext
  · simpa only [Prod.smul_fst,smul_eq_mul,mul_comm] using ha
  · simpa only [Prod.smul_snd,smul_eq_mul,mul_comm] using hb
private def d_reps (u v : Lattice) (c Δ : ℤ) : Finset Lattice :=
  ((Finset.range c.toNat).product (Finset.range Δ.toNat)).image
    (fun ij : ℕ×ℕ => (ij.1 : ℤ)•u+(ij.2 : ℤ)•v)
private theorem d_strip_reps (u v h₁ h₂ : Lattice) (c Δ : ℤ)
    (hc : 1≤c) (hΔ : 0<Δ) (hv : det u v=1) (hh₁ : h₁=c•u) (hh₂ : det u h₂=Δ)
    (j : ℤ) (z : Lattice) (hz : j*Δ≤det u z ∧ det u z≤(j+1)*Δ-1) :
    ∃ d ∈ d_reps u v c Δ, ∃ r : ℤ, z=d+j•h₂+r•h₁ := by
  let w := z-j•h₂
  let t := det u w
  let s := det w v
  have ht : 0≤t ∧ t<Δ := by
    have he : det u w=det u z-j*Δ := by
      have hdet : det u (z-j•h₂)=det u z-j*det u h₂ := by
        simp [det]
        ring
      simpa only [hh₂] using hdet
    dsimp only [t]
    rw [he]
    constructor <;> nlinarith [hz.1,hz.2]
  have hrem : 0 ≤ s%c ∧ s%c < c := ⟨Int.emod_nonneg s (by omega),Int.emod_lt_of_pos s (by omega)⟩
  let d : Lattice := (s%c)•u+t•v
  have hd : d ∈ d_reps u v c Δ := by
    apply Finset.mem_image.mpr
    refine ⟨((s%c).toNat,t.toNat),Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
    · apply Finset.mem_range.mpr
      omega
    · apply Finset.mem_range.mpr
      omega
    · dsimp [d]
      rw [Int.toNat_of_nonneg hrem.1,Int.toNat_of_nonneg ht.1]
  have hb : w=s•u+t•v := by
    have he : det u v•w=det w v•u+det u w•v := by
      ext <;> simp [det] <;> ring
    simpa only [hv,one_smul] using he
  refine ⟨d,hd,s/c,?_⟩
  have hdiv := Int.emod_add_mul_ediv s c
  calc
    z = w+j•h₂ := by dsimp [w]; abel
    _ = s•u+t•v+j•h₂ := by rw [hb]
    _ = d+j•h₂+(s/c)•h₁ := by
      dsimp [d]
      rw [hh₁,smul_smul,mul_comm (s/c) c]
      conv_lhs => rw [← hdiv,add_smul]
      abel
private theorem d_upper_agreement (p : ℕ) (hp : p.Prime) (θ₁ θ₂ : Configuration (ZMod p))
    (u h₁ h₂ : Lattice) (hu : Primitive u) (c₁ : ℤ) (hc₁ : 1≤c₁)
    (hh₁ : h₁=c₁•u) (hp₁ : HasPeriod θ₁ h₁) (hp₂ : HasPeriod θ₂ h₂)
    (hΔ : 0<det u h₂) (B : Finset Lattice)
    (hB : BalancedSet (fun z => θ₁ z+θ₂ z) u 1 B)
    (hnp : ¬ Periodic (fun z => θ₁ z+θ₂ z))
    (x : Configuration (ZMod p)) (hx : x ∈ OrbitClosure (fun z => θ₁ z+θ₂ z))
    (a b : ℤ) (hwidth : rowHeight u B hB.nonempty ≤ b-a)
    (hagrees : AgreesOn x (fun z => θ₁ z+θ₂ z) (latticeStrip u a b)) :
    AgreesOn x (fun z => θ₁ z+θ₂ z) (upperHalf u a) := by
  have hheight : 0≤rowHeight u B hB.nonempty := by
    obtain ⟨z,hz⟩ := hB.nonempty
    have hmin : rowMinimum u B hB.nonempty ≤ det u z := Finset.inf'_le _ hz
    have hmax : det u z ≤ rowMaximum u B hB.nonempty := Finset.le_sup' _ hz
    exact sub_nonneg.mpr (hmin.trans hmax)
  have hab : a≤b := by omega
  have hsteps : ∀ n : ℕ, AgreesOn x (fun z => θ₁ z+θ₂ z) (latticeStrip u a (b+n)) := by
    intro n
    induction n with
    | zero => simpa using hagrees
    | succ n ih =>
      intro z hz
      by_cases hprev : det u z≤b+n
      · exact ih z ⟨hz.1,hprev⟩
      · have hrow : det u z=b+n+1 := by have := hz.2; omega
        by_contra hdiff
        apply hnp
        apply lemmaD_7 p hp θ₁ θ₂ u h₁ h₂ hu c₁ hc₁ hh₁ hp₁ hp₂ hΔ B hB
          a (b+n+1)
        · refine ⟨by omega,x,hx,?_,z,hrow,hdiff⟩
          have heq : b+(n : ℤ)+1-1=b+n := by ring
          rwa [heq]
        · omega
  intro z hz
  have he := hsteps (det u z-b).toNat
  apply he z
  exact ⟨hz,by omega⟩

private theorem d_main_positive (p : ℕ) (hp : p.Prime) (θ₁ θ₂ : Configuration (ZMod p))
    (u h₁ h₂ : Lattice) (hu : Primitive u) (c : ℤ) (hc : 1≤c)
    (hh₁ : h₁=c•u) (hp₁ : HasPeriod θ₁ h₁) (hp₂ : HasPeriod θ₂ h₂)
    (hΔ : 0<det u h₂) (B : Finset Lattice)
    (hB : BalancedSet (fun z => θ₁ z+θ₂ z) u 1 B)
    (hwide : rowHeight u B hB.nonempty + 1 ≤ det u h₂) :
    Periodic (fun z => θ₁ z+θ₂ z) := by
  classical
  let : NeZero p := ⟨hp.ne_zero⟩
  let θ : Configuration (ZMod p) := fun z => θ₁ z+θ₂ z
  by_contra hnp
  obtain ⟨v,hv⟩ := primitive_height_surjective u hu 1
  change det u v=1 at hv
  let Δ := det u h₂
  let D := d_reps u v c Δ
  let N := complexity θ D
  have hpattfinite : (patternSet θ D).Finite := patternSet_finite θ D
  have hperiod_ne : ¬ HasPeriod θ ((N.factorial : ℤ)•h₂) := by
    intro hperiod
    apply hnp
    refine ⟨(N.factorial : ℤ)•h₂,?_,hperiod⟩
    have hh₂ : h₂≠0 := by intro h; simp [h,det] at hΔ
    have hfac : (N.factorial : ℤ)≠0 := by exact_mod_cast Nat.factorial_ne_zero N
    exact smul_ne_zero hfac hh₂
  obtain ⟨z₀,hz₀⟩ : ∃ z₀, θ (z₀+(N.factorial : ℤ)•h₂)≠θ z₀ := by
    simpa only [HasPeriod,not_forall] using hperiod_ne
  let k : ℤ := det u z₀ / Δ - N
  let f : Fin (N+1) → patternSet θ D := fun j =>
    ⟨pattern θ D ((k+(j.val : ℤ))•h₂),Set.mem_range_self _⟩
  let : Fintype (patternSet θ D) := Fintype.ofFinite _
  have hcard : Fintype.card (patternSet θ D)=N := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    rfl
  have hpair : ∃ i j : Fin (N+1), i<j ∧ f i=f j := by
    obtain ⟨i,j,hij,heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by rw [hcard,Fintype.card_fin]; omega)
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i,j,h,heq⟩
    · exact ⟨j,i,h,heq.symm⟩
  obtain ⟨i,j,hij,heq⟩ := hpair
  let d : ℕ := j.val-i.val
  have hd : 0<d := by dsimp [d]; exact Nat.sub_pos_of_lt hij
  have hdN : d≤N := by dsimp [d]; have := j.isLt; omega
  have hdi : (d : ℤ)+i.val=j.val := by dsimp [d]; omega
  let F : Set Lattice := {z | ∃ r ∈ D, z=r+(k+i.val)•h₂}
  have hF : AgreesOn (translate ((d : ℤ)•h₂) θ) θ F := by
    rintro z ⟨r,hr,rfl⟩
    have he := congrFun (congrArg Subtype.val heq) ⟨r,hr⟩
    have hpoint : r+(k+i.val)•h₂+(d : ℤ)•h₂=(k+j.val)•h₂+r := by
      rw [add_assoc,← add_smul]
      have hi : (k+i.val)+(d : ℤ)=k+j.val := by omega
      rw [hi]
      abel
    change θ (r+(k+i.val)•h₂+(d : ℤ)•h₂)=θ (r+(k+i.val)•h₂)
    rw [hpoint]
    simpa only [f,pattern,add_comm] using he.symm
  have hstrip : AgreesOn (translate ((d : ℤ)•h₂) θ) θ
      (latticeStrip u ((k+i.val)*Δ) ((k+i.val+1)*Δ-1)) := by
    intro z hz
    obtain ⟨r,hr,t,rfl⟩ := d_strip_reps u v h₁ h₂ c Δ hc hΔ hv hh₁ rfl (k+i.val) z hz
    exact appendixD_agreement_saturates θ₁ θ₂ h₁ h₂ hp₁ hp₂ d F hF
      (r+(k+i.val)•h₂) ⟨r,hr,rfl⟩ t
  have hupper := d_upper_agreement p hp θ₁ θ₂ u h₁ h₂ hu c hc hh₁ hp₁ hp₂ hΔ B hB hnp
    (translate ((d : ℤ)•h₂) θ) (orbitClosure_translate θ ((d : ℤ)•h₂))
    ((k+i.val)*Δ) ((k+i.val+1)*Δ-1) (by dsimp [Δ] at *; nlinarith) hstrip
  have hrepeat : ∀ m : ℕ, ∀ z ∈ upperHalf u ((k+i.val)*Δ),
      θ (z+(m : ℤ)•((d : ℤ)•h₂))=θ z := by
    intro m
    induction m with
    | zero => intro z hz; simp
    | succ m ih =>
      intro z hz
      have hz' : z+(m : ℤ)•((d : ℤ)•h₂) ∈ upperHalf u ((k+i.val)*Δ) := by
        change (k+i.val)*Δ≤height u (z+(m : ℤ)•((d : ℤ)•h₂))
        rw [height_add,height_zsmul,height_zsmul]
        change (k+i.val)*Δ≤det u z+(m : ℤ)*((d : ℤ)*Δ)
        have hm : (0 : ℤ) ≤ m := by omega
        have hd' : (0 : ℤ) ≤ d := by omega
        have hpos : 0 ≤ (m : ℤ)*((d : ℤ)*Δ) := mul_nonneg hm (mul_nonneg hd' hΔ.le)
        exact le_trans hz (by omega)
      calc
        θ (z+((m+1 : ℕ) : ℤ)•((d : ℤ)•h₂))=θ ((z+(m : ℤ)•((d : ℤ)•h₂))+(d : ℤ)•h₂) := by
          simp only [Nat.cast_add,Nat.cast_one,add_smul,one_smul,add_assoc]
        _=θ (z+(m : ℤ)•((d : ℤ)•h₂)) := hupper _ hz'
        _=θ z := ih z hz
  obtain ⟨M,hM⟩ := Nat.dvd_factorial hd hdN
  have hzupper : z₀ ∈ upperHalf u ((k+i.val)*Δ) := by
    have hiN : (i.val : ℤ)≤N := by have := i.isLt; omega
    have hdiv := Int.emod_add_mul_ediv (det u z₀) Δ
    have hrem := Int.emod_nonneg (det u z₀) (ne_of_gt hΔ)
    have hmul := mul_le_mul_of_nonneg_right hiN hΔ.le
    change (k+i.val)*Δ≤det u z₀
    dsimp [k]
    nlinarith
  have he := hrepeat M z₀ hzupper
  apply hz₀
  simpa only [smul_smul,← Nat.cast_mul,mul_comm M d,← hM] using he
private theorem d_det_neg (u z : Lattice) : det (-u) z= -det u z := by
  simp [det]
  ring
private theorem d_neg_rows (u : Lattice) (B : Finset Lattice) (hB : B.Nonempty) :
    rowMinimum (-u) B hB= -rowMaximum u B hB ∧
    rowMaximum (-u) B hB= -rowMinimum u B hB := by
  constructor
  · apply le_antisymm
    · obtain ⟨z,hz,he⟩ := Finset.exists_mem_eq_sup' hB (det u)
      have hle : rowMinimum (-u) B hB≤det (-u) z := Finset.inf'_le _ hz
      rw [d_det_neg,← he] at hle
      exact hle
    · apply Finset.le_inf'
      intro z hz
      rw [d_det_neg,neg_le_neg_iff]
      exact Finset.le_sup' _ hz
  · apply le_antisymm
    · apply Finset.sup'_le
      intro z hz
      rw [d_det_neg,neg_le_neg_iff]
      exact Finset.inf'_le _ hz
    · obtain ⟨z,hz,he⟩ := Finset.exists_mem_eq_inf' hB (det u)
      have hle : det (-u) z≤rowMaximum (-u) B hB := Finset.le_sup' _ hz
      rw [d_det_neg,← he] at hle
      exact hle
private theorem d_balanced_reverse {A : Type*} (θ : Configuration A)
    (u : Lattice) (B : Finset Lattice) (hB : BalancedSet θ u (-1) B) :
    BalancedSet θ (-u) 1 B := by
  have hrows := d_neg_rows u B hB.nonempty
  have hextreme : extremeRow 1 (-u) B hB.nonempty=extremeRow (-1) u B hB.nonempty := by
    ext z
    simp only [extremeRow,Finset.mem_filter,d_det_neg,hrows.2]
    simp
  refine ⟨hB.nonempty,hB.convex,Or.inl rfl,hB.low_complexity,?_,?_⟩
  · rw [hextreme]
    exact hB.strict_growth
  · intro t htmin htmax
    rw [hextreme]
    have ht := hB.every_row (-t) (by rw [hrows.1] at htmin; omega)
      (by rw [hrows.2] at htmax; omega)
    have hfilter : B.filter (fun z => det (-u) z=t)=B.filter (fun z => det u z= -t) := by
      ext z
      simp only [Finset.mem_filter,d_det_neg,neg_eq_iff_eq_neg]
    rwa [hfilter]
private theorem d_positive_transverse {A : Type*} (θ : Configuration A)
    (u h : Lattice) (hp : HasPeriod θ h) (hne : det u h≠0) :
    ∃ g : Lattice, HasPeriod θ g ∧ 0<det u g := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine ⟨-h,hasPeriod_neg θ h hp,?_⟩
    have he : det u (-h)= -det u h := by simp [det]; ring
    rw [he]
    omega
  · exact ⟨h,hp,hpos⟩

open scoped BigOperators

/-- D.1: exact finite-field convex two-component theorem. -/
theorem theoremD_1 (p : ℕ) (hp : p.Prime) (θ₁ θ₂ : Configuration (ZMod p))
    (h₁ h₂ : Lattice) (hh₁ : h₁ ≠ 0) (hh₂ : h₂ ≠ 0)
    (hperiod₁ : HasPeriod θ₁ h₁) (hperiod₂ : HasPeriod θ₂ h₂)
    (hindependent : Nonparallel h₁ h₂) (S : Finset Lattice)
    (hS : S.Nonempty) (hconvex : LatticeConvex S)
    (hlow : complexity (fun z => θ₁ z + θ₂ z) S ≤ S.card) :
    Periodic (fun z => θ₁ z + θ₂ z)  := by
  classical
  let : NeZero p := ⟨hp.ne_zero⟩
  let θ : Configuration (ZMod p) := fun z => θ₁ z+θ₂ z
  obtain ⟨u,c,hu,hc,hh₁u⟩ := d_primitive_factor h₁ hh₁
  have hne : det u h₂ ≠ 0 := by
    intro h
    apply hindependent
    have he : det h₁ h₂=c*det u h₂ := by rw [hh₁u]; simp [det]; ring
    rw [he,h,mul_zero]
  obtain ⟨σ,B,hBsub,hB⟩ := lemmaD_5 θ u hu S hS hconvex hlow
  have hfinish : ∀ (u h : Lattice), Primitive u → h=c•u → HasPeriod θ₁ h →
      det u h₂ ≠ 0 → BalancedSet θ u 1 B → Periodic θ := by
    intro u h hu hh hperiod hne hbalanced
    obtain ⟨g,hg,hgpos⟩ := d_positive_transverse θ₂ u h₂ hperiod₂ hne
    let H := rowHeight u B hbalanced.nonempty
    have hH : 0 ≤ H := by
      obtain ⟨z,hz⟩ := hbalanced.nonempty
      have hlo : rowMinimum u B hbalanced.nonempty≤det u z := Finset.inf'_le _ hz
      have hhi : det u z≤rowMaximum u B hbalanced.nonempty := Finset.le_sup' _ hz
      exact sub_nonneg.mpr (hlo.trans hhi)
    let g' := (H+1)•g
    have hp' : HasPeriod θ₂ g' := hasPeriod_zsmul θ₂ g hg (H+1)
    have hdet : det u g'=(H+1)*det u g := by
      change height u ((H+1)•g)=(H+1)*height u g
      exact height_zsmul u g (H+1)
    have hg'pos : 0 < det u g' := by rw [hdet]; exact mul_pos (by omega) hgpos
    have hg'wide : H+1 ≤ det u g' := by rw [hdet]; nlinarith
    exact d_main_positive p hp θ₁ θ₂ u h g' hu c hc hh hperiod hp' hg'pos B hbalanced hg'wide
  rcases hB.sign with rfl | rfl
  · exact hfinish u h₁ hu hh₁u hperiod₁ hne hB
  · have hu' : Primitive (-u) := by simpa [Primitive] using hu
    have hh' : -h₁=c•(-u) := by rw [hh₁u,smul_neg]
    have hne' : det (-u) h₂ ≠ 0 := by rw [d_det_neg]; exact neg_ne_zero.mpr hne
    exact hfinish (-u) (-h₁) hu' hh' (hasPeriod_neg θ₁ h₁ hperiod₁) hne'
      (d_balanced_reverse θ u B hB)


/-- D.2: all smaller decompositions excluded by MinimalPeriodicOrder. -/
theorem corollaryD_2 (p : ℕ) (hp : p.Prime) (η : Configuration (ZMod p))
    (hminimal : MinimalPeriodicOrder (ZMod p) η 2) :
    ¬ LowConvexComplexity η := by
  classical
  intro hlow
  obtain ⟨S,hS,hconvex,hlow⟩ := hlow
  obtain ⟨D⟩ := hminimal.1
  have heq : η = fun z => D.field 0 z + D.field 1 z := by
    funext z
    simpa only [Fin.sum_univ_two] using D.sum_eq z
  have hpη : Periodic η := by
    by_cases hind : Nonparallel (D.period 0) (D.period 1)
    · rw [heq]
      apply theoremD_1 p hp (D.field 0) (D.field 1) (D.period 0) (D.period 1)
        (D.period_nonzero 0) (D.period_nonzero 1) (D.has_period 0) (D.has_period 1)
        hind S hS hconvex
      simpa only [← heq] using hlow
    · have hparallel : det (D.period 0) (D.period 1) = 0 := by
        exact not_ne_iff.mp hind
      obtain ⟨q,hq,hdir,hperiod⟩ := parallel_periodic_sum (D.field 0) (D.field 1)
        (D.period 0) (D.period 1) (D.period_nonzero 0) (D.period_nonzero 1)
        hparallel (D.has_period 0) (D.has_period 1)
      exact ⟨q,hq,by simpa only [heq] using hperiod⟩
  obtain ⟨q,hq,hperiod⟩ := hpη
  have hone : HasPeriodicDecomposition (ZMod p) η 1 := by
    exact ⟨{
      field := fun _ => η
      period := fun _ => q
      period_nonzero := fun _ => hq
      has_period := fun _ => hperiod
      sum_eq := fun z => by simp
    }⟩
  have horder := hminimal.2 1 hone
  omega

end ConvexNivat
