import NivatTrial.TwoComponent

/-! A reference periodic in the first direction has only finitely many
phases on any finite-height transverse band. Repetition of the finite
phase block forces agreement on the entire infinite parallel band. -/

namespace NivatTrial.ColleReferencePhaseRepeat

open NivatTrial.Dynamics NivatTrial.Periodicity
open NivatTrial.LatticeCoordinates NivatTrial.RowDetermination
open NivatTrial.TwoComponent
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ
variable {A : Type*}

/-- One representative for every horizontal phase and every integer height
in the chosen finite interval. -/
def phaseBand (P : ℕ) (b H : ℤ) : Finset G :=
  (Finset.Ico (0:ℤ) (P:ℤ)) ×ˢ (Finset.Icc b H)

theorem phaseBand_representative (P : ℕ) (hP : 0 < P)
    (b H : ℤ) (k : G) (r : ℤ) (z : G)
    (hz : b ≤ (z-r•k).2 ∧ (z-r•k).2 ≤ H) :
    ∃ v ∈ phaseBand P b H, ∃ m : ℤ,
      z = r•k + v + m • (P • horizontal) := by
  let w := z-r•k
  let v : G := (w.1 % (P:ℤ),w.2)
  let m : ℤ := w.1 / (P:ℤ)
  have hPi : (0:ℤ) < P := by exact_mod_cast hP
  have hv : v ∈ phaseBand P b H := by
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_Ico.mpr
      ⟨Int.emod_nonneg _ (ne_of_gt hPi),Int.emod_lt_of_pos _ hPi⟩,
      Finset.mem_Icc.mpr hz⟩
  refine ⟨v,hv,m,?_⟩
  have hid := Int.emod_add_mul_ediv w.1 (P:ℤ)
  ext
  · simp only [Prod.fst_add,Prod.smul_fst,nsmul_horizontal,step,smul_eq_mul]
    dsimp [v,m,w] at *
    nlinarith [hid]
  · simp [v,w,horizontal]

/-- A repeated phase block yields equality on the entire `P`-periodic
horizontal band, rather than only on its finite representative set. -/
theorem periodic_reference_band_agreement
    (q : G → A) (P : ℕ) (hP : 0 < P)
    (hq : IsPeriod q (P • horizontal))
    (b H : ℤ) (k : G) (r s : ℤ)
    (hmatch : patternAt q (phaseBand P b H) (r•k) =
      patternAt q (phaseBand P b H) (s•k)) :
    ∀ z : G, b ≤ (z-r•k).2 → (z-r•k).2 ≤ H →
      q (z+(s-r)•k) = q z := by
  intro z hzlo hzhi
  obtain ⟨v,hv,m,hrep⟩ :=
    phaseBand_representative P hP b H k r z ⟨hzlo,hzhi⟩
  have hblock := congrFun hmatch ⟨v,hv⟩
  have htranslated : z+(s-r)•k = s•k+v+m•(P•horizontal) := by
    rw [hrep]
    simp [sub_smul]
    abel
  have hleft : q z = q (r•k+v) := by
    rw [hrep]
    exact (hq.zsmul m) _
  have hright : q (z+(s-r)•k) = q (s•k+v) := by
    rw [htranslated]
    exact (hq.zsmul m) _
  exact hright.trans (hblock.symm.trans hleft.symm)

variable [Fintype A]

/-- Among at most `P_q(T)` local phases a positive transverse gap recurs
arbitrarily far along the second direction. Its repeated finite pattern
implies agreement on a full infinite horizontal band at each occurrence. -/
theorem recurrent_periodic_reference_band
    (q : G → A) (P : ℕ) (hP : 0 < P)
    (hq : IsPeriod q (P • horizontal))
    (b H : ℤ) (k : G) (_hk : 0 < k.2) :
    ∃ N : ℕ, 0 < N ∧ N ≤ patternComplexity q (phaseBand P b H) ∧
      ∀ R : ℕ, ∃ r : ℕ, R ≤ r ∧
        ∀ z : G, b ≤ (z-(r:ℤ)•k).2 →
          (z-(r:ℤ)•k).2 ≤ H → q (z+(N:ℤ)•k) = q z := by
  let T := phaseBand P b H
  let M := patternComplexity q T
  have hM : 0 < M := by
    have hp : Nonempty (patternSet q T) :=
      ⟨⟨patternAt q T 0,⟨0,rfl⟩⟩⟩
    simpa [M,patternComplexity,Nat.card_eq_fintype_card]
      using Fintype.card_pos_iff.mpr hp
  let F := Finset.Icc 1 M
  have hF : F.Nonempty := ⟨1,Finset.mem_Icc.mpr ⟨le_rfl,hM⟩⟩
  have hsome (R : ℕ) : ∃ N ∈ F, ∃ r : ℕ, R ≤ r ∧
      patternAt q T ((r:ℤ)•k) = patternAt q T (((r+N:ℕ):ℤ)•k) := by
    obtain ⟨i,j,hij,hj,heq⟩ := pigeonhole_patterns q T R k
    let N := j-i
    let r := R+i
    refine ⟨N,Finset.mem_Icc.mpr ⟨by dsimp [N]; omega,by dsimp [N,M]; omega⟩,
      r,by dsimp [r]; omega,?_⟩
    have hsum : r+N = R+j := by dsimp [r,N]; omega
    rw [hsum]
    simpa [r,Nat.cast_add] using heq
  have hfixed : ∃ N ∈ F, ∀ R : ℕ, ∃ r : ℕ, R ≤ r ∧
      patternAt q T ((r:ℤ)•k) = patternAt q T (((r+N:ℕ):ℤ)•k) := by
    by_contra hn
    have hbounded (N : ℕ) (hN : N ∈ F) :
        ∃ R : ℕ, ∀ r : ℕ, R ≤ r →
          patternAt q T ((r:ℤ)•k) ≠ patternAt q T (((r+N:ℕ):ℤ)•k) := by
      have hnot : ¬∀ R : ℕ, ∃ r : ℕ, R ≤ r ∧
          patternAt q T ((r:ℤ)•k) = patternAt q T (((r+N:ℕ):ℤ)•k) := by
        intro h
        exact hn ⟨N,hN,h⟩
      push Not at hnot
      exact hnot
    choose cutoff hcutoff using hbounded
    let cutoff' : ℕ → ℕ := fun N => if h : N ∈ F then cutoff N h else 0
    let R := F.sup cutoff'
    obtain ⟨N,hNF,r,hr,hmatch⟩ := hsome R
    have hNR : cutoff N hNF ≤ R := by
      have hs : cutoff' N ≤ R := Finset.le_sup hNF
      simpa [cutoff',hNF] using hs
    exact hcutoff N hNF r (hNR.trans hr) hmatch
  obtain ⟨N,hNF,hrec⟩ := hfixed
  refine ⟨N,(Finset.mem_Icc.mp hNF).1,(Finset.mem_Icc.mp hNF).2,?_⟩
  intro R
  obtain ⟨r,hr,hmatch⟩ := hrec R
  refine ⟨r,hr,?_⟩
  intro z hzlo hzhi
  have hh := periodic_reference_band_agreement q P hP hq b H k
    (r:ℤ) ((r+N:ℕ):ℤ) hmatch z hzlo hzhi
  simpa only [Nat.cast_add,add_sub_cancel_left] using hh

end
end NivatTrial.ColleReferencePhaseRepeat
