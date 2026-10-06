import NivatTrial.ColleParallelogramSeeds

/-! The shorter top-edge case of Colle's Claim 4.3. The region and the
second direction keep their original orientation. Reflection is used only
to prove the upward row induction, after which the conclusion is stated
on the original upper half-plane. -/

namespace NivatTrial.ColleTopReferencePropagation

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.LatticePolygon
open NivatTrial.Dynamics NivatTrial.Periodicity NivatTrial.BalancedWindows
open NivatTrial.ColleGenerating NivatTrial.ColleAmbiguity
open NivatTrial.ColleSemiAmbiguity NivatTrial.ColleHalfStrip
open NivatTrial.ColleParallelogramGeometry NivatTrial.ColleParallelogramWindow
open NivatTrial.ColleParallelogramSeeds NivatTrial.ColleReferencePhaseRepeat
open NivatTrial.CollePeriodicRowPropagation NivatTrial.ColleLocalSubshift
open NivatTrial.ColleGeneratingTransforms NivatTrial.LatticeCoordinates
open NivatTrial.RowDetermination
open scoped Classical
noncomputable section

variable {A : Type*} [Fintype A]

/-- The same Q construction yields the shorter top-edge length, without
reversing the actual second-direction tail. -/
theorem high_row_top_seeds_of_semiAmbiguous
    (θ : Lattice → A) (S : Finset Lattice) (hS : GeneratingWindow θ S)
    (k : Lattice) (hprim : Int.gcd k.1 k.2 = 1) (hk : 0 < k.2)
    (q : Lattice → A) (hq : q ∈ languageHull θ) (τ : ℤ)
    (hamb : SemiAmbiguous θ S (embed k) k q hq τ)
    (hshort : (topEdge S).card ≤ (bottomEdge S).card) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ lo : ℤ,
      ∀ d : ℤ, lo ≤ d → ∃ l : ℤ, ∀ N : ℕ,
        ∀ j : ℤ, l ≤ j → j < l+((topEdge S).card-1 : ℕ) →
          q ((j,d)+(N : ℤ)•(Q•k)) = q (j,d) := by
  let L := (topEdge S).card-1
  have htop : L < (topEdge S).card := by
    have hh := Finset.card_pos.mpr (topEdge_nonempty hS.nonempty)
    dsimp [L]
    omega
  have hbot : L < (bottomEdge S).card := htop.trans_le hshort
  have hbudget := hS.strict_edge_budget (embed k)
  have hedge := supportEdge_card_two_of_semiAmbiguous θ S k q hq τ hamb hbudget
  obtain ⟨a,hrun,hrows⟩ := exists_cellAnchors_of_support_edge S hS.nonempty
    hS.latticeConvex k hprim hk L hbot htop hedge
  obtain ⟨T,Q,hQ,hper⟩ := common_semi_ambiguous_halfStrip_period θ S (embed k) k
    (cellAnchors S a k L) ((supportEdge S (embed k)).card-1) τ hq hamb
    hbudget hrun le_rfl
  let M : ℕ := (τ+(T : ℤ)).toNat
  have hM : τ+(T : ℤ) ≤ (M : ℤ) := by dsimp [M]; omega
  refine ⟨Q,hQ,a.2+(M : ℤ)*k.2,?_⟩
  intro d hd
  obtain ⟨l,n,hn,hseed⟩ := hrows M d hd
  refine ⟨l,?_⟩
  intro N j hjlo hjhi
  let j' : Fin L := ⟨(j-l).toNat,by dsimp [L]; omega⟩
  obtain ⟨w,hw,he⟩ := hseed j'
  have hj : l+(j' : ℤ) = j := by dsimp [j']; omega
  rw [hj] at he
  have hp : TailPeriod (fun i : ℤ => q (w+i•k)) (τ+(T : ℤ)) Q := hper w hw
  have hm := hp.nsmul N n (hM.trans hn)
  change q (w+(n+((N*Q : ℕ) : ℤ))•k) = q (w+n•k) at hm
  have heq : (w+n•k)+(N : ℤ)•(Q•k) = w+(n+((N*Q : ℕ) : ℤ))•k := by
    rw [← natCast_zsmul,smul_smul,Nat.cast_mul,add_smul]
    abel
  rw [he,heq]
  exact hm

/-- A matching finite-height band and top-edge seeds propagate upwards
on the original lattice. Reflection here is internal to the induction. -/
theorem agree_on_upper_halfPlane_of_band_and_top_seeds
    (θ : Lattice → A) (S : Finset Lattice) (hS : GeneratingWindow θ S)
    {x y : Lattice → A} (hx : x ∈ languageHull θ) (hy : y ∈ languageHull θ)
    (bot : ℤ)
    (hband : ∀ z : Lattice, bot ≤ z.2 → z.2 ≤ bot+upper S-lower S → x z=y z)
    (hseeds : ∀ d : ℤ, bot ≤ d → ∃ l : ℤ,
      ∀ j : ℤ, l ≤ j → j < l+((topEdge S).card-1 : ℕ) → x (j,d)=y (j,d)) :
    ∀ z : Lattice, bot ≤ z.2 → x z=y z := by
  let S' := mapWindow reflectY S
  have hS' : GeneratingWindow (θ ∘ reflectY) S' :=
    ColleGeneratingTransforms.GeneratingWindow.reflectY hS
  have hx' : LocalAdmissible (θ ∘ reflectY) S' (x ∘ reflectY) :=
    localAdmissible_of_hull (mem_languageHull_reflectY hx)
  have hy' : LocalAdmissible (θ ∘ reflectY) S' (y ∘ reflectY) :=
    localAdmissible_of_hull (mem_languageHull_reflectY hy)
  have hlower : lower S' = -upper S := lower_reflectY hS.nonempty
  have hupper : upper S' = -lower S := upper_reflectY hS.nonempty
  have hcard : (bottomEdge S').card = (topEdge S).card := by
    rw [show S' = mapWindow reflectY S from rfl,
      bottomEdge_reflectY hS.nonempty,card_mapWindow]
  let top : ℤ := -bot-upper S+lower S
  have hhigh : ∀ w : Lattice, top ≤ w.2 →
      w.2 ≤ top+upper S'-lower S' →
        (x ∘ reflectY) w = (y ∘ reflectY) w := by
    intro w hwl hwu
    apply hband (reflectY w)
    · change bot ≤ -w.2
      rw [hupper,hlower] at hwu
      dsimp [top] at *
      omega
    · change -w.2 ≤ bot+upper S-lower S
      dsimp [top] at hwl
      omega
  intro z hz
  have hseed : ∀ d : ℤ, -z.2 ≤ d → d < top → ∃ l : ℤ,
      ∀ j : ℤ, l ≤ j → j < l+((bottomEdge S').card-1 : ℕ) →
        (x ∘ reflectY) (j,d) = (y ∘ reflectY) (j,d) := by
    intro d _ hd
    have hwidth := lower_le_upper hS.nonempty
    obtain ⟨l,hl⟩ := hseeds (-d) (by dsimp [top] at hd; omega)
    refine ⟨l,?_⟩
    intro j hjl hjh
    exact hl j hjl (by simpa only [hcard] using hjh)
  have hh := agree_on_band_of_row_seeds (θ ∘ reflectY) S' hS' hx' hy'
    (-z.2) top hhigh hseed (reflectY z) (by simp) (by
      change -z.2 ≤ top+upper S'-lower S'
      rw [hupper,hlower]
      dsimp [top]
      omega)
  simpa [Function.comp_def] using hh

/-- A single repeated band above the seed threshold suffices when the top
edge is shorter: generated rows are added upwards indefinitely. -/
theorem reference_upper_period_of_top_seeds
    (θ : Lattice → A) (S : Finset Lattice) (hS : GeneratingWindow θ S)
    (q : Lattice → A) (hq : q ∈ languageHull θ)
    (P : ℕ) (hP : 0 < P) (hperiod : IsPeriod q (P•horizontal))
    (k : Lattice) (hk : 0 < k.2) (lo : ℤ)
    (hseeds : ∀ d : ℤ, lo ≤ d → ∃ l : ℤ, ∀ N : ℕ,
      ∀ j : ℤ, l ≤ j → j < l+((topEdge S).card-1 : ℕ) →
        q ((j,d)+(N : ℤ)•k) = q (j,d)) :
    ∃ N : ℕ, 0 < N ∧ ∃ bot : ℤ, ∀ z : Lattice, bot ≤ z.2 →
      q (z+(N : ℤ)•k) = q z := by
  let H := upper S-lower S
  obtain ⟨N,hN,_,hrec⟩ := recurrent_periodic_reference_band q P hP hperiod 0 H k hk
  obtain ⟨R,hR⟩ := exists_nat_gt lo
  obtain ⟨r,hr,hband⟩ := hrec R
  let bot : ℤ := (r : ℤ)*k.2
  have hr0 : (0 : ℤ) ≤ r := by positivity
  have hRr : (R : ℤ) ≤ r := by exact_mod_cast hr
  have hlobot : lo ≤ bot := by dsimp [bot]; nlinarith
  let y := shift ((N : ℤ)•k) q
  have hy : y ∈ languageHull θ := shift_mem_languageHull hq _
  have hband' : ∀ z : Lattice, bot ≤ z.2 → z.2 ≤ bot+upper S-lower S → q z=y z := by
    intro z hzl hzu
    have hh := hband z (by change 0 ≤ z.2-(r : ℤ)*k.2; dsimp [bot] at hzl; omega)
      (by change z.2-(r : ℤ)*k.2 ≤ H; dsimp [H,bot] at *; omega)
    simpa only [y,shift_apply,add_comm] using hh.symm
  have hseed' : ∀ d : ℤ, bot ≤ d → ∃ l : ℤ,
      ∀ j : ℤ, l ≤ j → j < l+((topEdge S).card-1 : ℕ) → q (j,d)=y (j,d) := by
    intro d hd
    obtain ⟨l,hl⟩ := hseeds d (hlobot.trans hd)
    refine ⟨l,?_⟩
    intro j hjl hjh
    simpa only [y,shift_apply,add_comm] using (hl N j hjl hjh).symm
  have hall := agree_on_upper_halfPlane_of_band_and_top_seeds θ S hS hq hy bot hband' hseed'
  refine ⟨N,hN,bot,?_⟩
  intro z hz
  simpa only [y,shift_apply,add_comm] using (hall z hz).symm

theorem reference_halfPlane_period_of_top_semiAmbiguous
    (θ : Lattice → A) (S : Finset Lattice) (hS : GeneratingWindow θ S)
    (k : Lattice) (hprim : Int.gcd k.1 k.2 = 1) (hk : 0 < k.2)
    (q : Lattice → A) (hq : q ∈ languageHull θ) (τ : ℤ)
    (hamb : SemiAmbiguous θ S (embed k) k q hq τ)
    (hshort : (topEdge S).card ≤ (bottomEdge S).card)
    (P : ℕ) (hP : 0 < P) (hperiod : IsPeriod q (P•horizontal)) :
    ∃ M : ℕ, 0 < M ∧ ∃ lo : ℤ, ∀ z : Lattice, lo ≤ z.2 →
      q (z+(M : ℤ)•k) = q z := by
  obtain ⟨Q,hQ,lo,hseed⟩ := high_row_top_seeds_of_semiAmbiguous θ S hS k hprim hk q hq τ hamb hshort
  have hkQ : 0 < (Q•k).2 := by
    change (0 : ℤ) < Q • k.2
    rw [nsmul_eq_mul]
    exact mul_pos (by exact_mod_cast hQ) hk
  obtain ⟨N,hN,bot,hper⟩ := reference_upper_period_of_top_seeds θ S hS q hq P hP hperiod
    (Q•k) hkQ lo hseed
  refine ⟨N*Q,Nat.mul_pos hN hQ,bot,?_⟩
  intro z hz
  simpa only [← natCast_zsmul,smul_smul,Nat.cast_mul] using hper z hz

/-- No ordering of the two first-direction edge lengths is assumed. Both
cases yield a period on an upper half-plane in the original coordinates. -/
theorem reference_halfPlane_period_of_semiAmbiguous_unordered
    (θ : Lattice → A) (S : Finset Lattice) (hS : GeneratingWindow θ S)
    (k : Lattice) (hprim : Int.gcd k.1 k.2 = 1) (hk : 0 < k.2)
    (q : Lattice → A) (hq : q ∈ languageHull θ) (τ : ℤ)
    (hamb : SemiAmbiguous θ S (embed k) k q hq τ)
    (P : ℕ) (hP : 0 < P) (hperiod : IsPeriod q (P•horizontal)) :
    ∃ M : ℕ, 0 < M ∧ ∃ lo : ℤ, ∀ z : Lattice, lo ≤ z.2 →
      q (z+(M : ℤ)•k) = q z := by
  rcases le_total (bottomEdge S).card (topEdge S).card with hshort | hshort
  · exact reference_halfPlane_period_of_semiAmbiguous θ S hS k hprim hk q hq τ hamb
      hshort P hP hperiod
  · exact reference_halfPlane_period_of_top_semiAmbiguous θ S hS k hprim hk q hq τ hamb
      hshort P hP hperiod

end
end NivatTrial.ColleTopReferencePropagation
