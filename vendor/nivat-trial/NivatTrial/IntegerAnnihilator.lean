import NivatTrial.LaurentAction

/-! Low pattern complexity gives a nonzero integer Laurent annihilator.
The coefficients are obtained over the rationals and genuinely cleared of
denominators, so the later finite-characteristic argument applies. -/

namespace NivatTrial.IntegerAnnihilator

open NivatTrial.LaurentAction
open scoped Classical
noncomputable section

variable {A : Type*} [Fintype A]

def rationalObservation (θ : Lattice → A) (S : Finset Lattice) (w : A → ℤ) :
    (Option S → ℚ) →ₗ[ℚ] (patternSet θ S → ℚ) where
  toFun c p := c none + ∑ s : S, c (some s) * (w (p.val s) : ℚ)
  map_add' c d := by
    funext p
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' r c := by
    funext p
    simp [smul_eq_mul, mul_add, Finset.mul_sum, mul_assoc]

theorem rational_relation (θ : Lattice → A) (S : Finset Lattice) (w : A → ℤ)
    (hlow : patternComplexity θ S ≤ S.card) :
    ∃ d : Option S → ℚ, d ≠ 0 ∧
      ∀ z, d none + ∑ s : S, d (some s) * (w (θ (z+s)) : ℚ) = 0 := by
  let T := rationalObservation θ S w
  have hnot : ¬Function.Injective T := by
    intro hinj
    have hdim := LinearMap.finrank_le_finrank_of_injective hinj
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_option,
      Fintype.card_coe] at hdim
    have hc : Fintype.card (patternSet θ S) ≤ S.card := by
      simpa only [patternComplexity, Nat.card_eq_fintype_card] using hlow
    omega
  obtain ⟨x,y,hxy,hne⟩ := Function.not_injective_iff.mp hnot
  have hzero : T (x-y)=0 := by rw [map_sub,hxy,sub_self]
  refine ⟨x-y,sub_ne_zero.mpr hne,?_⟩
  intro z
  have hp := congrFun hzero ⟨patternAt θ S z,⟨z,rfl⟩⟩
  simpa only [T,rationalObservation,LinearMap.coe_mk,AddHom.coe_mk,patternAt,
    Pi.zero_apply] using hp

/-- A common positive integer clears a finite family of rational coefficients. -/
theorem clear_denominators {ι : Type*} [Fintype ι] (d : ι → ℚ) :
    ∃ D : ℕ, 0<D ∧ ∃ c : ι → ℤ, ∀ i, (c i : ℚ)=(D:ℚ)*d i := by
  let D := ∏ i, (d i).den
  have hD : 0<D := Finset.prod_pos (fun i _ => (d i).den_pos)
  have hex (i : ι) : ∃ c : ℤ, (c:ℚ)=(D:ℚ)*d i := by
    have hi : (d i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    obtain ⟨q,hq⟩ := hi
    refine ⟨(q:ℤ)*(d i).num,?_⟩
    have he : d i * ((d i).den : ℚ) = (d i).num := by
      apply (eq_div_iff (by exact_mod_cast (d i).den_ne_zero)).mp
      exact (Rat.num_div_den (d i)).symm
    push_cast
    rw [hq, Nat.cast_mul]
    rw [← he]
    ring
  choose c hc using hex
  exact ⟨D,hD,c,hc⟩

theorem integer_relation (θ : Lattice → A) (S : Finset Lattice) (w : A → ℤ)
    (hlow : patternComplexity θ S ≤ S.card) :
    ∃ c : S → ℤ, c ≠ 0 ∧ ∃ b : ℤ,
      ∀ z, ∑ s : S, c s * w (θ (z+s)) = b := by
  obtain ⟨d,hd,hrel⟩ := rational_relation θ S w hlow
  obtain ⟨D,hD,c,hc⟩ := clear_denominators d
  have hDq : (D:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  have hcz (z : Lattice) : c none + ∑ s : S, c (some s)*w (θ (z+s))=0 := by
    have hh := congrArg (fun q : ℚ => (D:ℚ)*q) (hrel z)
    have he : (c none:ℚ)+∑ s : S, (c (some s):ℚ)*(w (θ (z+s)):ℚ)=0 := by
      simp only [hc]
      simpa only [mul_add, Finset.mul_sum, mul_assoc, mul_zero] using hh
    exact_mod_cast he
  have hcn : (fun s : S => c (some s)) ≠ 0 := by
    intro hz
    have hs : ∀ s : S, c (some s)=0 := fun s => congrFun hz s
    have hn : c none=0 := by simpa only [hs,zero_mul,Finset.sum_const_zero,add_zero] using hcz 0
    apply hd
    funext i
    have hi : c i=0 := by cases i with | none => exact hn | some s => exact hs s
    have hr : (D:ℚ)*d i=0 := by rw [← hc,hi]; rfl
    exact (mul_eq_zero.mp hr).resolve_left hDq
  refine ⟨fun s => c (some s),hcn,-c none,?_⟩
  intro z
  have hz := hcz z
  change (∑ s : S, c (some s)*w (θ (z+s))) = -c none
  omega

/-- The low-complexity input of Kari--Szabados now produces a real integer
annihilator; no annihilator-existence premise is retained. -/
theorem exists_integer_annihilator (θ : Lattice → A) (S : Finset Lattice)
    (w : A → ℤ) (hlow : patternComplexity θ S ≤ S.card) :
    ∃ f : RingLaurent ℤ, f ≠ 0 ∧ act f (fun z => w (θ z))=0 := by
  obtain ⟨c,hc,b,hrel⟩ := integer_relation θ S w hlow
  let q := windowPolynomial S c
  have hq : q ≠ 0 := windowPolynomial_ne_zero S hc
  have hqa : act q (fun z => w (θ z))=fun _ => b := by
    funext z
    exact (act_windowPolynomial S c _ z).trans (hrel z)
  let d : RingLaurent ℤ := AddMonoidAlgebra.single (1,0) 1 - 1
  have hd : d ≠ 0 := by
    intro hz
    have hz' : (AddMonoidAlgebra.single (1,0) 1 : RingLaurent ℤ) =
        AddMonoidAlgebra.single 0 1 := sub_eq_zero.mp hz
    have he := congrArg (fun f : RingLaurent ℤ => f.coeff (1,0)) hz'
    norm_num [Finsupp.single_apply] at he
  refine ⟨d*q,mul_ne_zero hd hq,?_⟩
  rw [act_mul,hqa]
  funext z
  simp [d,act_sub,act_single]

end
end NivatTrial.IntegerAnnihilator
