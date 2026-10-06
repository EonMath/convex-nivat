import NivatTrial.ColleActualSecondAmbiguity
import NivatTrial.ColleTopReferencePropagation

/-! The real second-boundary interface yields a high-half-plane period of
the original reference, with the original (possibly nonprimitive) direction. -/

namespace NivatTrial.ColleSecondBoundaryReference

open NivatTrial.Dynamics NivatTrial.Geometry NivatTrial.Zonotope
open NivatTrial.Periodicity NivatTrial.BalancedWindows NivatTrial.RowDetermination
open NivatTrial.ColleGenerating NivatTrial.ColleLeftwardCoordinates
open NivatTrial.ColleActualSecondAmbiguity NivatTrial.ColleParallelogramSeeds
open NivatTrial.ColleTopReferencePropagation
open scoped Classical
noncomputable section
abbrev G := ℤ × ℤ
variable {A : Type*} [Fintype A]

omit [Fintype A] in
theorem high_period_nsmul (p : G → A) (t : G) (lo : ℤ) (ht : 0≤t.2)
    (hper : ∀ z : G, lo≤z.2 → p (z+t)=p z) (N : ℕ) :
    ∀ z : G, lo≤z.2 → p (z+N•t)=p z := by
  induction N with
  | zero => intro z _; simp
  | succ N ih =>
    intro z hz
    have hhigh : lo≤(z+N•t).2 := by
      change lo≤z.2+N•t.2
      rw [nsmul_eq_mul]
      exact hz.trans (le_add_of_nonneg_right (mul_nonneg (by positivity) ht))
    rw [succ_nsmul,← add_assoc,hper (z+N•t) hhigh,ih z hz]

omit [Fintype A] in
theorem high_period_of_shift (p : G → A) (a t : G) (lo : ℤ)
    (hper : ∀ z : G, lo≤z.2 → shift a p (z+t)=shift a p z) :
    ∀ z : G, lo+a.2≤z.2 → p (z+t)=p z := by
  intro z hz
  have hh := hper (z-a) (by change lo≤z.2-a.2; omega)
  have he : a+(z-a+t)=z+t := by abel
  have he' : a+(z-a)=z := by abel
  simpa only [shift_apply,he,he'] using hh

theorem reference_halfPlane_period_of_inner_strips
    (θ : G → A) (S : Finset G) (hS : GeneratingWindow θ S)
    (P : ℕ) (hP : 0<P) {x p : G → A}
    (hx : x ∈ languageHull θ) (hp : p ∈ languageHull θ)
    (hperiod : IsPeriod p (P•horizontal))
    (k : G) (hk : 0<k.2) (c : ℕ) (e : G ≃+ G)
    (hc : 0<c) (hek : e (-(c:ℤ),0)=k)
    (hdet : ∀ z, det k (e z)=(c:ℤ)*z.2)
    (hstrips : ∀ height width : ℤ, ∃ v : G, x (e v)≠p (e v) ∧
      ∀ z : G, v.2<z.2 → z.2≤v.2+height → z.1≤v.1+width →
        x (e z)=p (e z)) :
    ∃ M : ℕ, 0<M ∧ ∃ lo : ℤ, ∀ z : G, lo≤z.2 → p (z+M•k)=p z := by
  let k₀ := e (-1,0)
  obtain ⟨hscale,hprim,hdual⟩ := primitive_second_axis e k c hc hek hdet
  have hk₀ : 0<k₀.2 := by
    have hh := congrArg Prod.snd hscale
    change k.2=(c:ℤ)*k₀.2 at hh
    have hc' : (0:ℤ)<c := by exact_mod_cast hc
    nlinarith
  obtain ⟨a,τ,hsemi⟩ := reference_semiAmbiguous_of_inner_strips θ S hS e k₀ rfl
    hdual hx hp hstrips
  obtain ⟨M,hM,lo,hm⟩ := reference_halfPlane_period_of_semiAmbiguous_unordered θ S hS
    k₀ hprim hk₀ (shift a p) (shift_mem_languageHull hp a) τ hsemi
    P hP (hperiod.shift a)
  have hpM : ∀ z : G, lo+a.2≤z.2 → p (z+M•k₀)=p z := by
    apply high_period_of_shift p a (M•k₀) lo
    simpa only [natCast_zsmul] using hm
  have hMy : 0≤(M•k₀).2 := by
    change (0:ℤ)≤M•k₀.2
    rw [nsmul_eq_mul]
    exact mul_nonneg (by positivity) hk₀.le
  refine ⟨M,hM,lo+a.2,?_⟩
  intro z hz
  have hh := high_period_nsmul p (M•k₀) (lo+a.2) hMy hpM c z hz
  have hck : c•(M•k₀)=M•k := by
    rw [hscale,natCast_zsmul]
    exact smul_comm c M k₀
  simpa only [hck] using hh

end
end NivatTrial.ColleSecondBoundaryReference
