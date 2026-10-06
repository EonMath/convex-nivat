import NivatTrial.ColleNonuniqueStrip

/-! Splicing two locally admissible configurations across a horizontal
interface uses agreement on precisely the rows a translated window can
straddle. This is the local-SFT operation in the unique/nonunique
extension dichotomy. -/

namespace NivatTrial.ColleHorizontalSplice

open NivatTrial.Dynamics NivatTrial.BalancedWindows
open NivatTrial.ColleLocalSubshift
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ
variable {A : Type*} [Fintype A]

def spliceAtRow (d : ℤ) (x y : G → A) (z : G) : A :=
  if z.2 ≤ d then y z else x z

theorem localAdmissible_spliceAtRow
    (θ : G → A) (S : Finset G) (d : ℤ)
    {x y : G → A}
    (hx : LocalAdmissible θ S x) (hy : LocalAdmissible θ S y)
    (hxy : ∀ z : G, d < z.2 →
      z.2 ≤ d + upper S - lower S → x z = y z) :
    LocalAdmissible θ S (spliceAtRow d x y) := by
  intro u
  by_cases hall : ∀ s ∈ S, d < (u+s).2
  · have he : patternAt (spliceAtRow d x y) S u = patternAt x S u := by
      funext s
      have hh := hall s.val s.property
      change spliceAtRow d x y (u+s.val) = x (u+s.val)
      unfold spliceAtRow
      split_ifs with hc
      · omega
      · rfl
    rw [he]
    exact hx u
  · push Not at hall
    obtain ⟨t,ht,htle⟩ := hall
    have hule : u.2 + lower S ≤ d := by
      have htlow := lower_le_of_mem ht
      simp only [Prod.snd_add] at htle
      omega
    have he : patternAt (spliceAtRow d x y) S u = patternAt y S u := by
      funext s
      have hsmax := le_upper_of_mem s.property
      by_cases hbelow : (u+s.val).2 ≤ d
      · change spliceAtRow d x y (u+s.val) = y (u+s.val)
        unfold spliceAtRow
        split_ifs
        rfl
      · have habove : d < (u+s.val).2 := lt_of_not_ge hbelow
        have hbound : (u+s.val).2 ≤ d+upper S-lower S := by
          simp only [Prod.snd_add]
          omega
        change spliceAtRow d x y (u+s.val) = y (u+s.val)
        unfold spliceAtRow
        split_ifs
        exact hxy (u+s.val) habove hbound
    rw [he]
    exact hy u

end

end NivatTrial.ColleHorizontalSplice
