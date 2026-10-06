import NivatTrial.ColleAmbiguousFullPatterns

/-! The finite-type space used inside Cyr–Kra's strip induction. Membership
means that every translated `S`-pattern is an actual pattern of `θ`. An
actual hull point belongs to this larger local space. Splicing across an
agreement strip preserves local admissibility, which is the crucial input
for the unique-extension case. -/

namespace NivatTrial.ColleLocalSubshift

open NivatTrial.Dynamics NivatTrial.AmbiguityPropagation
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ

variable {A : Type*} [Fintype A]

def LocalAdmissible (θ : G → A) (S : Finset G) (x : G → A) : Prop :=
  ∀ u : G, patternAt x S u ∈ patternSet θ S

theorem localAdmissible_of_hull {θ x : G → A} {S : Finset G}
    (hx : x ∈ languageHull θ) : LocalAdmissible θ S x := by
  intro u
  exact patternSet_subset_of_mem_languageHull hx S ⟨u,rfl⟩

theorem localAdmissible_shift {θ x : G → A} {S : Finset G}
    (hx : LocalAdmissible θ S x) (u : G) :
    LocalAdmissible θ S (shift u x) := by
  intro v
  have he : patternAt (shift u x) S v = patternAt x S (u+v) := by
    funext s
    simp [patternAt, shift, add_assoc]
  rw [he]
  exact hx (u+v)

theorem generated_determines_local
    (θ : G → A) (S : Finset G) (g : G)
    (hgen : NivatTrial.GeneratingWindows.Generated θ S g)
    {x y : G → A} (hx : LocalAdmissible θ S x)
    (hy : LocalAdmissible θ S y) (u v : G)
    (hbase : patternAt x (S.erase g) u =
      patternAt y (S.erase g) v) :
    x (u+g) = y (v+g) := by
  have hsub : S.erase g ⊆ S := Finset.erase_subset g S
  have hinj := patternRestriction_injective_of_card_eq θ hsub hgen.2
  let px : patternSet θ S := ⟨patternAt x S u, hx u⟩
  let py : patternSet θ S := ⟨patternAt y S v, hy v⟩
  have he : patternRestriction θ hsub px = patternRestriction θ hsub py :=
    Subtype.ext hbase
  have hfull := congrArg Subtype.val (hinj he)
  exact congrFun hfull ⟨g,hgen.1⟩

def spliceAtZero (x y : G → A) (z : G) : A :=
  if z.1 ≤ 0 then x z else y z

theorem localAdmissible_splice
    (θ : G → A) (S : Finset G) (W : ℤ)
    (hS : ∀ s ∈ S, 0 ≤ s.1 ∧ s.1 ≤ W)
    {x y : G → A}
    (hx : LocalAdmissible θ S x)
    (hy : LocalAdmissible θ S y)
    (hxy : ∀ z : G, 0 < z.1 → z.1 ≤ W → x z = y z) :
    LocalAdmissible θ S (spliceAtZero x y) := by
  intro u
  by_cases hall : ∀ s ∈ S, 0 < (u+s).1
  · have he : patternAt (spliceAtZero x y) S u = patternAt y S u := by
      funext s
      have hh := hall s.val s.property
      change spliceAtZero x y (u+s.val) = y (u+s.val)
      simp only [Prod.fst_add] at hh
      simp [spliceAtZero, not_le.mpr hh]
    rw [he]
    exact hy u
  · push Not at hall
    obtain ⟨t, ht, htle⟩ := hall
    have hule : u.1 ≤ 0 := by
      have ht0 := (hS t ht).1
      simp only [Prod.fst_add] at htle
      omega
    have he : patternAt (spliceAtZero x y) S u = patternAt x S u := by
      funext s
      have hsW := (hS s.val s.property).2
      by_cases hleft : (u+s.val).1 ≤ 0
      · change spliceAtZero x y (u+s.val) = x (u+s.val)
        simp only [Prod.fst_add] at hleft
        simp [spliceAtZero, hleft]
      · have hright : 0 < (u+s.val).1 := lt_of_not_ge hleft
        have hbound : (u+s.val).1 ≤ W := by
          simp only [Prod.fst_add]
          omega
        change spliceAtZero x y (u+s.val) = x (u+s.val)
        simp only [Prod.fst_add] at hleft
        simp [spliceAtZero, hleft, hxy (u+s.val) hright hbound]
    rw [he]
    exact hx u

end

end NivatTrial.ColleLocalSubshift
