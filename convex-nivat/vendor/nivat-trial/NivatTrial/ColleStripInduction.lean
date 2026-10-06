import NivatTrial.ColleAmbiguousStrip

/-! One half of the Cyr–Kra/Colle adjacent-strip induction: when each local
base pattern on the next boundary row has a unique actual extension, a
horizontal period on the known side propagates through that entire row. -/

namespace NivatTrial.ColleStripInduction

open NivatTrial.Dynamics NivatTrial.ColleAmbiguity
open NivatTrial.ColleLocalSubshift NivatTrial.BalancedWindows
open NivatTrial.ColleBalancedRows
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ

variable {A : Type*} [Fintype A]

theorem unique_fiber_of_count_lt_two
    {M N : Type*} [Fintype M] [Fintype N]
    (f : M → N) (p q : M) (he : f p = f q)
    (hcount : extensionCount f (f p) < 2) : p = q := by
  by_contra hpq
  have htwo : 2 ≤ extensionCount f (f p) :=
    two_extensions_imply_count rfl he.symm hpq
  omega

theorem unique_extension_propagates_horizontal_period
    (θ : G → A) (B : Finset G) (hB : B.Nonempty)
    {x : G → A} (hx : LocalAdmissible θ B x)
    (d : ℤ) (Q : ℕ)
    (habove : ∀ z : G, d < z.2 →
      x (z+(Q:ℤ) • ((1,0):G)) = x z)
    (hunique : ∀ a : G, a.2 + lower B = d →
      extensionCount (restriction θ B (1,0))
        (restriction θ B (1,0) ⟨patternAt x B a,hx a⟩) < 2) :
    ∀ z : G, z.2 = d →
      x (z+(Q:ℤ) • ((1,0):G)) = x z := by
  obtain ⟨s,hs⟩ := bottomEdge_nonempty hB
  have hsB : s ∈ B := (mem_row B (lower B) s).mp hs |>.1
  have hsrow : s.2 = lower B := (mem_row B (lower B) s).mp hs |>.2
  intro z hz
  let a : G := z-s
  have ha : a.2 + lower B = d := by
    dsimp [a]
    omega
  let a' : G := a+(Q:ℤ) • ((1,0):G)
  let p : patternSet θ B := ⟨patternAt x B a,hx a⟩
  let q : patternSet θ B := ⟨patternAt x B a',hx a'⟩
  have hbase : restriction θ B (1,0) p = restriction θ B (1,0) q := by
    apply Subtype.ext
    funext t
    have ht : t.val ∈ supportBase B (1,0) := t.property
    have htup : lower B < t.val.2 := by
      have hbaseEq := horizontal_supportBase_eq_upperBase B hB
      change supportBase B (1,0) = upperBase B at hbaseEq
      have ht' : t.val ∈ upperBase B := hbaseEq ▸ ht
      rw [upperBase_eq_filter] at ht'
      exact (Finset.mem_filter.mp ht').2
    have hhigh : d < (a+t.val).2 := by
      dsimp [a]
      omega
    have hp := habove (a+t.val) hhigh
    change x (a + t.val) = x (a' + t.val)
    calc
      x (a + t.val) = x ((a + t.val) + (Q:ℤ) • ((1,0):G)) := hp.symm
      _ = x (a' + t.val) := by
        congr 1
        dsimp [a']
        abel
  have hcount : extensionCount (restriction θ B (1,0))
      (restriction θ B (1,0) p) < 2 := by
    simpa [p] using hunique a ha
  have hpq := unique_fiber_of_count_lt_two
    (restriction θ B (1,0)) p q hbase hcount
  have he := congrFun (congrArg Subtype.val hpq) ⟨s,hsB⟩
  have haz : a+s=z := by dsimp [a]; abel
  change x (z + (Q:ℤ) • ((1,0):G)) = x z
  have he' : x (a + s) = x (a' + s) := he
  calc
    x (z + (Q:ℤ) • ((1,0):G)) = x (a' + s) := by
      congr 1
      dsimp [a']
      rw [← haz]
      abel
    _ = x (a+s) := he'.symm
    _ = x z := by rw [haz]

end

end NivatTrial.ColleStripInduction
