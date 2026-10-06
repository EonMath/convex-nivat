import NivatTrial.ColleSeedBlockPropagation

/-! The row induction in Colle's two-directional propagation. A generated
endpoint completes an exposed block of length one less than the edge; the
completed block then determines the whole row from the already matched
interior rows. High matching bands can therefore be propagated downwards. -/

namespace NivatTrial.CollePeriodicRowPropagation

open NivatTrial.Dynamics NivatTrial.BalancedWindows NivatTrial.ColleGenerating
open NivatTrial.ColleVertexGeometry NivatTrial.ColleLocalSubshift
open NivatTrial.ColleSeedBlockPropagation NivatTrial.GeneratingWindows
open scoped Classical
noncomputable section

abbrev G := ℤ × ℤ
variable {A : Type*} [Fintype A]

theorem agree_on_band_of_row_seeds
    (θ : G → A) (B : Finset G) (hB : GeneratingWindow θ B)
    {x y : G → A} (hx : LocalAdmissible θ B x) (hy : LocalAdmissible θ B y)
    (lo top : ℤ)
    (hhigh : ∀ z : G, top≤z.2 → z.2≤top+upper B-lower B → x z=y z)
    (hseeds : ∀ d : ℤ, lo≤d → d<top → ∃ L : ℤ,
      ∀ j : ℤ, L≤j → j<L+((bottomEdge B).card-1 : ℕ) → x (j,d)=y (j,d)) :
    ∀ z : G, lo≤z.2 → z.2≤top+upper B-lower B → x z=y z := by
  have hrows : ∀ n : ℕ, ∀ z : G, lo≤z.2 →
      top-(n:ℤ)≤z.2 → z.2≤top+upper B-lower B → x z=y z := by
    intro n
    induction n with
    | zero =>
      intro z _ hz hzu
      exact hhigh z (by simpa using hz) hzu
    | succ n ih =>
      intro z hzl hz hzu
      by_cases hzold : top-(n:ℤ)≤z.2
      · exact ih z hzl hzold hzu
      · have hzrow : z.2=top-(n:ℤ)-1 := by omega
        obtain ⟨L,hseed⟩ := hseeds z.2 hzl (by omega)
        apply whole_row_of_seed_block θ B hB hx hy z.2 L ?_ ?_ z rfl
        · intro w hwl hwu
          exact ih w (by omega) (by omega) (by omega)
        · intro j hjL hjU
          exact hseed j hjL (by omega)
  intro z hzl hzu
  exact hrows (top-z.2).toNat z hzl (by omega) hzu

theorem agree_on_halfPlane_of_arbitrarily_high_bands
    (θ : G → A) (B : Finset G) (hB : GeneratingWindow θ B)
    {x y : G → A} (hx : LocalAdmissible θ B x) (hy : LocalAdmissible θ B y)
    (lo : ℤ)
    (hhigh : ∀ H : ℤ, ∃ top : ℤ, H≤top ∧
      ∀ z : G, top≤z.2 → z.2≤top+upper B-lower B → x z=y z)
    (hseeds : ∀ d : ℤ, lo≤d → ∃ L : ℤ,
      ∀ j : ℤ, L≤j → j<L+((bottomEdge B).card-1 : ℕ) → x (j,d)=y (j,d)) :
    ∀ z : G, lo≤z.2 → x z=y z := by
  intro z hz
  obtain ⟨top,htop,hband⟩ := hhigh z.2
  have hwidth : 0≤upper B-lower B := sub_nonneg.mpr (lower_le_upper hB.nonempty)
  exact agree_on_band_of_row_seeds θ B hB hx hy lo top hband
    (fun d hd _ => hseeds d hd) z hz (by omega)

end
end NivatTrial.CollePeriodicRowPropagation
