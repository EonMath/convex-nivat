import NivatTrial.ColleRationalDirections

/-! Integral coordinates preserve the actual decomposition, minimal-order
hull condition, and the regional conclusion. This permits the horizontal
construction to be transported back as one complete mathematical object. -/

namespace NivatTrial.ColleCoordinateTransport

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.Dynamics
open NivatTrial.Periodicity NivatTrial.RegionGeometry NivatTrial.ExternalInputs
open NivatTrial.LatticeCoordinates NivatTrial.ColleDirectionalPropagation
open scoped Classical
noncomputable section

theorem det_addHom (e : Lattice →+ Lattice) (u v : Lattice) :
    det (e u) (e v) = det (e (1,0)) (e (0,1)) * det u v := by
  have he (z : Lattice) : e z = z.1 • e (1,0) + z.2 • e (0,1) := by
    rw [← map_zsmul,← map_zsmul,← map_add]
    congr 1
    ext <;> simp
  rw [he u,he v]
  simp only [det,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

theorem det_equiv_zero_iff (e : Lattice ≃+ Lattice) (u v : Lattice) :
    det (e u) (e v) = 0 ↔ det u v = 0 := by
  constructor
  · intro h
    have he := det_addHom e.symm.toAddMonoidHom (e u) (e v)
    simpa only [AddEquiv.toAddMonoidHom_eq_coe,AddMonoidHom.coe_coe,
      e.symm_apply_apply,h,mul_zero] using he
  · intro h
    simpa only [AddEquiv.toAddMonoidHom_eq_coe,AddMonoidHom.coe_coe,h,mul_zero]
      using det_addHom e.toAddMonoidHom u v

theorem isPeriodic_comp_equiv_iff {A : Type*} (e : Lattice ≃+ Lattice)
    (x : Lattice → A) : IsPeriodic (x ∘ e) ↔ IsPeriodic x := by
  constructor
  · rintro ⟨u,hu,hp⟩
    refine ⟨e u,fun he => hu (e.injective (by simpa using he)),?_⟩
    exact (isPeriod_comp_iff e x u).mp hp
  · rintro ⟨u,hu,hp⟩
    refine ⟨e.symm u,fun he => hu (e.symm.injective (by simpa using he)),?_⟩
    apply (isPeriod_comp_iff e x (e.symm u)).mpr
    simpa using hp

def reparametrize {f : Lattice → ℤ} {n : ℕ}
    (E : IntegerDecomposition f n) (e : Lattice ≃+ Lattice) :
    IntegerDecomposition (f ∘ e) n where
  component i := E.component i ∘ e
  period i := e.symm (E.period i)
  period_ne_zero i := fun he => E.period_ne_zero i
    (e.symm.injective (by simpa using he))
  independent i j hij := fun he => E.independent i j hij
    ((det_equiv_zero_iff e.symm _ _).mp he)
  component_period i := (isPeriod_comp_iff e (E.component i) _).mpr
    (by simpa using E.component_period i)
  sum_eq := by
    funext z
    simpa only [Finset.sum_apply,Function.comp_apply] using congrFun E.sum_eq (e z)

theorem hasIntegerDecomposition_comp {M n : ℕ} {x : Lattice → Fin M}
    (h : HasIntegerDecomposition (integerField x) n) (e : Lattice ≃+ Lattice) :
    HasIntegerDecomposition (integerField (x ∘ e)) n := by
  obtain ⟨E⟩ := h
  exact ⟨reparametrize E e⟩

theorem uniformOrder_comp {M n : ℕ} {θ : Lattice → Fin M}
    (h : UniformOrder θ n) (e : Lattice ≃+ Lattice) : UniformOrder (θ ∘ e) n := by
  intro y hy hnot
  have hyback : y ∘ e.symm ∈ languageHull θ := by
    simpa only [Function.comp_def,e.apply_symm_apply] using mem_languageHull_comp_equiv e.symm hy
  have hnotback : ¬IsPeriodic (y ∘ e.symm) :=
    fun hp => hnot ((isPeriodic_comp_equiv_iff e.symm y).mp hp)
  obtain ⟨hD,hmin⟩ := h (y ∘ e.symm) hyback hnotback
  refine ⟨?_,?_⟩
  · simpa only [Function.comp_def,e.symm_apply_apply] using hasIntegerDecomposition_comp hD e
  · intro m hm
    exact hmin m (hasIntegerDecomposition_comp hm e.symm)

theorem latticeConvex_preimage (e : Lattice ≃+ Lattice)
    {R : Set Lattice} (hR : LatticeConvexRegion R) : LatticeConvexRegion (e ⁻¹' R) := by
  obtain ⟨C,hC,hRC⟩ := hR
  refine ⟨(realMap e.toAddMonoidHom) ⁻¹' C,hC.linear_preimage _,?_⟩
  ext z
  simp only [Set.mem_preimage,realMap_embed,hRC]
  rfl

theorem periodicOn_preimage {A : Type*} (e : Lattice ≃+ Lattice)
    {x : Lattice → A} {R : Set Lattice} {u : Lattice}
    (hp : PeriodicOn x R u) : PeriodicOn (x ∘ e) (e ⁻¹' R) (e.symm u) := by
  constructor
  · intro z hz
    change e (z+e.symm u) ∈ R
    simpa only [map_add,e.apply_symm_apply] using hp.1 (e z) hz
  · intro z hz
    change x (e (z+e.symm u)) = x (e z)
    simpa only [map_add,e.apply_symm_apply] using hp.2 (e z) hz

theorem pull_back_regional_conclusion {A : Type*}
    (θ : Lattice → A) (e : Lattice ≃+ Lattice)
    (h : ∃ x ∈ languageHull (θ ∘ e), ¬IsPeriodic x ∧
      ∃ R : Set Lattice, LatticeConvexRegion R ∧ R.Nonempty ∧
        ∃ a b : Lattice, det a b ≠ 0 ∧ PeriodicOn x R a ∧ PeriodicOn x R b) :
    ∃ x ∈ languageHull θ, ¬IsPeriodic x ∧
      ∃ R : Set Lattice, LatticeConvexRegion R ∧ R.Nonempty ∧
        ∃ a b : Lattice, det a b ≠ 0 ∧ PeriodicOn x R a ∧ PeriodicOn x R b := by
  obtain ⟨x,hx,hnot,R,hR,⟨z,hz⟩,a,b,hab,ha,hb⟩ := h
  refine ⟨x ∘ e.symm,?_,?_,e.symm ⁻¹' R,latticeConvex_preimage e.symm hR,
    ⟨e z,by simpa using hz⟩,e a,e b,?_,periodicOn_preimage e.symm ha,
    periodicOn_preimage e.symm hb⟩
  · simpa only [Function.comp_def,e.apply_symm_apply] using mem_languageHull_comp_equiv e.symm hx
  · exact fun hp => hnot ((isPeriodic_comp_equiv_iff e.symm x).mp hp)
  · exact fun he => hab ((det_equiv_zero_iff e a b).mp he)

end
end NivatTrial.ColleCoordinateTransport
