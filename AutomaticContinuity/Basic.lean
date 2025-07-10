import Mathlib
import AutomaticContinuity.Pointwise
import AutomaticContinuity.Homeomorph
import AutomaticContinuity.Baire

open Filter Set Topology Pointwise TopologicalSpace
variable {X : Type*} [TopologicalSpace X]
variable {G : Type*} [Group G] [MulAction G X] [ContinuousConstSMul G X]

lemma residual_smul_eventuallyEq {A B : Set X} {g : G} (h : A =ᶠ[residual X] B)
    : g • A =ᶠ[residual X] g • B := by
  simp [EventuallyEq, Filter.Eventually] at h ⊢
  have : g • {x | A x ↔ B x} = {x | (g • A) x ↔ (g • B) x} := by
    calc
      g • {x | A x ↔ B x}
        = {x | A (g⁻¹ • x) ↔ B (g⁻¹ • x)} := by rw [←preimage_smul_inv]; simp
      _ = {x | (g • A) x ↔ (g • B) x} := by simp only [←preimage_smul_inv] ;rfl
  rw [←this]
  exact residual_smul g h

variable [TopologicalSpace G] [IsTopologicalGroup G] [BaireSpace G]

lemma pettis_0 {A : Set G} {U : Set G} (hU : U ∈ 𝓝 1) (hAU : A =ᶠ[residual G] U)
    : A⁻¹ * A ∈ 𝓝 1 := by
  obtain ⟨V, h_V_mem, h_V_open, h_V_symm, h_V_U⟩ := exists_open_nhds_one_inv_eq_mul_subset hU
  refine Filter.mem_of_superset h_V_mem ?_
  intro v hv
  have h_res_eq : ((v⁻¹ • A⁻¹) ∩ A⁻¹ : Set G) =ᶠ[residual G] ((v⁻¹ • U⁻¹) ∩ U⁻¹ : Set G) :=
    have hAU_inv : (A⁻¹ : Set G) =ᶠ[residual G] (U⁻¹ : Set G) := residual_inv hAU
    (residual_smul_eventuallyEq hAU_inv).inter hAU_inv
  have h_mem_nhds : (v⁻¹ • U⁻¹) ∩ U⁻¹ ∈ 𝓝 1 := by
    refine inter_mem ?_ <| inv_mem_nhds_one G hU
    have h42 : U⁻¹ ∈ 𝓝 v := by
      rw [mem_nhds_iff]
      use V
      refine ⟨?_, h_V_open, hv⟩

      have h44 : V⁻¹ ⊆ U := by
        rw [h_V_symm]
        intro x hx
        have hxV : x ∈ V := hx
        have h1V : 1 ∈ V := mem_of_mem_nhds h_V_mem
        have hmul : x * 1 ∈ V * V := mul_mem_mul hxV h1V
        simp at hmul
        exact h_V_U hmul
      exact inv_subset.mp h44
    rw [← (smul_mem_nhds_smul_iff v)]
    simpa
  have h_nm : NonMeagre ((v⁻¹ • A⁻¹) ∩ A⁻¹ : Set G) := mt
    (isMeagre_congr_residual h_res_eq).mp <| nonMeagre_of_mem_nhds h_mem_nhds
  obtain ⟨g, hgA, hgAv⟩ : ((v⁻¹ • A⁻¹) ∩ A⁻¹ : Set G).Nonempty :=
    h_nm.nonempty
  have : (v * g) * g⁻¹ ∈ A⁻¹ * A :=
    ⟨v • g, by rwa [← mem_inv_smul_set_iff], g⁻¹, by rwa [← Set.mem_inv], by simp⟩
  simpa using this

theorem pettis {A : Set G} (hBM : BaireMeasurableSet A) (hA : ¬ IsMeagre A)
    : A⁻¹ * A ∈ nhds 1 := by
  obtain ⟨U, hU, AU⟩ := hBM.residualEq_isOpen
  have : NonMeagre U := mt (isMeagre_congr_residual AU).mpr hA
  obtain ⟨g, hg⟩ : U.Nonempty := this.nonempty
  have h_mem_nhds : g⁻¹ • U ∈ 𝓝 1 := by
    have : U ∈ 𝓝 g := by exact IsOpen.mem_nhds hU hg
    rwa [←inv_mul_cancel g, ←smul_eq_mul, smul_mem_nhds_smul_iff g⁻¹]
  have h_res_eq: g⁻¹ • A =ᶠ[residual G] g⁻¹ • U := by
    exact residual_smul_eventuallyEq AU
  have : (g⁻¹ • A)⁻¹ * (g⁻¹ • A) ∈ 𝓝 1 := pettis_0 h_mem_nhds h_res_eq
  simpa [Set.op_smul_set_mul_eq_mul_smul_set] using this

variable [MeasurableSpace G] [BorelSpace G]
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

example {φ : G →* H} (h : ContinuousAt φ 1) : (Continuous φ) := continuous_of_continuousAt_one φ h

lemma automatic_continuity {φ : G →* H} (h: Measurable φ) : Continuous φ := by
  -- Enough to show continuous at 1
  apply continuous_of_continuousAt_one

  rw [continuousAt_def, map_one]

  -- Fix an arbitrary neighborhood U of the 1 of H
  intro U hU

  -- Find symmetric neighborhood V of 1 satisfying V * V ⊆ U
  obtain ⟨V, h_V_mem, h_V_open, h_V_symm, h_V_U⟩ := exists_open_nhds_one_inv_eq_mul_subset hU

  -- Find a countable set D such that D • V covers H
  obtain ⟨D, hD_countable, h_covers⟩ : ∃ (D : Set H), D.Countable ∧ ⋃ d ∈ D, d • V = univ
    := TopologicalSpace.countable_cover_nhds <| fun h ↦ id (smul_mem_nhds_self.mpr h_V_mem)

  have h_covers' : ⋃ h ∈ D, φ⁻¹' (h • V) = univ := by
    rw [←preimage_iUnion₂, h_covers]
    rfl

  have h101 : ∃ d ∈ D, ¬ IsMeagre (φ⁻¹' (d • V)) := by
    by_contra h_contra
    simp [IsMeagre] at h_contra

    have : IsMeagre (⋃ h ∈ D, φ⁻¹' (h • V)) := by
      rw [IsMeagre, compl_iUnion]
      simp
      exact (countable_bInter_mem hD_countable).mpr h_contra

    rw [h_covers'] at this
    have a : ¬ IsMeagre (univ : Set G) := NonMeagre_of_univ
    contradiction

  obtain ⟨d, hd, hnonmeagre⟩ : ∃ d ∈ D, ¬ IsMeagre (φ⁻¹' (d • V)) := h101

  set A := φ⁻¹' (d • V)
  have : BaireMeasurableSet A := (h (h_V_open.smul d).measurableSet).baireMeasurableSet
  have h4 : A⁻¹ * A ∈ nhds 1 := by exact pettis this hnonmeagre

  have h234 : φ '' A ⊆ d • V := by
    dsimp [A]
    exact image_preimage_subset (⇑φ) (d • V)
  have h23 : φ '' (A⁻¹ * A) ⊆ U := by
    calc
      φ '' (A⁻¹ * A)
        = (φ '' A⁻¹) * (φ '' A) := by
          exact image_mul φ
      _ = (φ '' A)⁻¹ * (φ '' A) := by
          exact congrFun (congrArg HMul.hMul (image_inv φ A)) (φ '' A)
      _ ⊆ (d • V)⁻¹ * (d • V) := by
          have : φ '' A ⊆ d • V := by
            dsimp [A]
            exact image_preimage_subset (⇑φ) (d • V)
          refine mul_subset_mul (inv_subset_inv.mpr h234) h234
      _ = V⁻¹ * V := by
          rw [inv_smul_set_distrib, Set.op_smul_set_mul_eq_mul_smul_set, inv_smul_smul]
      _ ⊆ U := by
          rw [h_V_symm]
          exact h_V_U


  have h234 : A⁻¹ * A ⊆ φ ⁻¹' U := by
    simpa using h23

  exact mem_of_superset h4 h234

#print axioms automatic_continuity
