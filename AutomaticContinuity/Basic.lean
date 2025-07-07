import Mathlib
import AutomaticContinuity.Pointwise
import AutomaticContinuity.Homeomorph

open Filter Set Topology Pointwise
variable {X : Type*} [TopologicalSpace X]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MulAction G X] [ContinuousConstSMul G X]
variable [MeasurableSpace G] [BorelSpace G] [BaireSpace G]

lemma pettis_0 {A : Set G} {U : Set G} (hU : U ∈ 𝓝 1) (hAU : A =ᶠ[residual G] U) : A⁻¹ * A ∈ 𝓝 1 := by
  obtain ⟨V, h_V_mem, h_V_open, h_V_symm, h_V_U⟩ := exists_open_nhds_one_inv_eq_mul_subset hU
  refine Filter.mem_of_superset h_V_mem ?_

  intro v hv

  have h1 : (A⁻¹ : Set G) =ᶠ[residual G] (U⁻¹ : Set G) := by

    sorry
  have h2 : (v⁻¹ • A⁻¹ : Set G) =ᶠ[residual G] (v⁻¹ • U⁻¹) := by

    sorry
  have : ((v⁻¹ • A⁻¹) ∩ A⁻¹ : Set G) =ᶠ[residual G] ((v⁻¹ • U⁻¹) ∩ U⁻¹ : Set G) := by
    exact EventuallyEq.inter h2 h1
  have : ((v⁻¹ • U⁻¹) ∩ U⁻¹ : Set G).Nonempty := by sorry
  have : ((v⁻¹ • A⁻¹) ∩ A⁻¹ : Set G).Nonempty := by sorry

  obtain ⟨g, hgA, hgAv⟩ := this

  have : v * g ∈ A⁻¹ := by sorry
  have : g⁻¹ ∈ A := by sorry

  have : (v * g) * g⁻¹ ∈ A⁻¹ * A := by sorry

  simpa using this

theorem pettis {A : Set G} (hBM : BaireMeasurableSet A) (hA : ¬ IsMeagre A)
    : A⁻¹ * A ∈ nhds 1 := by
  sorry


variable {H: Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [BaireSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]





open TopologicalSpace

variable [SeparableSpace H] [BorelSpace H]

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


    --have : Countable ↑D := by exact hD_countable
    have : IsMeagre (⋃ h ∈ D, φ⁻¹' (h • V)) := by
      rw [IsMeagre, compl_iUnion]
      dsimp [IsMeagre] at h_contra
      simp
      exact (countable_bInter_mem hD_countable).mpr h_contra

    rw [h_covers'] at this
    have a : ¬ IsMeagre (univ : Set G) := BaireTheorem.nonMeagre_of_univ
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
      _ ⊆ V⁻¹ * V := by

          sorry
      _ ⊆ U := by
          rw [h_V_symm]
          exact h_V_U


  have h234 : A⁻¹ * A ⊆ φ ⁻¹' U := by
    simpa using h23

  exact mem_of_superset h4 h234

#print axioms automatic_continuity
