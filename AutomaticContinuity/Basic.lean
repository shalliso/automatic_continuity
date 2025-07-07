import Mathlib

open Filter Set Topology
variable {X : Type*} [TopologicalSpace X]

/-- A countable union of meagre sets is meagre. -/
lemma isMeagre_iUnion' {ι : Type*} [Countable ι] {f : ι → Set X} (hs : ∀ i, IsMeagre (f i))
    : IsMeagre (⋃ i, f i) := by
  rw [IsMeagre, compl_iUnion]
  exact countable_iInter_mem.mpr hs

variable {G : Type*} [Group G] [MulAction G X] [ContinuousConstSMul G X]

open Pointwise

theorem residual_smul' {A : Set X} {g : G} : A ∈ residual X → g • A ∈ residual X := by
  intro h
  obtain ⟨S, h_open, h_dense, h_ctbl, h_inter⟩ := mem_residual_iff.mp h
  set S' := g • S
  refine mem_residual_iff.mpr ⟨S', ?_, ?_, ?_, ?_⟩

  simp [S']
  intro U hU
  have h1 : g⁻¹ • U ∈ S := by exact mem_smul_set_iff_inv_smul_mem.mp hU
  have h2 : U = g • (g⁻¹ • U) := by exact Eq.symm (smul_inv_smul g U)
  have h3 := h_open (g⁻¹ • U) h1
  have h4 : IsOpen (g • (g⁻¹ • U)) := by exact IsOpen.smul (h_open (g⁻¹ • U) h1) g
  rw [←h2] at h4
  assumption

  simp [S']
  intro U hU
  have h1 : g⁻¹ • U ∈ S := by exact mem_smul_set_iff_inv_smul_mem.mp hU
  have h2 : U = g • (g⁻¹ • U) := by exact Eq.symm (smul_inv_smul g U)
  have h3 := h_dense (g⁻¹ • U) h1
  have h4 : Dense (g • (g⁻¹ • U)) := by exact Dense.smul g (h_dense (g⁻¹ • U) h1)
  rw [←h2] at h4
  assumption

  rcases Set.eq_empty_or_nonempty S with rfl|hS
  . have : S' = ∅ := by
      exact smul_set_empty
    rwa [this]

  obtain ⟨f, hf⟩ : ∃ (f : ℕ → Set X), S = range f := Countable.exists_eq_range h_ctbl hS
  set h := fun (n : ℕ) ↦ (g • f n)
  rw [countable_iff_exists_subset_range]
  use h
  intro s hs
  obtain ⟨s', hs1, hs2⟩ := hs
  simp at hs2
  rw [hf] at hs1
  obtain ⟨n, hfn⟩ := hs1
  use n
  simp [h, hfn, hs2]


  have : ⋂₀ S' = g • (⋂₀ S) := by
    simp [S']
    ext x
    constructor

    intro h
    simp [HSMul.hSMul, SMul.smul]
    use g⁻¹ • x
    constructor
    intro t ht
    have : g • t ∈ g • S := by exact smul_mem_smul_set ht
    have : x ∈ g • t := by exact h (g • t) this
    (expose_names; exact mem_smul_set_iff_inv_smul_mem.mp (h (g • t) this_1))

    exact smul_inv_smul g x

    intro h
    intro t ht
    have h453 : g⁻¹ • t ∈ S := by exact mem_smul_set_iff_inv_smul_mem.mp ht
    simp [HSMul.hSMul, SMul.smul] at h
    obtain ⟨x_1, hx_1t, hx2⟩ := h
    rw [←hx2]
    have h12 : x_1 ∈ g⁻¹ • t := by exact hx_1t (g⁻¹ • t) h453
    have : g • x_1 ∈ t := by exact mem_inv_smul_set_iff.mp (hx_1t (g⁻¹ • t) h453)
    exact this

  intro x hx
  rw [this] at hx
  have : g • ⋂₀ S ⊆ g • A := by exact smul_set_mono h_inter
  exact this hx



theorem isMeagre_smul {A : Set X} {g : G} : IsMeagre A → IsMeagre (g • A) := by
  dsimp [IsMeagre]
  rw [←smul_set_compl]
  exact residual_smul'

/-- A union of two meagre sets is meagre. -/
lemma isMeagre_union {s t : Set X} (hs : IsMeagre s) (ht : IsMeagre t)
    : IsMeagre (s ∪ t) := by
  rw [IsMeagre, compl_union]
  exact inter_mem hs ht


/-- A residual set is nonempty.
    Put this in Topology/Baire/Lemmas.lean
-/
theorem nonempty_of_residual [Nonempty X] [BaireSpace X] {s : Set X} : s ∈ residual X → s.Nonempty := by
  exact (fun h ↦ (dense_of_mem_residual h).nonempty)

theorem empty_IsMeagre [BaireSpace X] : IsMeagre (∅ : Set X) := by
  by_contra h
  simp only [IsMeagre, compl_empty, univ_mem, not_true_eq_false] at h

theorem BaireTheorem.nonMeagre_of_univ [Nonempty X] [BaireSpace X]
    : ¬ (IsMeagre (univ : Set X)) := by sorry


variable [TopologicalSpace G] [IsTopologicalGroup G] [BaireSpace G] [MeasurableSpace G] [BorelSpace G]



-- Add this next to exists_closed_nhds_one_inv_eq_mul_subset in
-- Topology/Algebra/Group/Pointwise.lean
/-- Given a neighborhood `U` of the identity, one may find a neighborhood `V` of the identity which
is open, symmetric, and satisfies `V * V ⊆ U`. -/
@[to_additive "Given a neighborhood `U` of the identity, one may find a neighborhood `V` of the
identity which is open, symmetric, and satisfies `V + V ⊆ U`."]
theorem exists_open_nhds_one_inv_eq_mul_subset {U : Set G} (hU : U ∈ 𝓝 1) :
    ∃ V ∈ 𝓝 1, IsOpen V ∧ V⁻¹ = V ∧ V * V ⊆ U := by
  rcases exists_open_nhds_one_mul_subset hU with ⟨V, V_open, V_one, hV⟩
  --rcases exists_mem_nhds_isClosed_subset (V_open.mem_nhds V_mem) with ⟨W, W_mem, W_closed, hW⟩
  have V_mem : V ∈ 𝓝 1 := V_open.mem_nhds V_one
  refine ⟨V ∩ V⁻¹, Filter.inter_mem V_mem (inv_mem_nhds_one G V_mem), V_open.inter V_open.inv,
    by simp [inter_comm], ?_⟩
  calc
  V ∩ V⁻¹ * (V ∩ V⁻¹)
  _ ⊆ V * V := mul_subset_mul inter_subset_left inter_subset_left
  _ ⊆ U := hV



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
  intro U hU
  obtain ⟨V, h_V_mem, h_V_open, h_V_symm, h_V_U⟩ := exists_open_nhds_one_inv_eq_mul_subset hU

  set m : H → Set H := fun h ↦ h • V
  have hasdf : ∀ h, m h ∈ nhds h := by
    intro h
    dsimp [m]
    exact smul_mem_nhds_self.mpr h_V_mem

  obtain ⟨D, hD_countable, h1⟩ : ∃ (D : Set H), D.Countable ∧ ⋃ d ∈ D, m d = univ
    := TopologicalSpace.countable_cover_nhds hasdf

  have h2 : ⋃ h ∈ D, φ⁻¹' (h • V) = univ := by
    rw [←preimage_iUnion₂, h1]
    rfl

  have h101 : ∃ d ∈ D, ¬ IsMeagre (φ⁻¹' (d • V)) := by
    by_contra h_contra
    simp at h_contra

    --have : Countable ↑D := by exact hD_countable
    have : IsMeagre (⋃ h ∈ D, φ⁻¹' (h • V)) := by
      rw [IsMeagre, compl_iUnion]
      dsimp [IsMeagre] at h_contra
      simp
      exact (countable_bInter_mem hD_countable).mpr h_contra

    rw [h2] at this
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
