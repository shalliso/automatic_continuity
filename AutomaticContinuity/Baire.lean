import Mathlib

noncomputable section

open scoped Topology
open Filter Set TopologicalSpace

variable {X α : Type*} {ι : Sort*}
variable {s t : Set X}

variable [TopologicalSpace X]

/-- A residual set is nonempty.
    Put this in Topology/Baire/Lemmas.lean
-/
theorem nonempty_of_mem_residual [Nonempty X] [BaireSpace X] (hs : s ∈ residual X)
    : s.Nonempty :=
  (dense_of_mem_residual hs).nonempty

-- rename meagre_empty to IsMeagre.empty

-- rename isMeagre_iUnion to isMeagre_iUnionNat and add the following
/-- A countable union of meagre sets is meagre. -/
lemma isMeagre_iUnion' [Countable ι] {f : ι → Set X} (hs : ∀ i, IsMeagre (f i))
    : IsMeagre (⋃ i, f i) := by
  rw [IsMeagre, compl_iUnion]
  exact countable_iInter_mem.mpr hs

theorem mem_residual_of_univ : univ ∈ residual X := univ_mem

lemma isMeagre_congr_residual {s t : Set X} (h : s =ᶠ[residual X] t) : IsMeagre s ↔ IsMeagre t := by
  dsimp [EventuallyEq, Filter.Eventually] at h
  set A := {x | s x = t x}
  constructor
  · intro h_meagre
    dsimp [IsMeagre] at h_meagre ⊢
    have hs : sᶜ ∩ {x | s x = t x} ∈ residual X := by exact inter_mem h_meagre h
    have hst : sᶜ ∩ {x | s x = t x} = tᶜ ∩ {x | s x = t x} := by ext x; simp; tauto
    rw [hst] at hs
    exact mem_of_superset hs inter_subset_left
  · intro h_meagre
    dsimp [IsMeagre] at h_meagre ⊢
    have hs : tᶜ ∩ {x | s x = t x} ∈ residual X := by exact inter_mem h_meagre h
    have hst : tᶜ ∩ {x | s x = t x} = sᶜ ∩ {x | s x = t x} := by ext x; simp; tauto
    rw [hst] at hs
    exact mem_of_superset hs inter_subset_left

section NonMeagre
-- A non meagre set is a set that is not meagre
def NonMeagre (A : Set X) : Prop := ¬ IsMeagre A

lemma BaireMeasurableSet.nonMeagre_residualEq_isOpen_Nonempty (hBM : BaireMeasurableSet s)
    (hNM : NonMeagre s) : ∃ u : Set X, (IsOpen u) ∧ u.Nonempty ∧ s =ᵇ u := by
  rcases hBM.residualEq_isOpen with ⟨u, h_open, h_su⟩
  refine ⟨u, h_open, ?_, h_su⟩
  · by_contra hu
    push_neg at hu
    have : IsMeagre s := by exact (isMeagre_congr_residual h_su).mpr <| hu.symm ▸ IsMeagre.empty
    contradiction

theorem NonMeagre.univ [Nonempty X] [BaireSpace X] : NonMeagre (univ : Set X) := by
    simp [NonMeagre, IsMeagre]
    by_contra h
    have : (∅ : Set X).Nonempty := nonempty_of_mem_residual h
    simpa

theorem NonMeagre.nonempty [Nonempty X] {s : Set X} (hs : NonMeagre s)
    : s.Nonempty := by
  by_contra h
  have : s = ∅ := by exact Set.not_nonempty_iff_eq_empty.mp h
  rw [this] at hs
  have : IsMeagre (∅ : Set X) := by exact IsMeagre.empty
  contradiction

theorem IsOpen.nonMeagre_of_Nonempty [BaireSpace X] (h_open : IsOpen s) (h_ne : s.Nonempty)
     : NonMeagre s := by
  by_contra h_meagre
  simp [NonMeagre, IsMeagre] at h_meagre
  apply dense_of_mem_residual at h_meagre
  have : (s ∩ sᶜ).Nonempty := Dense.inter_open_nonempty h_meagre s h_open h_ne
  simp at this

lemma NonMeagre.mono {s t : Set X} (hs : NonMeagre s) (hst : s ⊆ t) : NonMeagre t :=
  mt (IsMeagre.mono · hst) hs

theorem nonMeagre_of_nonempty_interior [BaireSpace X] {s : Set X} (hs : (interior s).Nonempty)
    : NonMeagre s :=
  NonMeagre.mono (isOpen_interior.nonMeagre_of_Nonempty hs) interior_subset

theorem nonMeagre_of_mem_nhds [BaireSpace X] {s : Set X} {a : X} (hs : s ∈ 𝓝 a)
    : NonMeagre s := by
  obtain ⟨U, hUs, hU_open, h_aU⟩ := mem_nhds_iff.mp hs
  exact NonMeagre.mono (hU_open.nonMeagre_of_Nonempty ⟨a, h_aU⟩) hUs

/-- If a countable union of sets covers the space,
then one of the sets is non meagre. -/
theorem nonMeagre_of_iUnion_univ [Nonempty X] [BaireSpace X] [Countable ι] {f : ι → Set X}
    (hU : ⋃ i, f i = univ) : ∃ i, NonMeagre (f i) := by
  by_contra h
  simp [NonMeagre] at h
  have h1 : IsMeagre (univ : Set X) := by
    rw [←hU]
    exact isMeagre_iUnion' h
  simp [IsMeagre] at h1
  apply nonempty_of_mem_residual at h1
  obtain ⟨a, ha⟩ := h1
  contradiction

end NonMeagre
