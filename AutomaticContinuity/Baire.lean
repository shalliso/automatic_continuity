import Mathlib

noncomputable section

open scoped Topology
open Filter Set TopologicalSpace

variable {X α : Type*} {ι : Sort*}

section BaireTheorem

variable [TopologicalSpace X]

/-- A set is nonmeagre if it is not meagre. -/
abbrev NonMeagre (A : Set X) : Prop := ¬ IsMeagre A

/-- A countable union of meagre sets is meagre. -/
lemma isMeagre_iUnion' [Countable ι]
  {f : ι → Set X} (hs : ∀ i, IsMeagre (f i)) : IsMeagre (⋃ i, f i) := by
  rw [IsMeagre, compl_iUnion]
  exact countable_iInter_mem.mpr hs

theorem IsMeagre_of_empty : IsMeagre (∅ : Set X) := by
  by_contra h
  simp only [IsMeagre, compl_empty, univ_mem, not_true_eq_false] at h

theorem mem_residual_of_univ : univ ∈ residual X := by exact univ_mem

/-- A residual set is nonempty.
    Put this in Topology/Baire/Lemmas.lean
-/
theorem nonempty_of_mem_residual [Nonempty X] [BaireSpace X] {s : Set X} (hs : s ∈ residual X)
    : s.Nonempty :=
  (dense_of_mem_residual hs).nonempty

theorem NonMeagre_of_univ [Nonempty X] [BaireSpace X] : NonMeagre (univ : Set X) := by
  simp [NonMeagre, IsMeagre]
  by_contra h
  have : (∅ : Set X).Nonempty := nonempty_of_mem_residual h
  simpa

theorem NonMeagre_of_nonempty_open [BaireSpace X] {s : Set X} (h_ne : s.Nonempty) (h_open : IsOpen s)
    : NonMeagre s := by
  by_contra h_meagre
  simp [IsMeagre] at h_meagre
  apply dense_of_mem_residual at h_meagre
  have : (s ∩ sᶜ).Nonempty := Dense.inter_open_nonempty h_meagre s h_open h_ne
  simp at this

lemma NonMeagre.mono {s t : Set X} (hs : NonMeagre s) (hst : s ⊆ t) : NonMeagre t :=
  mt (IsMeagre.mono · hst) hs

theorem NonMeagre_of_nonempty_interior [BaireSpace X] {s : Set X} (hs : (interior s).Nonempty)
    : NonMeagre s :=
  NonMeagre.mono (NonMeagre_of_nonempty_open hs isOpen_interior) interior_subset

theorem NonMeagre_of_mem_nhds [BaireSpace X] {s : Set X} {a : X} (hs : s ∈ 𝓝 a)
    : NonMeagre s := by
  obtain ⟨U, hUs, hU_open, h_aU⟩ := mem_nhds_iff.mp hs
  exact NonMeagre.mono (NonMeagre_of_nonempty_open ⟨a, h_aU⟩ hU_open) hUs

/-- If a countable union of BaireMeasurable sets covers the space,
then one of the sets is non meagre. -/
theorem nonMeagre_of_iUnion [Nonempty X] [BaireSpace X] [Countable ι] {f : ι → Set X}
    (hc : ∀ i, BaireMeasurableSet (f i)) (hU : ⋃ i, f i = univ) : ∃ i, NonMeagre (f i) := by
  by_contra h
  simp at h
  have h1 : IsMeagre (univ : Set X) := by
    rw [←hU]
    exact isMeagre_iUnion' h
  simp [IsMeagre] at h1
  apply nonempty_of_mem_residual at h1
  obtain ⟨a, ha⟩ := h1
  contradiction

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MulAction G X] [ContinuousConstSMul G X]

/-- A union of two meagre sets is meagre. -/
lemma isMeagre_union {s t : Set X} (hs : IsMeagre s) (ht : IsMeagre t)
    : IsMeagre (s ∪ t) := by
  rw [IsMeagre, compl_union]
  exact inter_mem hs ht


theorem nonempty_of_NonMeagre [Nonempty X] {s : Set X} (hs : NonMeagre s)
    : s.Nonempty := by
  by_contra h
  have : s = ∅ := by exact Set.not_nonempty_iff_eq_empty.mp h
  rw [this] at hs
  have : IsMeagre (∅ : Set X) := by exact IsMeagre_of_empty
  contradiction

lemma isMeagre_congr_residual {s t : Set X} (h : s =ᶠ[residual X] t) : IsMeagre s ↔ IsMeagre t := by
  dsimp [EventuallyEq, Filter.Eventually] at h
  set A := {x | s x = t x}
  constructor
  · intro h_meagre
    dsimp [IsMeagre] at h_meagre ⊢
    have hs : sᶜ ∩ {x | s x = t x} ∈ residual X := by exact inter_mem h_meagre h
    have hst : sᶜ ∩ {x | s x = t x} = tᶜ ∩ {x | s x = t x} := by
      ext x
      simp
      tauto
    rw [hst] at hs
    exact mem_of_superset hs inter_subset_left
  · intro h_meagre
    dsimp [IsMeagre] at h_meagre ⊢
    have hs : tᶜ ∩ {x | s x = t x} ∈ residual X := by exact inter_mem h_meagre h
    have hst : tᶜ ∩ {x | s x = t x} = sᶜ ∩ {x | s x = t x} := by
      ext x
      simp
      tauto
    rw [hst] at hs
    exact mem_of_superset hs inter_subset_left

end BaireTheorem
