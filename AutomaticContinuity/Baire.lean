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

variable [BaireSpace X]

theorem empty_IsMeagre : IsMeagre (∅ : Set X) := by
  by_contra h
  simp only [IsMeagre, compl_empty, univ_mem, not_true_eq_false] at h

/-- If a countable union of BaireMeasurable sets covers the space,
then one of the sets is non meagre. -/
theorem nonMeagre_of_iUnion [Nonempty X] [Countable ι] {f : ι → Set X}
    (hc : ∀ i, BaireMeasurableSet (f i)) (hU : ⋃ i, f i = univ) : ∃ i, NonMeagre (f i) := by
  by_contra h
  simp at h
  have : IsMeagre (univ : Set X) := by
    rw [←hU]
    exact isMeagre_iUnion' h

  sorry
  --simpa using (dense_iUnion_interior_of_closed hc hU).nonempty


variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MulAction G X] [ContinuousConstSMul G X]

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

end BaireTheorem
