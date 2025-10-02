import Mathlib

noncomputable section

open Topology
open Filter Set TopologicalSpace

variable {X α : Type*} {ι : Sort*}
variable {s t : Set X}

variable [TopologicalSpace X]

lemma residual_frequently_nonempty_open [BaireSpace X] (S : Set X) (hSopen : IsOpen S) (hSne : S.Nonempty)
  : ∃ᵇ (x : X), x ∈ S := by
  by_contra h_meagre
  simp at h_meagre
  have : Sᶜ ∈ residual X := by exact h_meagre
  have : Dense Sᶜ := dense_of_mem_residual this
  have : (S ∩ Sᶜ).Nonempty := Dense.inter_open_nonempty this S hSopen hSne
  simp at this

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
  constructor <;> {
    intro h_meagre
    have : _ᶜ ∩ {x | s x = t x} ∈ residual X := inter_mem h_meagre h
    refine mem_of_superset this ?_
    intro x ⟨hs, hx⟩
    simp only [mem_setOf_eq] at hx
    tauto
  }
