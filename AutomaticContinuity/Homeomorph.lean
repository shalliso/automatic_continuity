import Mathlib

open Set Topology Filter TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace Homeomorph

theorem preimage_dense (h : X ≃ₜ Y) {s : Set Y} (hs : Dense s) : Dense (h ⁻¹' s) := by
  rw [dense_iff_closure_eq] at hs ⊢; rw [←h.preimage_closure, hs, preimage_univ]

theorem image_dense (h : X ≃ₜ Y) {s : Set X} (hs : Dense s) : Dense (h '' s) := by
  rw [dense_iff_closure_eq] at hs ⊢; rw [←h.image_closure, hs, image_univ, range_coe]

theorem preimage_Gδ (h : X ≃ₜ Y) {s : Set Y} (hs : IsGδ s) : IsGδ (h ⁻¹' s) := by
  rcases hs with ⟨T, h_open, h_ctbl, rfl⟩
  refine ⟨(fun t ↦ h ⁻¹' t) '' T, ?_, Countable.image h_ctbl _, by simp⟩
  · rintro _ ⟨U, hU, rfl⟩; exact (isOpen_preimage h).mpr (h_open U hU)

theorem image_Gδ (h : X ≃ₜ Y) {s : Set X} (hs : IsGδ s) : IsGδ (h '' s) := by
  simp only [image_eq_preimage h s, preimage_Gδ h.symm hs]

theorem preimage_residual (h : X ≃ₜ Y) {s : Set Y} (hs : s ∈ residual Y)
    : h ⁻¹' s ∈ residual X := by
  rw [mem_residual_iff] at hs ⊢
  obtain ⟨S, h_open, h_dense, h_ctbl, h_s2⟩ := hs
  refine ⟨(fun t ↦ h ⁻¹' t) '' S, ?_, ?_, Countable.image h_ctbl _, ?_⟩
  · rintro t ⟨x, hxs, rfl⟩; simpa using h_open x hxs
  · rintro t ⟨x, hxs, rfl⟩; simpa using preimage_dense h <| h_dense x hxs
  · have : h ⁻¹' (⋂₀ S) ⊆ h ⁻¹' s := fun x hx ↦ h_s2 hx
    simpa using this

theorem image_residual (h : X ≃ₜ Y) {s : Set X} (hs : s ∈ residual X) : h '' s ∈ residual Y := by
  simp only [image_eq_preimage h s, preimage_residual h.symm hs]

end Homeomorph


variable {G : Type*} [Group G]
variable [MulAction G X] [ContinuousConstSMul G X]

open Pointwise

theorem residual_smul {A : Set X} {g : G} (hA : A ∈ residual X) : g • A ∈ residual X :=
  (Homeomorph.smul g).image_residual hA

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem residual_inv {A : Set G} (hA : A ∈ residual G) : A⁻¹ ∈ residual G := by
  simpa using (Homeomorph.inv G).image_residual hA
