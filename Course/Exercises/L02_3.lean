/-
  # EXERCISES FOR `L02`

  Some of the exercises are adapted from "Theorem Proving in Lean" and Velleman's "How to Prove It"

  ## INSTRUCTIONS

  Replace the `sorry` in each exercise with a proof of the given proposition.
-/

import Course.CourseLib

variable {α : Type} (P Q : α → Prop) (A B C : Set α)

theorem ex3_1 : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by
  rw [forall_and]

theorem ex3_2 : (∀ x, P x) ∨ (∀ x, Q x) → ∀ x, P x ∨ Q x := by
  contrapose
  push Not
  intro h
  obtain ⟨a, ha⟩ := h
  obtain ⟨hP, hQ⟩ := ha
  constructor
  · exists a
  · exists a

theorem ex3_3 : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  rw [exists_or]

theorem ex3_4 : A ⊆ B ↔ A \ B = ∅ := by
  contrapose
  push Not
  constructor
  · intro h
    whnf
    rw [Set.subset_def] at h
    push Not at h
    obtain ⟨a, ha⟩ := h
    exists a
  · intro h
    obtain ⟨a, ha⟩ := h
    whnf at ha
    rw [Set.subset_def]
    push Not
    exists a


theorem ex3_5 : C ⊆ A ∪ B ↔ C \ A ⊆ B := by
  constructor
  · intro h
    rw [Set.subset_def] at h
    rw [Set.subset_def]
    intro a ha
    rw [Set.mem_sdiff] at ha
    obtain ⟨haC, haA⟩ := ha
    have h3 : a ∈ A ∪ B := h a haC
    whnf at h3
    cases h3 with
    | inl h => contradiction
    | inr h => exact h

  · intro h
    rw [Set.subset_def] at h
    rw [Set.subset_def]
    intro a ha
    by_cases h3: a ∈ A
    · left
      exact h3

    · have h4 : a ∈ C \ A := ⟨ha, h3⟩
      have h5 : a ∈ B := h a h4
      right
      exact h5
