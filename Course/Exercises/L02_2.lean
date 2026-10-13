/-
  # EXERCISES FOR `L02`

  Some of the exercises are adapted from "Theorem Proving in Lean" and Velleman's "How to Prove It"

  ## INSTRUCTIONS

  Replace the `sorry` in each exercise with a proof of the given proposition.
-/

import Course.CourseLib

variable {α : Type} (A B C : Set α) (x : α)

theorem ex2_1 : x ∈ A \ (A ∩ B) ↔ x ∈ A \ B := by
  rw [Set.sdiff_self_inter]



theorem ex2_2 : x ∈ A ∪ (B ∩ C) ↔ x ∈ (A ∪ B) ∩ (A ∪ C) := by
  rw [Set.union_inter_distrib_left]

theorem ex2_3 : x ∈ (A ∪ B) \ C ↔ x ∈ (A \ C) ∪ (B \ C) := by
  rw [Set.union_sdiff_distrib]

/-
  HINT: depending on how you do the proof, you may find one or more of the
  theorems in `L02_BasicProofs::USEFUL_THEOREMS` to be...well, useful -/
theorem ex2_4 : x ∈ A ∪ (B \ C) ↔ x ∈ (A ∪ B) \ (C \ A) := by
  rw [Set.mem_sdiff]
  rw [Set.mem_union]
  rw [Set.mem_union]
  rw [Set.mem_sdiff]
  rw [Set.mem_sdiff]
  push Not
  rw [imp_iff_not_or]
  nth_rewrite 2 [or_comm]
  rw [<- and_or_right]
  rw [or_comm]
