/-
  # EXERCISES FOR `L02`

  Some of the exercises are adapted from "Theorem Proving in Lean" and Velleman's "How to Prove It"

  ## INSTRUCTIONS

  Replace the `sorry` in each exercise with a proof of the given proposition.
-/

import Course.CourseLib

variable (P Q R : Prop)


theorem ex1_1 : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) := by
  constructor
  · intro h1
    rw [or_assoc] at h1
    exact h1
  · intro h2
    rw [or_assoc]
    exact h2

theorem ex1_2 : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
    rw [and_or_left]



theorem ex1_3 : (P → (Q → R)) ↔ (P ∧ Q → R) := by
  rw [and_imp]

theorem ex1_4 : ((P ∨ Q) → R) ↔ (P → R) ∧ (Q → R) := by
    rw [or_imp]

theorem ex1_5 : ¬P ∨ ¬Q → ¬(P ∧ Q) := by
  push Not
  rw[or_iff_not_imp_left]
  push Not
  intro h
  exact h

theorem ex1_6 : ¬P → (P → Q) := by
  intro h
  rw [imp_iff_not_or]
  left
  exact h
