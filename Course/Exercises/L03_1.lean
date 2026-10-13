/-
  # EXERCISES FOR `L03`

  Reasoning about lists and sorting.

  ## INSTRUCTIONS

  Replace the `sorry` in each theorem below with a proof of the given
  proposition.
-/

import Course.CourseLib

variable {α : Type}

/-
  -----------------------------------------------------------
  REASONING ABOUT LISTS
  -----------------------------------------------------------
-/

/-
  Append an element to the end of a list -/
def snoc : List α → α → List α
  | [], a => [a]
  | x :: xs, a => x :: snoc xs a

/-
  Sum a list of numbers -/
def sum : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + sum xs

/-
  HINT: the following theorems may be useful in some of the exercises below. You
  may also wish to use the results of one exercise in a following exercise. -/
#check List.nil_append
#check List.reverse_cons
#check Nat.right_eq_add

theorem ex3_1
  (ℓ : List ℕ) (n : ℕ)
  : sum (snoc ℓ n) = n + sum ℓ
:= by
  fun_induction sum with
  | case1 => unfold snoc; unfold sum; unfold sum; lia
  | case2 x xs ih =>
    rw [add_comm]
    rw [add_comm] at ih
    rw [add_assoc]
    rw [← ih]
    rfl

theorem ex3_2
  (ℓ₁ ℓ₂ : List ℕ)
  : sum (ℓ₁ ++ ℓ₂) = sum ℓ₁ + sum ℓ₂
:= by
  rw [← ex3_1]
  fun_induction sum with
  | case1 => rw [ex3_1]; rw[List.nil_append]; lia
  | case2 x xs ih =>
    rw [ex3_1]
    rw [List.cons_append]
    conv => lhs; unfold sum
    rw [ih]
    rw [ex3_1]
    rw [add_assoc]


theorem ex3_3
  (ℓ : List ℕ)
  : sum ℓ.reverse = sum ℓ
:= by
  fun_induction sum with
  | case1 => unfold sum; rfl
  | case2 x xs ih =>
    rw [add_comm]
    rw [List.reverse_cons]
    rw [← ih]
    apply ex3_2
