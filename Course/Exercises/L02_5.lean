/-
  # EXERCISES FOR `L02`

  Some of the exercises are adapted from "Theorem Proving in Lean" and Velleman's "How to Prove It"

  ## INSTRUCTIONS

  Replace the `sorry` in each exercise with a proof of the given proposition.
-/

import Course.CourseLib

variable {α β γ : Type} (f : α → β)

def inj       (f : α → β) := ∀ (x y : α), f x = f y → x = y
def surj      (f : α → β) := ∀ (y : β), ∃ (x : α), f x = y
def bijection (f : α → β) := inj f ∧ surj f

/-
  HINT: remember that the `rw` tactic requires an exact match, so rewriting a
  statement into a different form may be necessary (e.g., using
  `Function.comp`) -/

theorem ex5_1
  (f : α → β) (g : β → γ)
  : surj f → surj g → surj (g ∘ f)
:= by
  unfold surj
  intro h1 h2 y
  obtain ⟨z, hz⟩ := h2 y
  obtain ⟨x, hx⟩ := h1 z
  exists x
  rw [Function.comp]
  rw [hx]
  exact hz



theorem ex5_2
  (f : α → β) (g : β → α)
  (h : g ∘ f = id)
  : inj f
:= by
  unfold inj
  intro x y h1
  have h2 : (g ∘ f) x = x := by rw[h] ; rfl
  have h3 : (g ∘ f) y = y := by rw[h] ; rfl
  have h4 : (g ∘ f) y = (g ∘ f) x := by
    rw [Function.comp, Function.comp, h1]
  lia


/-
  HINT: the following theorems may be useful for `ex5_3`. Don't forget that
  `nlinarith` can solve some (not all) non-linear arithmetic goals. Ignore the
  `@` when using the theorem, it's only there to make the `#check` output look
  nicer. -/
#check @mul_eq_mul_left_iff
#check @mul_div_cancel₀

theorem ex5_3
  (a b : ℝ) (f : ℝ → ℝ)
  (h1 : f = fun z => a*z + b) (h2 : a ≠ 0)
  : bijection f
:= by
  unfold bijection
  constructor
  · unfold inj
    intro x y h
    rw [h1] at h
    have h4 : a * (x - y) = a * 0 := by linarith
    have h5 : x - y = 0 := by
      rw[mul_eq_mul_left_iff] at h4
      cases h4 with
      | inl h6 => exact h6
      | inr h6 => contradiction
    linarith
  · unfold surj
    intro y
    rw [h1]
    exists (y - b)/a
    rw [← eq_sub_iff_add_eq]
    rw [mul_div_cancel₀]
    exact h2
