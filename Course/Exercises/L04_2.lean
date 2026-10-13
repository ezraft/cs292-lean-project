/-
  # EXERCISES FOR `L04`

  Mergesort and selection sort.

  ## INSTRUCTIONS

  Fill in the `sorry` for the theorems below.
-/

import Course.CourseLib
import Course.L03_Sorting
import Course.L04_SortingDeux

/-
  Make available the `sorted` predicate and various useful lemmas about the
  `sorted` predicate -/
open INSERTION_SORT_P2 (sorted empty_sorted singleton_sorted head_sorted
  tail_sorted cons_sorted cons_sorted')

/-
  -----------------------------------------------------------
  SELECTION SORT
  -----------------------------------------------------------
-/

/-
  Given `n` and `ℓ` returns `n₁` and `ℓ₁` where `n₁` is the smallest element in
  `n :: ℓ` and `ℓ₁` is all of `n :: ℓ` _except_ the smallest element. We can see
  what `List.minimum_of_length_pos` does by hovering over it in VS Code. It
  requires a proof that the list is nonempty, which we provide using `simp`. -/
def select_min (n : ℕ) (ℓ : List ℕ) : ℕ × (List ℕ) :=
  let min := (n :: ℓ).minimum_of_length_pos (by simp)
  (min, (n :: ℓ).erase min)

/-
  A useful lemma for helping to prove termination of `selection_sort` below -/
lemma select_min_size
  (n : ℕ) (ℓ : List ℕ)
  : let (_, ℓ₁) := select_min n ℓ
    ℓ₁.length = ℓ.length
:= by simp [select_min, List.minimum_of_length_pos_mem]

/-
  The selection sort algorithm -/
def selection_sort : List ℕ → List ℕ
  | [] => []
  | x :: xs =>
    let mr := select_min x xs
    mr.1 :: (selection_sort mr.2)
termination_by ℓ => ℓ.length
decreasing_by simp_all [select_min_size x xs]

/-
  HINT: Some useful theorems for the lemmas below (along with the theorems
  already suggested in the `L04_1` exercises) -/
#check List.minimum_of_length_pos_mem
#check List.minimum_of_length_pos_le_of_mem
#check List.perm_cons_erase

/-
  HINT: sometimes `simp` will simplify things _too_ much, applying too many
  rewrites that transform the target into something that our theorems don't
  apply to. Remember that we can use `simp only [...]` to apply only the
  theorems we want, and in particular we can use `simp only` to apply no
  theorems at all, only the built-in `simp` simplications. -/

lemma select_min_perm
  (n : ℕ) (ℓ : List ℕ)
  : let (n₁, ℓ₁) := select_min n ℓ
    (n₁ :: ℓ₁).Perm (n :: ℓ)
:= by
  unfold select_min
  simp_all
  rw [List.perm_comm]
  apply List.perm_cons_erase
  apply List.minimum_of_length_pos_mem

lemma select_min_smallest
  (n : ℕ) (ℓ : List ℕ)
  : let (n₁, _) := select_min n ℓ
    (∀ m ∈ (n :: ℓ), n₁ ≤ m)
:= by
  unfold select_min
  simp only
  intro m hm
  apply List.minimum_of_length_pos_le_of_mem hm

lemma selection_sort_perm
  (ℓ : List ℕ)
  : (selection_sort ℓ).Perm ℓ
:= by
  fun_induction selection_sort with
  | case1 => rfl
  | case2 x xs mr ih =>
    obtain h3 := select_min_perm x xs
    have h4 : (mr.1 :: mr.2).Perm (x :: xs) := by
      exact h3
    have h5 : (mr.1 :: mr.2).Perm (mr.1 :: selection_sort mr.2) := by
      apply List.Perm.cons
      rw [List.perm_comm]
      exact ih
    rw [List.perm_comm] at h5
    apply List.Perm.trans h5 h4


lemma selection_sort_sorted
  (ℓ : List ℕ)
  : sorted (selection_sort ℓ)
:= by
  fun_induction selection_sort with
  | case1 => apply empty_sorted
  | case2 x xs mr ih =>
    obtain h1 := selection_sort_perm mr.2
    obtain h2 := select_min_smallest x xs
    have h3 : mr.1 ≤ x ∧ ∀ m ∈ xs, mr.1 ≤ m := by
      simp at h2
      exact h2
    have h4 : ∀ m ∈ selection_sort mr.2, mr.1 ≤ m := by
      intro m hm
      have h6 := (List.Perm.mem_iff h1).1 hm
      have h7 : m ∈ x :: xs := by
        exact List.mem_of_mem_erase h6
      obtain h8 := List.eq_or_mem_of_mem_cons h7
      obtain ⟨h9, h10⟩ := h3
      cases h8 with
      | inl h => lia
      | inr h =>
        exact h10 m h
    exact cons_sorted ih h4
