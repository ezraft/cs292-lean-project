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
  HINT: don't forget about the `sorted` lemmas we proved in the lecure notes;
  you will need them in the following exercises -/

/-
  Make available the `sorted` predicate and various useful lemmas about the
  `sorted` predicate -/
open INSERTION_SORT_P2 (sorted empty_sorted singleton_sorted head_sorted
  tail_sorted cons_sorted cons_sorted')

/-
  -----------------------------------------------------------
  MERGE SORT
  -----------------------------------------------------------
-/

/-
  HINT: recall the following theorems, used in `L03_Sorting` -/
#check if_pos
#check if_neg
#check List.Perm.nil
#check List.Perm.refl
#check List.Perm.trans
#check List.Perm.cons
#check List.Perm.swap
#check List.Perm.mem_iff
#check List.mem_cons
#check List.pairwise_cons

/-
  HINT: you may also find the following theorems helpful -/
#check List.Perm.append
#check List.perm_comm
#check List.perm_middle

theorem split_correct
  (ℓ : List ℕ)
  : let (ℓ₁, ℓ₂) := split ℓ
    (ℓ₁ ++ ℓ₂).Perm ℓ
:= by
  unfold split
  simp_all

lemma merge_perm
  (ℓ₁ ℓ₂ : List ℕ)
  : (merge ℓ₁ ℓ₂).Perm (ℓ₁ ++ ℓ₂)
:= by
  fun_induction merge with
  | case1 l => rfl
  | case2 l x => simp_all
  | case3 x l1 y l2 h ih => simp_all
  | case4 x l1 y l2 h ih =>
    simp_all
    obtain h2 := List.Perm.cons y ih
    have h3 : (y :: x :: (l1 ++ l2)).Perm (x :: y :: (l1 ++ l2)) := by apply List.Perm.swap
    obtain h4 := List.Perm.trans h2 h3
    have h5 : (x :: y :: (l1 ++ l2)).Perm (x :: (l1 ++ y :: l2)) := by
      simp_all
      exact List.Perm.symm List.perm_middle
    exact List.Perm.trans h4 h5



lemma merge_sorted
  {ℓ₁ ℓ₂ : List ℕ}
  : sorted ℓ₁ → sorted ℓ₂ → sorted (merge ℓ₁ ℓ₂)
:= by
  intro h1 h2
  fun_induction merge with
  | case1 l => exact h2
  | case2 l x => exact h1
  | case3  x l1 y l2 h ih =>
    simp_all
    have h3 : sorted l1 := by
      exact tail_sorted h1
    obtain h4 := ih h3
    obtain h5 := merge_perm l1 (y :: l2)
    apply cons_sorted
    exact h4
    intro m hm
    have h6 := (List.Perm.mem_iff h5).1 hm
    cases List.mem_append.1 h6 with
      | inl h7 =>
        have hx := head_sorted h1
        exact hx m h7
      | inr h7 =>
        have hy := head_sorted h2
        simp_all
        cases h7 with
        | inl hmy => lia
        | inr hl2 =>
          obtain h8 := hy m hl2
          lia
  | case4 x l1 y l2 h ih =>
    simp_all
    have h3 : sorted l2 := by
      exact tail_sorted h2
    obtain h4 := ih h3
    obtain h5 := merge_perm (x :: l1) l2
    apply cons_sorted
    exact h4
    intro m hm
    have h6 := (List.Perm.mem_iff h5).1 hm
    cases List.mem_append.1 h6 with
      | inl h7 =>
        have hx := head_sorted h1
        simp_all
        cases h7 with
        | inl hmy => lia
        | inr hl2 =>
          obtain h8 := hx m hl2
          lia
      | inr h7 =>
        have hy := head_sorted h2
        exact hy m h7

lemma merge_sort_perm
  (ℓ : List ℕ)
  : (merge_sort ℓ).Perm ℓ
:= by
  fun_induction merge_sort with
  | case1 => exact List.Perm.nil
  | case2 l => rfl
  | case3 x y l1 l2 ih2 ih1 =>
    have h1 := @merge_perm (merge_sort l2.1) (merge_sort l2.2)
    have h2 : (l2.1 ++ l2.2).Perm (x :: y :: l1) := by
      exact split_correct (x :: y :: l1)
    have h3 : (merge_sort l2.1 ++ merge_sort l2.2).Perm (l2.1 ++ l2.2) := by
      exact List.Perm.append ih2 ih1
    have h4 : (merge (merge_sort l2.1) (merge_sort l2.2)).Perm (x :: y :: l1) := by
      obtain h6 := List.Perm.trans h1 h3
      exact List.Perm.trans h6 h2
    exact h4

lemma merge_sort_sorted
  (ℓ : List ℕ)
  : sorted (merge_sort ℓ)
:= by
  fun_induction merge_sort with
  | case1 => exact empty_sorted
  | case2 n => exact singleton_sorted
  | case3 x y l1 l2 ih2 ih1 => exact merge_sorted ih2 ih1
