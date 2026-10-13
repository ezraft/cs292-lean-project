/-
  # EXERCISES FOR `L05`
-/

import Course.CourseLib

/-
  ## INSTRUCTIONS

  We revisit the tree-based map from the `L03_2` exercises to finish proving
  correctness. The theorems from `L03_2` establish that the `BstMap` functions
  are consistent with each other, but do not prove that insertion preserves the
  binary search tree property. Fill in the `sorry` in the theorems below to
  establish that fact.
-/

/- Same as before -/
inductive BstMap (α β : Type) [LinearOrder α] where
  | empty
  | node (left right : BstMap α β) (key : α) (val : β)

namespace BstMap

variable {α β : Type} [LinearOrder α]

/- Same as before -/
def insert : BstMap α β → α → β → BstMap α β
  | .empty, key, val => .node .empty .empty key val
  | .node left right k v, key, val =>
    if k = key then .node left right key val
    else if key < k then .node (left.insert key val) right k v
    else .node left (right.insert key val) k v

/-
  **NEW**
  We need a predicate to be able to say that some proposition holds for every
  node in a `BstMap` -/
def every_node_prop (P : α → β → Prop) : BstMap α β → Prop
  | .empty => True
  | .node left right k v =>
    P k v ∧
    every_node_prop P left ∧
    every_node_prop P right

/-
  **NEW**
  The BST invariant, i.e., for each node its key is less than than all keys in
  its left subtree and greater than than all keys in its right subtree -/
inductive BstInv : BstMap α β → Prop
  | empty_inv : BstInv .empty
  | node_inv left right k v :
      every_node_prop (fun kₗ _ => kₗ < k) left →
      every_node_prop (fun kᵣ _ => k < kᵣ) right →
      BstInv left → BstInv right → BstInv (.node left right k v)

/-
  **NEW**
  It will be helpful to prove that inserting a (key, value) pair into a `BstMap`
  preserves the properties of other (key, value) pairs -/
lemma insert_preserves_pred
  (bst : BstMap α β) (key : α) (val : β) (P : α → β → Prop)
  : every_node_prop P bst → P key val → every_node_prop P (bst.insert key val)
:= by
  intro h1 h2

  fun_induction every_node_prop with
  | case1 =>
    unfold insert
    unfold every_node_prop
    constructor
    · exact h2
    · unfold every_node_prop
      lia
  | case2 left right k v ih2 ih1 =>
    unfold insert
    by_cases h : k = key
    case pos =>
      rw [if_pos h]
      unfold every_node_prop
      obtain ⟨h3, h4⟩ := h1
      constructor
      · exact h2
      · exact h4
    case neg =>
      rw [if_neg h]
      by_cases hk : key < k
      case pos =>
        rw [if_pos hk]
        obtain ⟨h3, h4, h5⟩ := h1
        unfold every_node_prop
        constructor
        · exact h3
        · exact ⟨ih2 h4,h5⟩
      case neg =>
        rw [if_neg hk]
        obtain ⟨h3, h4, h5⟩ := h1
        unfold every_node_prop
        constructor
        · exact h3
        · exact ⟨h4, ih1 h5⟩

/-
  HINT: some potentially helpful theorems. We can use the `PartialOrder` theorem
  because we require `LinearOrder α` when we define `BstMap`, and any linear
  order is automatically also a partial order. -/
#check if_pos
#check if_neg
#check PartialOrder.le_antisymm

/-
  HINT: remember that inductive type constructors (e.g., the constructors
  `BstInv.{empty_inv, node_inv}`) are just functions, and can be passed to
  `simp` just like any function, e.g., `simp [BstInv.node_inv]` -/

/-
  **NEW**
  Here is the main theorem that says `insert` preserves the `BstInv` property -/
theorem insert_preserves_bstinv
  (bst : BstMap α β) (key : α) (val : β)
  : BstInv bst → BstInv (insert bst key val)
:= by
  intro h
  fun_induction insert with
  | case1 key val =>
    apply BstInv.node_inv empty empty key val trivial trivial
    simp [BstInv.empty_inv]
    simp [BstInv.empty_inv]
  | case2 left right v key val =>
    obtain ⟨_⟩ := h
    rename_i h2 h3 left_ih right_ih
    apply BstInv.node_inv left right key val
    exact left_ih
    exact right_ih
    exact h2
    exact h3
  | case3 left right k v key val h2 h3 ih1 =>
    obtain ⟨_⟩ := h
    rename_i h4 h5 left_ih right_ih
    simp_all
    apply BstInv.node_inv (left.insert key val) right k v
    apply insert_preserves_pred
    exact left_ih
    exact h3
    exact right_ih
    exact ih1
    exact h5
  | case4 left right k v key val h2 h3 ih1 =>
    obtain ⟨_⟩ := h
    rename_i h4 h5 left_ih right_ih
    simp_all
    apply BstInv.node_inv left (right.insert key val) k v
    exact left_ih
    apply insert_preserves_pred
    exact right_ih
    have h6 : k < key := by
      rw [lt_iff_le_and_ne]
      exact ⟨h3, h2⟩
    exact h6
    exact h4
    exact ih1

end BstMap
