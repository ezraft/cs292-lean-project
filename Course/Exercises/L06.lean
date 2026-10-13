/-
  # EXERCISES FOR `L06`

  Fill in the `sorry` for the requested definitions. For each definition the
  `#guard_msgs` below it should pass with no errors.
-/

import Course.CourseLib

topic::P1

variable {α β γ : Type}

/-
  Curry a function, i.e., instead of taking a pair of arguments it takes one
  argument at a time -/
def curry (f : (α × β) → γ) : α → β → γ :=
  fun n1 => fun n2 => f (n1, n2)

/-- info: true -/
#guard_msgs in
#eval (curry (fun ((a, b) : ℕ × ℕ) => a * b)) 2 3 == 6

/-
  Uncurry a function, i.e., instead of taking one argument at a time it takes a
  pair of arguments -/
def uncurry (f : α → β → γ) : (α × β) → γ :=
  fun n1 => f n1.1 n1.2
/-- info: true -/
#guard_msgs in
#eval (uncurry (fun (a b : ℕ) => a * b)) (2, 3) == 6

end_topic P1


topic::P2

/-
  A list of integers -/
inductive MyList
  | nil
  | cons : ℤ → MyList → MyList
deriving BEq

namespace MyList

/- For tests -/
def ℓ₁ : MyList := .cons 1 (.cons 2 (.cons 3 .nil))
def ℓ₂ : MyList := (.cons 1 (.cons 2 .nil))
def ℓ₃ : MyList := (.cons 3 .nil)
def ℓ₄ : MyList := .cons 3 (.cons 2 (.cons 1 .nil))

/-
  The fold function that transforms a `MyList` into an `α`. Takes the list to
  transform, a function that takes the accumulated result so far and an element
  of the list and returns a new result, and the initial value (also the result
  if the list is empty). -/
def fold {α : Type} (ℓ : MyList) (f : α → ℤ → α) (init : α) : α :=
  match ℓ with
  | nil => init
  | cons z tl => fold tl f (f init z)
/-- info: 6 -/
#guard_msgs in
#eval ℓ₁.fold (fun acc z => acc * z) 1

/-
  ## INSTRUCTIONS
  For all definitions below here, use your `fold` definition to define the
  functions rather than direct recursion (you may also use the functions you
  have already defined)
-/

/-
  Returns the reverse of `ℓ` -/
def reverse (ℓ : MyList) : MyList :=
  ℓ.fold (fun l1 v => cons v l1) nil

/-- info: true -/
#guard_msgs in
#eval ℓ₁.reverse == ℓ₄

/-
  Returns `ℓ₁ ++ ℓ₂` -/
def append (ℓ₁ ℓ₂ : MyList) : MyList :=
  (ℓ₂.fold (fun l1 v => cons v l1) ℓ₁.reverse).reverse

/-- info: true -/
#guard_msgs in
#eval ℓ₂.append ℓ₃ == ℓ₁

/-
  Returns whether any of the elements satisfy the predicate -/
def any (ℓ : MyList) (P : ℤ → Bool) : Bool :=
  ℓ.fold (fun b v => b ∨ P v) False

/-- info: true -/
#guard_msgs in
#eval ℓ₁.any (fun z => z > 2)

/-- info: false -/
#guard_msgs in
#eval ℓ₁.any (fun z => z = 10)

/-
  Returns whether all of the elements satisfy the predicate -/
def all (ℓ : MyList) (P : ℤ → Bool) : Bool :=
  ℓ.fold (fun b v => b ∧ P v) True

/-- info: true -/
#guard_msgs in
#eval ℓ₁.all (fun z => z < 10)

/-- info: false -/
#guard_msgs in
#eval ℓ₁.all (fun z => z > 2)

/-
  Returns those elements that satisfy the predicate -/
def filter (ℓ : MyList) (P : ℤ → Bool) : MyList :=
   ℓ.fold (fun l1 v => if P v then cons v l1 else l1) nil

/-- info: true -/
#guard_msgs in
#eval ℓ₁.filter (fun z => z > 2) == ℓ₃

end MyList

end_topic P2


topic::P3

/-
  Fill in the function so that it outputs a list of pairs `(str, n)` s.t. `n` is
  the number of times `str` appears in the input list, in the order that `str`
  first appears in the input list. The `#guard_msgs` test immediately below
  should pass with no errors. You may define nested helper functions if you find
  them helpful. -/

def add_to_val (ℓ : List (String × ℕ)) (s : String) : List (String × ℕ) :=
  match ℓ with
  | [] => []
  | x :: xs => if x.1 == s then (x.1, x.2+1)::(add_to_val xs s) else x::(add_to_val xs s)

def word_count (ℓ : List String) : List (String × ℕ) :=
  (count_word ℓ.reverse).reverse
where count_word (ℓ : List String) : List (String × ℕ) :=
  match ℓ with
  | [] => []
  | x :: xs =>
    if ((count_word xs).filter (fun (z,_) => (z == x))).length == 0 then
      [(x,1)] ++ (count_word xs)
    else
      add_to_val (count_word xs) x

#eval word_count ["a", "b", "a", "c", "b", "a"]
/-- info: true -/
#guard_msgs in
#eval word_count ["a", "b", "a", "c", "b", "a"] == [("a", 3), ("b", 2), ("c", 1)]

end_topic P3


topic::P4

/-
  A binary tree where every node and leaf has a value -/
inductive Tree
  | leaf : ℕ → Tree
  | node : ℕ → Tree → Tree → Tree
deriving BEq

namespace Tree

/- For tests-/
def t₁ : Tree :=
  .node 1
    (.node 2
      (.leaf 3)
      (.node 4
        (.leaf 5)
        (.leaf 6)))
    (.node 7
      (.node 8
        (.leaf 9)
        (.leaf 10))
      (.node 11
        (.leaf 12)
        (.leaf 13)))

def t₂ : Tree :=
  .node 2
    (.node 4
      (.leaf 6)
      (.node 8
        (.leaf 10)
        (.leaf 12)))
    (.node 14
      (.node 16
        (.leaf 18)
        (.leaf 20))
      (.node 22
        (.leaf 24)
        (.leaf 26)))

def t₃ : Tree :=
  .node 1
    (.node 2
      (.leaf 3)
      (.leaf 4))
    (.leaf 5)

/-
  Returns whether `n` is an element of the tree -/
def mem (t : Tree) (n : ℕ) : Bool :=
  match t with
    | leaf z => (n == z)
    | node z left right => (n == z) ∨ (mem left n) ∨ (mem right n)

/-- info: true -/
#guard_msgs in
#eval t₁.mem 8

/-- info: false -/
#guard_msgs in
#eval t₁.mem 14

/-
  Outputs a pre-order list of tree elements -/
def toList₁ (t : Tree) : List ℕ :=
  match t with
    | leaf z => [z]
    | node z left right => [z] ++ (toList₁ left) ++ (toList₁ right)

/-- info: true -/
#guard_msgs in
#eval t₁.toList₁ == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-
  Outputs a post-order list of tree elements -/
def toList₂ (t : Tree) : List ℕ :=
  match t with
    | leaf z => [z]
    | node z left right =>  (toList₂ left) ++ (toList₂ right) ++ [z]

/-- info: true -/
#guard_msgs in
#eval t₁.toList₂ == [3, 5, 6, 4, 2, 9, 10, 8, 12, 13, 11, 7, 1]

/-
  Outputs an in-order list of tree elements -/
def toList₃ (t : Tree) : List ℕ :=
  match t with
  | leaf z => [z]
  | node z left right =>  (toList₃ left) ++ [z] ++ (toList₃ right)


/-- info: true -/
#guard_msgs in
#eval t₁.toList₃ == [3, 2, 5, 4, 6, 1, 9, 8, 10, 7, 12, 11, 13]

/-
  Maps each tree element to a new element according to `f` -/
def map (t : Tree) (f : ℕ → ℕ) : Tree :=
  match t with
  | leaf z => .leaf (f z)
  | node z left right =>  .node (f z) (map left f) (map right f)

/-- info: true -/
#guard_msgs in
#eval t₁.map (fun z => 2*z) == t₂

/-
  The fold function on trees. Now `f` takes three arguments: the result of
  folding the left subtree, the result of folding the right subtree, and the
  value at the node. `init` is now a function `leaf` that takes the value at a
  leaf. -/
def fold {α : Type} (t : Tree) (f : α → α → ℕ → α) (leaf : ℕ → α) : α :=
  match t with
  | .leaf z => leaf z
  | .node z left right =>  (f (fold left f leaf) (fold right f leaf) z)
/-- info: 91 -/
#guard_msgs in
#eval t₁.fold (fun accₗ accᵣ n => accₗ + accᵣ + n) id

/-
  Outputs a list of all paths from the root of the tree to a leaf (using the
  value of each node as its identifier). HINT: use the `fold` that you
  implemented above. -/



def paths (t : Tree) : List (List ℕ) :=
  t.fold (fun left right v => (add_to_all left v) ++ (add_to_all right v)) (fun x => [[x]])
where add_to_all (a : List (List ℕ)) (v : ℕ) : List (List ℕ) :=
    match a with
    | [] => []
    | x :: xs => ([v] ++ x) :: (add_to_all xs v)

#eval t₃.paths
/-- info: true -/
#guard_msgs in
#eval t₃.paths == [[1, 2, 3], [1, 2, 4], [1, 5]]

end Tree

end_topic P4
