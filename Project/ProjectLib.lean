import Aesop -- `aesop` tactic
import Batteries.CodeAction.Match -- code completion for `match` expressions
import Mathlib.Data.List.AList
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic -- ℕ notation for Nat
import Mathlib.Basic.Rel
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import Mathlib.Data.BitVec
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Analysis.Complex.Exponential
import Cslib.Init
import Cslib.Crypto.Computational.Basic
import Cslib.Probability.BitString
import Cslib.Computability.Probabilistic.PPT
import Cslib.Languages.Probabilistic.Basic
import Cslib.Probability.PMF
import Cslib.Crypto.Game

open Lean Elab Command Tactic Expr MVarId

/-
  Alias for `#guard_msgs` that includes common configurations -/

macro
  doc?:(docComment)? tk:"#guard_error" c:command : command =>
  `(command|$[$doc?]? #guard_msgs%$tk (whitespace := lax, substring := true) in $c)

/-
  Define aliases for `namespace` and `end` that allow for selective color-coding
  in VS Code -/

syntax "topic::" ident : command
syntax "end_topic" ident : command
syntax "subtopic::" ident : command
syntax "end_subtopic" ident : command

macro_rules
  | `(topic:: $title:ident) => `(namespace $title)
  | `(end_topic $title:ident) => `(end $title)
  | `(subtopic:: $title:ident) => `(namespace $title)
  | `(end_subtopic $title:ident) => `(end $title)

/-
  A helpful theorem. This has to already exist somewhere, but I can't find it
  and it's simple enough to prove my own version. -/
theorem imp_iff_or (A B : Prop) : A ∨ B ↔ ¬A → B := by
  constructor
  case mp =>
    intro h
    exact Or.resolve_left h
  case mpr =>
    intro h1
    by_cases h2 : A
    · left; exact h2
    · right; exact h1 h2
