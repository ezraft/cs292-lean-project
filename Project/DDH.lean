import Project.ProjectLib
import Project.Uniform
import Project.Negligible
import Project.PKE
import Project.GroupFamily

/-
  Formalizes the DDH assumption, based on the hardness of the discrete logarithm problem.
-/

open Cslib Cslib.Probability Cslib.Crypto GroupFamily

variable (Gf : GroupFamily) [∀ n, DecidableEq (Gf n)] [∀ n, Group (Gf n)] [∀ n, Finite (Gf n)] [∀ n, Nontrivial (Gf n)] [∀ n, IsCyclic (Gf n)] [∀ n, Fintype (Gf n)] (prime_order : ∀ n, Prime (Fintype.ofFinite (Gf n)).card)

namespace DDH

noncomputable def DDH_real (n : ℕ) (adv : Adversary) : ProbComp Bool := do
  let p := Fintype.card (Gf n)

  let a ← OracleComp.sample (uniform_zmodn p)
  let b ← OracleComp.sample (uniform_zmodn p)
  let g := (exists_ne (1 : (Gf n))).choose
  let g1 := g^(ZMod.val a)
  let g2 := g^(ZMod.val b)
  let g3 := g^((ZMod.val a) * (ZMod.val b))
  adv p (DDHEncoding (Gf n) (g1, g2, g3))

noncomputable def DDH_ideal (n : ℕ) (adv : Adversary) : ProbComp Bool := do
  let p := Fintype.card (Gf n)

  let a ← OracleComp.sample (uniform_zmodn p)
  let b ← OracleComp.sample (uniform_zmodn p)
  let c ← OracleComp.sample (uniform_zmodn p)
  let g := (exists_ne (1 : (Gf n))).choose
  let g1 := g^(ZMod.val a)
  let g2 := g^(ZMod.val b)
  let g3 := g^(ZMod.val c)
  adv p (DDHEncoding (Gf n) (g1, g2, g3))
end DDH


/- The DDH assumption: for some groups, (g^a, g^b, g^(ab)) is not distinguishable from (g^a, g^b, g^c) -/
def DDH_SecureN (n : ℕ) (ε : ℕ → ℝ) (a : PPTAdversary) :=
    advantage (DDH.DDH_real Gf n a.adv) (DDH.DDH_ideal Gf n a.adv) ≤ ε n

def DDH_Secure :=
  ∃ (ε : ℕ → ℝ) (_ : negligible ε), ∀ (n : ℕ) (a : PPTAdversary), DDH_SecureN Gf n ε a
