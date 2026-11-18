import Project.ProjectLib
import Project.Uniform
import Project.Negligible
import Project.PKE

/-
  Formalizes group families and their encoding into words.
-/

open Cslib Cslib.Probability Cslib.Crypto


abbrev GroupFamily := ℕ → Type*

variable (Gf : GroupFamily) [∀ n, DecidableEq (Gf n)] [∀ n, Group (Gf n)] [∀ n, Finite (Gf n)] [∀ n, Nontrivial (Gf n)] [∀ n, IsCyclic (Gf n)] [∀ n, Fintype (Gf n)] (_ : ∀ n, Prime (Fintype.ofFinite (Gf n)).card)
variable (G : Type*) [DecidableEq G] [Group G] [Finite G] [Nontrivial G] [IsCyclic G] [Fintype G] (_ : Prime (Fintype.ofFinite G).card)


namespace GroupFamily

@[simp, grind]
noncomputable def WordToNat (w : Word) : ℕ :=
  List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + b.toNat) 0 w

@[simp, grind]
noncomputable def NatToWord (n : ℕ) : Word :=
  if n = 0 then [false] else [(n % 2) == 1] ++ NatToWord (n/2)

@[simp, grind]
noncomputable def GroupEltEnumeration (g : G) : ℕ :=
  (Fintype.equivFin G) g

@[simp, grind]
noncomputable def ReverseGroupEltEnumeration : ℕ → G :=
  fun n =>
    if h: n < Fintype.card G then
      let nFin := { val := n, isLt := h}
      (Fintype.equivFin G).2 nFin
    else (1 : G)

@[simp, grind]
noncomputable def GroupEltEncoding (g : G) : Word :=
  NatToWord (GroupEltEnumeration G g)

@[simp, grind]
noncomputable def WordToGroupElt (w : Word) : G :=
  ReverseGroupEltEnumeration G (WordToNat w)

noncomputable def GroupProductEncoding (elt : G × G) : Word :=
  (GroupEltEncoding (G × G) elt)

noncomputable def DDHEncoding (elt : G × G × G) : Word :=
  (GroupEltEncoding G elt.1) ++ (GroupEltEncoding G elt.2.1) ++ (GroupEltEncoding G elt.2.2)

def nonTrivElts : Finset G :=
  {(g : G) | g ≠ 1}

@[grind.]
theorem WordToNat_append : ∀ (a : Bool) (b : Word), WordToNat (a :: b) = a.toNat + 2 * WordToNat b := by
  grind [WordToNat]

@[grind.]
theorem NatEncodingIsCorrect : ∀ (n : ℕ), WordToNat (NatToWord n) = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold NatToWord
    split
    · simp_all
    · obtain h1 := ih (n/2)
      have h2 : n/2 < n := by lia
      obtain h3 := h1 h2
      rw [List.singleton_append]
      rw [WordToNat_append]
      rw [h3]
      by_cases h4 : n % 2 == 1
      repeat' grind

omit [DecidableEq G] [Finite G] [Nontrivial G] [IsCyclic G] in theorem GroupEltEncodingIsCorrect : ∀ (g : G), WordToGroupElt G (GroupEltEncoding G g) = g := by
  intro g
  simp only [GroupEltEncoding, WordToGroupElt, ReverseGroupEltEnumeration]
  have h1 : WordToNat (NatToWord (GroupEltEnumeration G g)) = (GroupEltEnumeration G g) := by grind
  simp only [h1]
  simp

@[grind.]
theorem NatEncodingIsEfficient : ∀ (m : ℕ), ∀ n ≥ 0, m < 2^n → (NatToWord m).length ≤ n + 1 := by
  intro m n hn h
  induction n generalizing m with
  | zero => grind
  | succ m1 ih =>
    unfold NatToWord
    split
    · grind
    · have h2 : m1 ≥ 0 := by grind
      have h3 : m/2 < 2^m1 := by grind
      obtain h4 := ih (m/2) h2 h3
      rw [List.length_append]
      grind

omit [∀ (n : ℕ), DecidableEq (Gf n)] [∀ (n : ℕ), Finite (Gf n)] [∀ (n : ℕ), Nontrivial (Gf n)] [∀ (n : ℕ), Group (Gf n)] [∀ (n : ℕ), IsCyclic (Gf n)] in theorem GroupEncodingIsEfficient : ∀ (m : ℕ), ∀ n ≥ 0, Fintype.card (Gf m) < 2^n → ∀ (g : Gf m), (GroupEltEncoding (Gf m) g).length ≤ n + 1 := by
  unfold GroupEltEncoding
  intro m n hn hg g
  have h : (GroupEltEnumeration (Gf m) g) < 2^n := by grind
  apply NatEncodingIsEfficient (GroupEltEnumeration (Gf m) g) n hn h

end GroupFamily
