import Project.ProjectLib
import Cslib.Init
import Cslib.Crypto.Computational.Basic
import Cslib.Probability.BitString
import Cslib.Computability.Probabilistic.PPT
import Cslib.Languages.Probabilistic.Basic
import Cslib.Probability.PMF
import Cslib.Crypto.Game
import Project.Uniform
import Project.Negligible
import Project.PKE
/-
  Proves that the existence of public key encryption implies the existence of one way functions.
  Mostly a sanity check to determine that PKE is implemented correctly.
-/

open Cslib Cslib.Probability Cslib.Crypto

abbrev Inverter := ℕ → Word → ProbComp Word

structure PPTInverter where
  inv: Inverter
  inv_ppt: IsPPT wordEncoding inv



def OneWay (f : ℕ → Word → Word) :=
  ∀ (n : ℕ) (a : PPTInverter),
    ∃ (ε : ℕ → ℝ) (_ : negligible ε),  ≤ ε n


theorem PKEImpliesOWF :=
  ∃ (pke : PKEScheme Bool Word Word Word) (admissible : AdmissiblePKEScheme pke), (Secure pke admissible) → ∃ f, OneWay f
