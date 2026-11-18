import Project.ProjectLib
import Project.Uniform
import Project.Negligible
/-
  Formalizes Public Key Encryption.
  security: for all messages m₀, m₁, |Pr[A outputs 1 given Enc(m₀)] - Pr[A outputs 1 given Enc(m₁)]| < negl(λ)
-/

open Cslib Cslib.Probability Cslib.Crypto

variable (Message PublicKey SecretKey Ciphertext : Type*)

abbrev Adversary := ℕ → Word → ProbComp Bool


structure PPTAdversary where
  adv: Adversary
  adv_ppt: IsPPT boolEncoding adv


structure PKEScheme where
  gen: ℕ → PMF (PublicKey × SecretKey)
  enc: ℕ → (pk : PublicKey) → (m : Message) → PMF Ciphertext
  dec : ℕ → (sk : SecretKey) → (ct : Ciphertext) → Message
  correct: ∀ (n : ℕ), ∀ pk sk, (pk,sk) ∈ (gen n).support → ∀ message ct,
    ct ∈ (enc n pk message).support → dec n sk ct = message


/- Restricting to encryption schemes which encrypt a singular bit.
   This in practice is as powerful as encrypting a full message, and it makes the proofs easier. -/

noncomputable def real_experiment (pke : PKEScheme Bool Word Word Word) (n : ℕ) (m₀ : Bool) (m₁ : Bool) (a : Adversary): ProbComp Bool := do
    let keys ← OracleComp.sample (pke.gen n) /- public key, secret key -/
    let ct₀ ← OracleComp.sample (pke.enc n keys.1 m₀)
    let ct₁ ← OracleComp.sample (pke.enc n keys.1 m₁)
    let rand_bit ← OracleComp.sample uniform_bit
    if rand_bit = False then a n ct₀ else a n ct₁

noncomputable def ideal_experiment (_ : PKEScheme Bool Word Word Word) (n : ℕ) (_ : Bool) (_ : Bool) (a : Adversary) : ProbComp Bool := do
    let ct ← (OracleComp.sample (uniformBits n))
    a n ct


def GenPolynomial (pke : PKEScheme Bool Word Word Word) :=
  ∃ c > 0, ∃ C > 0, ∀ (n : ℕ), ∀ pk sk, (pk,sk) ∈ (pke.gen n).support → pk.length ≤ C * n^c ∧ sk.length ≤ C * n^c

def EncPolynomial (pke : PKEScheme Bool Word Word Word) :=
  ∃ c > 0, ∃ C > 0, ∀ (n : ℕ), ∀ pk sk, (pk,sk) ∈ (pke.gen n).support → ∀ (m : Bool), ∀ ct ∈ (pke.enc n pk m).support, ct.length ≤ C * n^c

def AdmissiblePKEScheme (pke : PKEScheme Bool Word Word Word) :=
  GenPolynomial pke ∧ EncPolynomial pke

def Secure (pke : PKEScheme Bool Word Word Word) (_ : AdmissiblePKEScheme pke):=
  ∀ (n : ℕ) (a : PPTAdversary) (m₀ : Bool) (m₁ : Bool),
    ∃ (ε : ℕ → ℝ) (_ : negligible ε), advantage (real_experiment pke n m₀ m₁ a.adv) (ideal_experiment pke n m₀ m₁ a.adv) ≤ ε n
