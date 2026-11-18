import Project.ProjectLib
/-
  Formalizes sampling from the uniform distribution on a finite set.
  I am trying to avoid measure theory because it is very hard to argue about.
  Partially adapted from https://github.com/zkcrypto/cryptolib/blob/main/Cryptolib/Fundamentals/Uniform.lean
-/

variable (G : Type*) [Fintype G] [Nonempty G] [Group G]

noncomputable section


def uniform_nat (n : ℕ) [NeZero n] : PMF (Fin n) :=
  PMF.uniformOfFintype (Fin n)

def uniform_group : PMF G :=
  PMF.uniformOfFintype G

def uniform_zmodn (n : ℕ) [NeZero n] : PMF (ZMod n) :=
  uniform_group (ZMod n)

def uniform_bit : PMF Bool :=
  PMF.uniformOfFintype Bool

/- gets around fintype issue with bitvec -/
def uniform_BitVec (n : ℕ): PMF (BitVec n) :=
   (uniform_nat (2^n)).map (fun (x : Fin (2^n)) => BitVec.ofNatLT x (Fin.isLt x))


theorem uniform_bit_is_uniform : ∀ (b : Bool),
  (uniform_bit) b = 1/2 := by
  intro b
  rw [uniform_bit, PMF.uniformOfFintype_apply]
  simp_all

theorem uniform_nat_is_uniform : ∀ (n : ℕ) [NeZero n], ∀ (v : Fin (n)),
  (uniform_nat n) v = 1/n := by
  intro n nz v
  rw [uniform_nat, PMF.uniformOfFintype_apply]
  simp_all

omit [Group G] in theorem uniform_group_is_uniform : ∀ (g : G),
  (uniform_group G) g = 1/Fintype.card G := by
  intro g
  rw [uniform_group, PMF.uniformOfFintype_apply]
  simp_all

theorem uniform_BitVec_is_uniform : ∀ (n : ℕ), ∀ (v : BitVec n),
  (uniform_BitVec n) v = 1/(2^n) := by
  intro n v
  rw [uniform_BitVec, uniform_nat]
  simp_all
  have h : (∑ a, if v = { toFin := a } then ((2 ^ n)⁻¹ : ENNReal) else 0) = (∑ a ∈ {a | v = { toFin := a }}, ((2 ^ n)⁻¹ : ENNReal)) := by
    exact Eq.symm (Finset.sum_filter (fun a ↦ v = { toFin := a }) fun a ↦ ((2 ^ n)⁻¹ : ENNReal))
  rw [h]
  simp
  have h1 : Finset.card {a | v = { toFin := a }} = 1 := by
    apply Finset.card_eq_one_iff_existsUnique.mpr
    simp
    exists v.toFin
    simp_all
  simp_all
