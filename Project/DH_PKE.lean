import Project.ProjectLib
import Project.Uniform
import Project.Negligible
import Project.PKE
import Project.GroupFamily
import Project.DDH

/-
  A construction of public key encryption from the DDH assumption.
-/

open Cslib Cslib.Probability Cslib.Crypto GroupFamily

variable (Gf : GroupFamily) [∀ n, DecidableEq (Gf n)] [∀ n, Group (Gf n)] [∀ n, Finite (Gf n)] [∀ n, Nontrivial (Gf n)] [∀ n, IsCyclic (Gf n)] [∀ n, Fintype (Gf n)] (prime_order : ∀ n, Prime (Fintype.ofFinite (Gf n)).card) (poly_size : ∃ C > 0, ∃ c > 0, ∀ n, (Fintype.ofFinite (Gf n)).card ≤ C * n^c)

@[grind., simp]
noncomputable def DDHGen (n : ℕ) : PMF (Word × Word) :=
  let G := Gf n
  let p := Fintype.card G

  let nontriv := Nontrivial G
  have h : Nonempty (nonTrivElts G) := by
    expose_names
    obtain h2 :=  G
    obtain ⟨x, y, hxy⟩ := nontrivial_iff.mp (inst_3 n)
    simp_all
    simp [nonTrivElts]
    by_cases h3: x = 1
    · exists y
      rw [eq_comm]
      simp_all
    · exists x
  (PMF.uniformOfFintype ((nonTrivElts G) × (Fin p))).map
    (fun ((g, a) : ((nonTrivElts G) × (Fin p))) =>
    (GroupProductEncoding G (g, g^(Fin.val a)), NatToWord (Fin.val a)))

@[grind., simp]
noncomputable def DDHEnc (n : ℕ) (pk_word : Word) (m : Bool) : PMF (Word) :=
  let G := Gf n
  let pk := WordToGroupElt (G × G) pk_word
  let p := Fintype.card G

  let (g, ga) := pk
  if m = False then
    (PMF.uniformOfFintype (Fin p)).map
    (fun (b : Fin p) => GroupProductEncoding G (g^(Fin.val b), ga^(Fin.val b)))
  else
    (PMF.uniformOfFintype (Fin p)).map
    (fun (b : Fin p) => GroupProductEncoding G (g^(Fin.val b), g * ga^(Fin.val b)))

@[grind., simp]
noncomputable def DDHDec (n : ℕ) (sk_word : Word) (ct_word : Word) : Bool :=
  let G := Gf n
  let sk := WordToNat sk_word
  let ct := WordToGroupElt (G × G) ct_word
  let (gb, gabct) := ct
  ((gabct)/(gb^sk)) ≠ (1 : G)

omit [∀ (n : ℕ), Finite (Gf n)] [∀ (n : ℕ), IsCyclic (Gf n)] in lemma DDHCorrect : ∀ (n : ℕ), ∀ pk sk, (pk,sk) ∈ (DDHGen Gf n).support → ∀ (m : Bool) (ct : Word),
    ct ∈ (DDHEnc Gf n pk m).support → DDHDec Gf n sk ct = m := by
      intro n
      let G := Gf n
      let p := Fintype.card G

      intro pk sk h1 m ct h2
      unfold DDHGen at h1
      simp at h1
      obtain ⟨g,gh,a,h3,h4⟩ := h1
      simp only [DDHDec]
      unfold DDHEnc at h2
      simp only [eq_iff_iff, iff_false, Bool.not_eq_true, PMF.mem_support_iff, ne_eq] at h2
      split at h2
      · simp only [PMF.map_apply, PMF.uniformOfFintype_apply, Fintype.card_fin, tsum_fintype, Finset.sum_eq_zero_iff, Finset.mem_univ,
        ite_eq_right_iff, ENNReal.inv_eq_zero, ENNReal.natCast_ne_top, imp_false, forall_const, not_forall,
        Decidable.not_not] at h2
        obtain ⟨b, h6⟩ := h2
        rw [eq_comm] at h3
        rw [h3] at h6
        simp only [GroupProductEncoding] at h6
        repeat' rw [GroupEltEncodingIsCorrect (G × G)] at h6
        simp only at h6
        rw [h6]
        repeat' rw [GroupEltEncodingIsCorrect (G × G)]
        rw [← h4]
        have h7 : (g ^ (Int.ofNat a.toNat)) ^ (Int.ofNat b.toNat) = (g ^ (Int.ofNat b.toNat)) ^ (Int.ofNat a.toNat) := by
          exact zpow_comm g (Int.ofNat a.toNat) (Int.ofNat b.toNat)

        have h8 : (g ^ (Int.ofNat a.toNat)) ^ (Int.ofNat b.toNat) / (g ^ (Int.ofNat b.toNat)) ^ (Int.ofNat a.toNat) = (1 : G) := by
          exact div_eq_one_of_eq h7

        rw [NatEncodingIsCorrect]
        rename_i m_F
        rw [m_F]
        simp_all
      · simp only [PMF.map_apply, PMF.uniformOfFintype_apply, Fintype.card_fin, tsum_fintype, Finset.sum_eq_zero_iff, Finset.mem_univ,
        ite_eq_right_iff, ENNReal.inv_eq_zero, ENNReal.natCast_ne_top, imp_false, forall_const, not_forall,
        Decidable.not_not] at h2
        obtain ⟨b, h6⟩ := h2
        rw [eq_comm] at h3
        rw [h3] at h6
        simp only [GroupProductEncoding] at h6
        repeat' rw [GroupEltEncodingIsCorrect (G × G)] at h6
        simp only at h6
        rw [h6]
        repeat' rw [GroupEltEncodingIsCorrect (G × G)]
        rw [← h4]
        have h7 : (g ^ (Int.ofNat a.toNat)) ^ (Int.ofNat b.toNat) = (g ^ (Int.ofNat b.toNat)) ^ (Int.ofNat a.toNat) := by
          exact zpow_comm g (Int.ofNat a.toNat) (Int.ofNat b.toNat)

        have h8 : (g ^ (Int.ofNat a.toNat)) ^ (Int.ofNat b.toNat) / (g ^ (Int.ofNat b.toNat)) ^ (Int.ofNat a.toNat) = (1 : G) := by
          exact div_eq_one_of_eq h7

        rw [NatEncodingIsCorrect]
        rename_i m_T
        simp at m_T
        rw [m_T]
        simp [nonTrivElts] at gh
        simp_all

noncomputable def DDH_PKE : PKEScheme Bool Word Word Word :=
  PKEScheme.mk (DDHGen Gf) (DDHEnc Gf) (DDHDec Gf) (DDHCorrect Gf)

theorem DDHGenPolynomial (exp_size : ∃ c > 0, ∀ n, (Fintype.ofFinite (Gf n)).card ≤ c^n) : GenPolynomial (DDH_PKE Gf) := by
  unfold GenPolynomial
  obtain ⟨c1, hc1, hn⟩ := exp_size
  unfold DDH_PKE
  simp only
  sorry
