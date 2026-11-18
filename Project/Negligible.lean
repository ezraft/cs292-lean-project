import Project.ProjectLib


/-
  Formalizes negligible functions. Previous implementations are difficult to work with, so I made my own version which I feel is simpler.
  For example, the other implementers had difficulty formalizing the last fact (inverse exponential is negligible), but I was able to do it.
-/

def negligible (f : ℕ → ℝ) :=
  ∀ ε > 0, ∀ c > 0, ∃ n₀ : ℕ, n₀ > 0 ∧ ∀ n ≥ n₀, |(f n)/((n : Real)^c)| < ε

theorem zero_is_negl : negligible (fun _ => 0) := by
  unfold negligible
  simp_all
  intro h1 h2 h3 h4
  exists 1

theorem negl_additive {f₁ f₂} : negligible f₁ → negligible f₂ → negligible (f₁ + f₂) := by
  unfold negligible
  intro h1 h2
  simp [abs_div] at *
  intro ε hε c hc
  have hε1 : ε/2 > 0 := by nlinarith
  obtain ⟨n1, hnp1, hn1⟩ := h1 (ε/2) hε1 c hc
  obtain ⟨n2, hnp2, hn2⟩ := h2 (ε/2) hε1 c hc
  exists n1 + n2
  constructor
  · lia
  · intro n hn
    have hnpos : ↑n > (0 : ℝ) := by
      simp_all
      lia
    have pow_neq_zero : (0 : ℝ) < (↑n ^ c) := by
      apply pow_pos hnpos c
    have h3 : |f₁ n + f₂ n| ≤ |f₁ n| + |f₂ n| := by
      exact abs_add_le (f₁ n) (f₂ n)
    have h4 : |f₁ n + f₂ n|/(↑n ^ c) ≤ (|f₁ n| + |f₂ n|)/(↑n ^ c) := by
      apply (div_le_div_iff_of_pos_right pow_neq_zero).mpr h3
    have h5 : |f₁ n + f₂ n| / (↑n ^ c) ≤ |f₁ n|/(↑n ^ c) + |f₂ n| /(↑n ^ c) := by grind
    grind

theorem const_multiple_negl {f₁} {c₁ : ℝ} : c₁ > 0 → negligible f₁ → negligible (fun n => c₁ * (f₁ n)) := by
  unfold negligible
  intro h1 h2
  simp [abs_div] at *
  intro ε hε c hc
  have hε1 : ε/|c₁| > 0 := by
    simp_all
    exact ne_of_gt h1
  obtain ⟨n1, hnp1, hn1⟩ := h2 (ε/|c₁|) hε1 c hc
  exists n1
  constructor
  · lia
  · intro n hn
    obtain ha := hn1 n hn
    have hnpos : ↑n > (0 : ℝ) := by
      simp_all
      lia
    have pow_neq_zero : (0 : ℝ) < (↑n ^ c) := by
      apply pow_pos hnpos c
    have hcn : |c₁| = c₁ := by
      exact abs_of_pos h1
    have h3 : |c₁| * |f₁ n| / (↑n ^ c) / |c₁| < ε / |c₁| := by
      rw [div_div, mul_comm, div_mul_eq_div_div_swap, mul_div_assoc, div_self]
      simp
      exact RCLike.ofReal_lt_ofReal.mp (hn1 n hn)
      rw [hcn]
      linarith
    rw [← hcn] at h1
    exact (div_lt_div_iff_of_pos_right h1).1 h3

theorem inv_exp_is_negl : negligible (fun n => Real.exp (-n)) := by
  unfold negligible
  simp [abs_div] at *
  intro ε hε c hc
  by_cases h1 : ε < 1
  · exists Nat.ceil (-Real.log ε) + 1
    simp_all
    intro n hn
    have h5: Real.log ε < 0 := by exact Real.log_neg hε h1
    have h6 : n > 0 := by grind
    have h9 : (1 : ℝ) ≤ ↑n := by
      simp_all
      grind
    have h2 : -Real.log ε < n := by exact Nat.lt_of_ceil_lt hn
    have h3 : Real.log ε > -n := by exact neg_lt_of_neg_lt h2
    have h4 : (0 : ℝ) < ↑n^c := by simp_all
    have h8 : (1 : ℝ) ≤ ↑n^c := by apply one_le_pow₀ h9
    have h7 : Real.exp (-↑n) < ε := by exact (Real.lt_log_iff_exp_lt hε).mp h3
    have h9 : ε ≤ ε * (↑n^c) := by simp_all
    have h10 : Real.exp (-↑n) < ε * (↑n^c) := by grind
    apply (div_lt_iff₀ h4).mpr h10
  · exists 2
    simp_all
    intro n hn
    have h6 : n > 0 := by grind
    have h9 : (1 : ℝ) ≤ ↑n := by
      simp_all
      grind
    have h4 : (0 : ℝ) < ↑n^c := by simp_all
    have h8 : (1 : ℝ) ≤ ↑n^c := by apply one_le_pow₀ h9
    have h10 : Real.exp (-↑n) < 1 := by simp_all
    have h11 : ε * (↑n^c) ≥ 1 := by exact one_le_mul_of_one_le_of_one_le h1 h8
    apply (div_lt_iff₀ h4).mpr
    grind
