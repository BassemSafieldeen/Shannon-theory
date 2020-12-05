import analysis.special_functions.exp_log

namespace real

lemma one_of_log_zero_of_pos : ∀ (r : ℝ), 0 < r → real.log(r) = 0 → r = 1 :=
begin
  intros r hr1 hr2,
  calc r = exp(log(r))  : by exact (exp_log hr1).symm
  ... = exp(0)          : by rw hr2
  ... = 1               : by rw exp_zero,
end

lemma log_inv_nonneg : ∀ (r : ℝ), 0 ≤ r → r ≤ 1 → 0 ≤ log(r⁻¹) :=
begin
  intros r hr,
  norm_num at *,
  apply log_nonpos hr,
end

lemma r_neq_zero_one : ∀ (r : ℝ), r ≠ 0 ∧ r ≠ 1 → r < 0 ∨ (0 < r ∧ r < 1) ∨ 1 < r :=
begin
  intros r hr,
  by_contradiction,
  push_neg at h,
  cases h with r0 hright,
  cases hright with r01 r1,
  finish,
end

lemma zero_or_one_of_log_zero : ∀ (r : ℝ), log(r) = 0 → r = 0 ∨ r = 1 :=
begin
  intro r,
  contrapose,
  push_neg,
  intro h,
  cases h,
  have h' : r < 0 ∨ 0 < r ∧ r < 1 ∨ 1 < r, 
  {
    apply r_neq_zero_one,
    split, exact h_left, exact h_right,
  },
  cases h',
  sorry, -- real.log_pos and real.log_neg_eq_log
  cases h',
  cases h',
  by_contradiction,
  norm_num at h,
  have h'' : log r < 0, by exact log_neg h'_left h'_right,
  linarith,
  by_contradiction,
  push_neg at h,
  have h' : log r > 0, by exact log_pos h',
  linarith,
end

end real