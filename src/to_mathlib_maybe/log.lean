import analysis.special_functions.exp_log

namespace real

lemma one_of_log_zero_of_pos : ∀ (r : ℝ), 0 < r → real.log(r) = 0 → r = 1 :=
begin
  intros r hr1 hr2,
  calc r = exp(log(r))  : by exact (exp_log hr1).symm
  ... = exp(0)          : by rw hr2
  ... = 1               : by rw exp_zero,
end

lemma zero_or_one_of_log_zero_if_nonneg : ∀ (r : ℝ), 0 ≤ r → log(r) = 0 → r = 0 ∨ r = 1 :=
begin
  intros r hr logr,
  replace hr := le_iff_lt_or_eq.mp hr,
  cases hr with r1 r0,
  right,
  exact one_of_log_zero_of_pos r r1 logr,
  left,
  linarith,
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

lemma zero_or_pm_one_of_log_zero : ∀ (r : ℝ), log(r) = 0 → r = -1 ∨ r = 0 ∨ r = 1 :=
begin
  intros r log0,
  -- case r < 0
  have r_sign : r < 0 ∨ 0 ≤ r, {by exact lt_or_ge r 0,},
  cases r_sign with r_neg r_nonneg,
  rw ← log_neg_eq_log at log0,
  have r_sign' : 0 ≤ -r, {by linarith,},
  have h' : -r = 0 ∨ -r = 1, {by exact zero_or_one_of_log_zero_if_nonneg (-r) r_sign' log0,},
  left,
  cases h' with r0 r1,
  exfalso,
  linarith,
  linarith,
  -- case r ≥ 0, proved by zero_or_one_of_log_zero_if_nonneg
  right,
  exact zero_or_one_of_log_zero_if_nonneg r r_nonneg log0,
end

end real