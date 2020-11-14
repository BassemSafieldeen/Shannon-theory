import algebra.big_operators
import linear_algebra.basic
import analysis.special_functions.exp_log

import rnd_var

---- SHANNON ENTROPY 

open finset rnd_var

open_locale big_operators  -- this enables the notation

universe x

variables {ι : Type x} [fintype ι] -- indexing type

noncomputable theory

/--
Definition: Shannon entropy. 
-/
def Shannon_entropy (X : ι → ℝ) [rnd_var X] : ℝ := 
- ∑ i, (X i) * real.log(X i)

-- notation `H(`X`)` := Shannon_entropy X

/--
Theorem (non-negativity): Shannon entropy is non-negative for 
any random variable.
-/
theorem Shannon_entropy_nonneg (X : ι → ℝ) [rnd_var X] : 
Shannon_entropy X ≥ 0 := 
begin
    intros,
    rw Shannon_entropy,
    -- move the minus inside
    simp only [← mul_neg_eq_neg_mul_symm, ← sum_neg_distrib],
    -- each term in the sum is nonnegative
    have H2 : ∀ i, - (X i) * real.log(X i) ≥ 0, {
        intros,
        have h : - (X i) * real.log(X i) = (X i) * (- real.log(X i)), by linarith,
        rw h,
        apply mul_nonneg,
        {apply probs_nonneg},
        {
            rw neg_nonneg,
            apply real.log_nonpos,
            {apply probs_nonneg},
            {apply probs_le_one},
        },
    },
    -- so we have that the whole sum is nonneg
    apply sum_nonneg,
    simp only [neg_mul_eq_neg_mul_symm, ge_iff_le, mul_neg_eq_neg_mul_symm, neg_nonneg] at *,
    -- exact H2,
    intros i hi,
    exact H2 i,
end

/--
Theorem (Minimum value): Shannon entropy vanishes if and only if 
X is a deterministic variable.

This is property 10.1.4 here (https://arxiv.org/pdf/1106.1445.pdf)
-/
theorem Shannon_entropy_minimum_value (X : ι → ℝ) [rnd_var X] : 
Shannon_entropy X = 0 ↔ is_deterministic X :=
begin
    sorry
end

/--
Theorem: The Shannon entropy of a uniform 
random variable is log(n).
-/
theorem Shnn_entropy_uniform_rdm_var (X : ι → ℝ) [rnd_var X] : 
is_uniform X → Shannon_entropy X = real.log(fintype.card ι) :=
begin
    intro hX,
    rw Shannon_entropy,
    have : - ∑ i, X i * real.log (X i) = ∑ i, X i * real.log (1 / (X i)) ,
        by simp only [one_div, real.log_inv, mul_neg_eq_neg_mul_symm, sum_neg_distrib],
    rw is_uniform at hX,
    -- we need to subsitute 1 / fintype.card ι for (X i).
    sorry
end