import algebra.big_operators
import linear_algebra.basic
import analysis.special_functions.exp_log

import rnd_var

---- SHANNON ENTROPY 

open finset rnd_var

open_locale big_operators  -- this enables the notation

universe x

variables {ι : Type x} -- indexing type

noncomputable theory

/--
Definition: Shannon entropy. 
-/
def Shannon_entropy (s : finset ι) (X : ι → ℝ) [rnd_var s X] : ℝ := 
- ∑ i in s, (X i) * real.log(X i)

-- notation `H(`X`)` := Shannon_entropy X

/--
Theorem (non-negativity): Shannon entropy is non-negative for 
any random variable.
-/
theorem Shannon_entropy_nonneg (s : finset ι) (X : ι → ℝ) [rnd_var s X] : 
Shannon_entropy s X ≥ 0 := 
begin
    intros,
    rw Shannon_entropy,
    -- move the minus inside
    simp only [← mul_neg_eq_neg_mul_symm, ← sum_neg_distrib],
    -- each term in the sum is nonnegative
    have H2 : ∀ i ∈ s, - (X i) * real.log(X i) ≥ 0, {
        intros,
        have h : - (X i) * real.log(X i) = (X i) * (- real.log(X i)), by linarith,
        rw h,
        apply mul_nonneg,
        {apply probs_nonneg i H, assumption},
        {
            rw neg_nonneg,
            apply real.log_nonpos,
            {apply probs_nonneg i H, assumption},
            {exact probs_le_one i H},
        },
    },
    -- so we have that the whole sum is nonneg
    apply sum_nonneg,
    simp only [neg_mul_eq_neg_mul_symm, ge_iff_le, mul_neg_eq_neg_mul_symm, neg_nonneg] at *,
    exact H2,
end

/--
Theorem (Minimum value): Shannon entropy vanishes if and only if 
X is a deterministic variable.

This is property 10.1.4 here (https://arxiv.org/pdf/1106.1445.pdf)
-/
theorem Shannon_entropy_minimum_value (s : finset ι) (X : ι → ℝ) [rnd_var s X] : 
Shannon_entropy s X = 0 ↔ is_deterministic s X :=
begin
    sorry
end

/--
Theorem: The Shannon entropy of a uniform 
random variable is log(n).
-/
theorem Shnn_entropy_uniform_rdm_var (s : finset ι) (X : ι → ℝ) [rnd_var s X] : 
is_uniform s X → Shannon_entropy s X = real.log(s.card) :=
begin
    intro hX,
    rw Shannon_entropy,
    have : -∑ i in s, X i * real.log (X i) = ∑ i in s, X i * real.log (1 / (X i)) ,
        by simp only [one_div, real.log_inv, mul_neg_eq_neg_mul_symm, sum_neg_distrib],
    rw this,
    clear this,
    rw is_uniform at hX,
    -- we need to subsitute 1 / s.card for  (X i).
    sorry
end