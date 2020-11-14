import algebra.big_operators
import linear_algebra.basic
import analysis.special_functions.exp_log

import rnd_var

---- SHANNON ENTROPY 

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
    simp only [← mul_neg_eq_neg_mul_symm, ← finset.sum_neg_distrib],
    -- each term in the sum is nonnegative
    have H2 : ∀ i ∈ s, - (X i) * real.log(X i) ≥ 0, {
        intros,
        have h : - (X i) * real.log(X i) = (X i) * (- real.log(X i)), by linarith,
        rw h,
        apply mul_nonneg,
        {   
            apply probs_nonneg_of_rnd_var i H,
            assumption,
        },
        {
            rw neg_nonneg,
            apply real.log_nonpos,
            {
                apply probs_nonneg_of_rnd_var i H,
                assumption,
            },
            {exact Xᵢ_le_1 i H},
        },
    },
    -- so we have that the whole sum is nonneg
    apply finset.sum_nonneg,
    simp only [neg_mul_eq_neg_mul_symm, ge_iff_le, mul_neg_eq_neg_mul_symm, neg_nonneg] at *,
    exact H2,
end

section
open_locale classical

/--
Definition (deterministic random variable): 
-/
def is_deterministic (s : finset ι) (X : ι → ℝ) [rnd_var s X] : Prop := 
∃ j ∈ s, ∀ i ∈ s, if (i = j) then (X i = 1) else (X i = 0)  

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
Definition (uniform random variable): a random variable
whose  probabilities are equal to 1/n, where n 
is the number of symbols that the random variable 
can assume.
-/
def is_uniform (s : finset ι) (X : ι → ℝ) [rnd_var s X] : Prop :=
(∀ i ∈ s, X i = 1 / s.card)

/--
Theorem: The Shannon entropy of a uniform 
random variable is log(n).
-/
theorem Shnn_entropy_uniform_rdm_var (s : finset ι) (X : ι → ℝ) [rnd_var s X] : 
is_uniform s X → Shannon_entropy s X = real.log(s.card)
:=
begin
    intro hX₃,
    rw Shannon_entropy,
    have : -∑ i in s, X i * real.log (X i) = ∑ i in s, X i * real.log (1 / (X i)) ,
        by simp only [one_div, real.log_inv, mul_neg_eq_neg_mul_symm, finset.sum_neg_distrib],
    rw this,
    clear this,
    rw is_uniform at hX₃,
    -- we need to subsitute 1 / s.card for  (X i).
    sorry
end