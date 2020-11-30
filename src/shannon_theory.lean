import algebra.big_operators
import analysis.special_functions.exp_log

import rnd_var

---- SHANNON ENTROPY 

open finset rnd_var

open_locale big_operators  -- this enables the notation

universe x

variables 
{ι : Type x} -- indexing type
[fintype ι] -- tell Lean that the set of all elements ι is finite.

noncomputable theory

/--
Definition: Shannon entropy. 
-/
def Shannon_entropy (X : ι → ℝ) [rnd_var X] : ℝ := 
- ∑ i, (X i) * real.log(X i)

-- notation `H(`X`)` := Shannon_entropy X

/--
Theorem (non-negativity): Shannon entropy is non-negative for 
any discrete random variable.
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
    intros i hi,
    exact H2 i,
end

/--
def delta i j
-/

/--
Theorem (Minimum value): Shannon entropy vanishes if and only if 
X is a deterministic variable.

This is property 10.1.4 here (https://arxiv.org/pdf/1106.1445.pdf)
-/
theorem Shannon_entropy_zero_iff_deterministic (X : ι → ℝ) [rnd_var X] : 
Shannon_entropy X = 0 ↔ is_deterministic X :=
begin
    -- we begin by asking Lean to provide the meanings of the 
    -- words we've taught it. We use the rewrite tactic for that.
    rw [is_deterministic, Shannon_entropy],
    -- We split the two directions of the iff.
    split,
    {
        -- we prove one direction
        intro Hm,
        -- remove the minus sign
        have H : ∑ (i : ι), X i * real.log(X i) = 0,
        { linarith, },
        -- show that each term must be zero
        -- this has to be a lemma already: sum_of_nonneg_eq_zero or something
        have H' : ∀ (i : ι), X i * real.log(X i) = 0,
        { sorry, },
        -- since each term is a product, at least one of the factors must be zero
        have H'' : ∀ (i : ι), (X i = 0) ∨ (real.log(X i) = 0),
        { intros,
          specialize H' i,
          exact eq_zero_or_eq_zero_of_mul_eq_zero H', },
        -- stuck here with
        -- H'' : ∀ (i : ι), X i = 0 ∨ real.log (X i) = 0
        -- goal : ∃ (j : ι), ∀ (i : ι), ite (i = j) (X i = 1) (X i = 0)
        -- I feel like I want to do case analysis on i because the two terms in H''
        -- exactly match the if/else condition in the goal, but I don't know how to state it
        have helper : ∀ (r : ℝ), real.log(r) = 0 → r = 1, {rw real.log_one, }, -- Yeah!
        have H''' : ∀ (i : ι), X i = 0 ∨ X i = 1, {sorry},
        -- Hmmm, and now it should be easy but I don't know the syntax.
        -- Let me ask around and tell you in the next session.
        sorry,
    },
    {
        -- we prove the other direction
        intro H,
        cases H with j hj,
        calc -∑ (i : ι), (X i) * real.log(X i)         : {by rw is_deterministic}
        -- I think it'd make sense to define the delta to make notation clearer
        -- otherwise the definition of a deterministic random variable contains an existential quantifier that I don't know how to handle. Will look into it tonight.
        -- I also feel we need the use tactic at some point, because otherwise the variable j is going to be undefined
        -- So we can set e.g. j=0 and show it works in that case and we're done
        ... = -∑ (i : ι), (δ i j) * real.log(δ i j)      : {by rw kronecker_delta}
        ... = -∑ (i : ι), (if (i = j) then (1*real.log(1)) else (0*real.log(0)))     : {}
        ... = 0
        sorry
    },
end

/--
Theorem: The Shannon entropy of a uniform 
random variable is log(n).
-/
theorem Shannon_entropy_of_uniform (X : ι → ℝ) [rnd_var X] : 
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