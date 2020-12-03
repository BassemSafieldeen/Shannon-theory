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

lemma sum_nonneg_zero {f : ι → ℝ} (hf1 : ∑ i, f i = 0) (hf2: ∀ i, 0 ≤ f i) : 
∀ i, f i = 0 :=
begin
    -- intro i,
    -- specialize hf2 i,
    -- split h' into branches f i = 0 and f i > 0
    -- first one follows from sum_const_zero
    -- second one leads to contradiction, so `exfalso` + something
    -- exact sum_eq_zero_iff.mp hf1,
    -- exact (sum_eq_zero_iff_of_nonneg hf2).mp hf1,  -- why doesn't this work?
    sorry,
end

lemma helper : ∀ (r : ℝ), 0 < r → real.log(r) = 0 → r = 1 :=
begin
    intros r hr1 hr2,
    calc r = real.exp(real.log(r))  : by exact (real.exp_log hr1).symm
    ... = real.exp(0)               : by rw hr2
    ... = 1                         : by rw real.exp_zero,
end

lemma r_neq_zero_one : ∀ r : ℝ, r ≠ 0 ∧ r ≠ 1 → r < 0 ∨ (0 < r ∧ r < 1) ∨ 1 < r :=
begin
    intros r hr,
    by_contradiction,
    push_neg at h,
    cases h with r0 hright,
    cases hright with r01 r1,
    finish,
end

lemma helper' : ∀ (r : ℝ), real.log(r) = 0 → r = 0 ∨ r = 1 :=
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
    have h'' : real.log r < 0, {exact real.log_neg h'_left h'_right,},
    linarith,
    by_contradiction,
    push_neg at h,
    have h' : real.log r > 0, by exact real.log_pos h',
    linarith,
end

lemma helper2 : ∀ (r : ℝ), r⁻¹ = 1 → r = 1 := by exact λ {g : ℝ}, inv_eq_one'.mp

lemma log_nonneg : ∀ (r : ℝ), 0 ≤ r → r ≤ 1 → 0 ≤ real.log(r⁻¹) :=
begin
    intros r hr,
    norm_num at *,
    apply real.log_nonpos,
    exact hr,
end

lemma helper3 (X : ι → ℝ) (h : ∑ i, X i = 1) [decidable_eq ι] : 
(∀ i, X i = 0 ∨ X i = 1) 
→ 
(∃ j, ∀ i, if (i = j) then (X i = 1) else (X i = 0)) := 
begin
    intros hX,
    sorry
end

lemma test : (1 : ℝ) / 0 > 1 := 
begin
    ring,
    sorry
end

#check (1 : ℝ)/0

lemma helper4 (X : ι → ℝ) : 
(∀ (i : ι), X i = 0 ∨ X i = 1) → (∀ (i : ι), X i = 0 ∨ real.log(X i) = 0) :=
begin
    intros hi i,
    specialize hi i,
    cases hi with x0 log0,
    left,
    exact x0,
    right,
    rw log0,
    exact real.log_one,
end

lemma helper5 {X : ι → ℝ} [decidable_eq ι] : 
(∃ j, ∀ i, ite (i = j) (X i = 1) (X i = 0)) → (∀ i, X i = 0 ∨ X i = 1) := 
begin
    contrapose,
    intro h,
    push_neg,
    push_neg at h,
    cases h with i hi,
    cases hi,
    intro j,
    use i,
    split_ifs,
    exact hi_right,
    exact hi_left,
end

lemma helper6 {X : ι → ℝ} :
(∀ i, (X i) = 0 ∨ (X i) = 1) → (∀ i, (X i)⁻¹ > 1 ∨ (X i)⁻¹ = 1) := 
begin
    sorry
end

/--
Theorem (Minimum value): Shannon entropy vanishes if and only if 
X is a deterministic variable.

This is property 10.1.4 here (https://arxiv.org/pdf/1106.1445.pdf)
-/
theorem Shannon_entropy_zero_iff_deterministic (X : ι → ℝ) [rnd_var X] [decidable_eq ι] : 
Shannon_entropy X = 0 ↔ is_deterministic X :=
begin
    -- we begin by asking Lean to provide the meanings of the 
    -- words we've taught it. We use the rewrite tactic for that.
    rw [is_deterministic, Shannon_entropy],
    -- We split the two directions of the iff.
    split,
    {
        -- we prove one direction
        intro H0,
        -- rewrite in a more convenient form
        have H1: ∑ (i : ι), X i * real.log ((X i)⁻¹) = 0,
        {
            simp only [← real.log_inv, ← mul_neg_eq_neg_mul_symm, ← sum_neg_distrib] at H0,
            exact H0,
        },
        -- show each term in the sum must be zero
        have H2 : ∀ (i : ι), (X i) * real.log((X i)⁻¹) = 0,
        {
            apply sum_nonneg_zero, -- TODO
            exact H1,
            intro i,
            rw mul_nonneg_iff,
            left,
            split, {apply probs_nonneg,}, {apply log_nonneg, apply probs_nonneg, apply probs_le_one,},
        },
        -- if the product is zero then one of the factors must be zero
        have H3 : ∀ (i : ι), (X i = 0) ∨ (real.log((X i)⁻¹) = 0),
        {
            intros i,
            specialize H2 i,
            rw mul_eq_zero at H2,
            exact H2,
        },
        have H4 : ∀ (i : ι), (X i = 0) ∨ (X i = 1),
        {
            intros i,
            specialize H3 i,
            cases H3 with l r,
            left,
            exact l,
            right,
            -- specialize helper (X i)⁻¹,
            -- specialize helper2 (X i),
            apply helper2,
            apply helper,
            {
                rw real.log_inv at r,
                rw neg_eq_zero at r,
                have hXi0 : (X i) = 0 ∨ (X i) = 1, {sorry}, -- in both cases (X i)⁻¹ > 0
                have hXi1 : (X i)⁻¹ > 1 ∨ (X i)⁻¹ = 1, {sorry},
                have hXi4 : (X i)⁻¹ > 0, {sorry},
                exact hXi4,
            },
            exact r,
        },
        apply helper3, exact sum_probs_one, exact H4,
    },
    {
        -- we prove the other direction
        intro h,
        simp only [← sum_neg_distrib, ← mul_neg_eq_neg_mul_symm, ← real.log_inv],
        rw sum_eq_zero, norm_num,
        apply helper4,
        apply helper5,
        cases h with j hj,
        use j,
        finish,
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
    have H : - ∑ i, X i * real.log (X i) = ∑ i, X i * real.log (1 / (X i)) ,
        by simp only [one_div, real.log_inv, mul_neg_eq_neg_mul_symm, sum_neg_distrib],
    unfold is_uniform at hX,
    -- have hX2 : ∀ i : ι, 1 / (X i) = fintype.card ι, {sorry},
    -- have hX3 : ∀ i : ι, (X i) * real.log(1 / (X i)) = (1 / fintype.card ι) * real.log(fintype.card ι), {sorry},
    -- rw hX2 at H,
    -- rw is_uniform at hX,
    -- we need to subsitute 1 / fintype.card ι for (X i).
    sorry
end