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

-- def delta (i : ι) (j : ι) [decidable_eq ι] : ℝ := if i=j then 1 else 0

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

lemma sum_nonneg_zero {f : ι → ℝ} (h : ∑ (i : ι), f i = 0) (h': ∀ i : ι, 0 ≤ f i) : ∀ i : ι, f i = 0 :=
begin
    intro i,
    specialize h' i,
    -- split h' into branches f i = 0 and f i > 0
    -- first one follows from sum_const_zero
    -- second one leads to contradiction, so `exfalso` + something
    sorry,
end

lemma helper : ∀ (r : ℝ), real.log(r) = 0 → r = 1 := sorry

lemma helper1 : ∀ (r : ℝ), r = 1 → real.log(r) = 0 := sorry

lemma helper2 : ∀ (r : ℝ), r⁻¹ = 1 → r = 1 := by exact λ {g : ℝ}, inv_eq_one'.mp

lemma log_nonneg : ∀ (r : ℝ), r ≤ 1 → 0 ≤ real.log(r⁻¹) := sorry

lemma helper3 (X : ι → ℝ) (hX : ∑ i, X i = 1) [decidable_eq ι] : 
∀ i, X i = 0 ∨ X i = 1 → (∃ j, ∀ i, if (i = j) then (X i = 1) else (X i = 0)) := 
begin
    sorry,
end

lemma helper4 (X : ι → ℝ) : 
(∀ (i : ι), X i = 0 ∨ X i = 1) → (∀ (i : ι), X i = 0 ∨ real.log(X i) = 0) := sorry

lemma helper5 {X : ι → ℝ} {j : ι} [decidable_eq ι] : 
(∀ i, ite (i = j) (X i = 1) (X i = 0)) → (∀ i, X i = 0 ∨ X i = 1) := 
begin
    sorry
end

lemma helper5' {X : ι → ℝ} [decidable_eq ι] : 
∀ i, X i = 0 ∨ X i = 1 → ∃ j, ∀ i, ite (i = j) (X i = 1) (X i = 0) := 
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
            split, {apply probs_nonneg,}, {apply log_nonneg, apply probs_le_one,},
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
            exact r,
        },
        -- use helper3?
        sorry,
    },
    {
        -- we prove the other direction
        intro h,
        simp only [← sum_neg_distrib, ← mul_neg_eq_neg_mul_symm, ← real.log_inv],
        rw sum_eq_zero, norm_num,
        -- intro i,
        apply helper4,
        -- use helper 5?
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