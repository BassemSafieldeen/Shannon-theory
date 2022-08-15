import algebra.big_operators
import analysis.special_functions.exp_log
import log

import rnd_var

---- SHANNON ENTROPY 

open finset rnd_var

open_locale big_operators  -- this enables the notation

universe x

variables 
{ι : Type x} -- indexing type
[fintype ι] -- tell Lean that the set of all elements ι is finite.
[decidable_eq ι] -- and that its elements can be compared for equality

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
  intro i,
  have H : ∑ i, f i = 0 ↔ ∀ i, f i = 0, {
    rw sum_eq_zero_iff_of_nonneg,
    {
      finish,
    },
    {
      simp only [hf2],
      finish,
    },
  },
  have H2 : ∀ i, f i = 0, {
    exact H.1 hf1,
  },
  apply H2,
end

lemma helper4 (X : ι → ℝ) : 
(∀ (i : ι), X i = 0 ∨ X i = 1) → (∀ (i : ι), X i = 0 ∨ real.log(X i) = 0) :=
begin
  intros hi i,
  have H : X i = 0 ∨ X i = 1, by exact hi i,
  cases H with x0 log0,
  left, exact x0,
  right, simp only [log0, real.log_one],
end

lemma helper5 {X : ι → ℝ} : 
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
    intro H0,
    -- rewrite in a more convenient form
    simp only [← real.log_inv, ← mul_neg_eq_neg_mul_symm, ← sum_neg_distrib] at H0,
    -- show each term in the sum must be zero
    have H2 : ∀ (i : ι), (X i) * real.log((X i)⁻¹) = 0,
    {
      apply sum_nonneg_zero,
      exact H0,
      intro i,
      rw mul_nonneg_iff,
      left,
      split, {apply probs_nonneg}, {apply real.log_inv_nonneg, apply probs_nonneg, apply probs_le_one},
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
      left, exact l,
      have hxi : 0 ≤ X i,
      {
        apply probs_nonneg i,
        exact _inst_3,
      },
      replace hxi := le_iff_lt_or_eq.mp hxi,
      cases hxi with xi0 xi1,
      right,
      rw real.log_inv at r,
      norm_num at r,
      exact real.one_of_log_zero_of_pos (X i) xi0 r,
      left,
      linarith,
    },
    apply delta_if_det, exact H4,
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

lemma
sum_of_constant_fun {f : ι → ℝ} {c : ℝ} (h1 : ∀ i, f i = c) : 
∑ i, f i = c * fintype.card ι :=
begin
  have h' : ∑ i, f i = ∑ i : ι, c, {finish,},
  have h'' : ∑ i : ι, c = fintype.card(ι) * c,
  {
    rw finset.sum_const,
    finish,
  },
  finish,
end