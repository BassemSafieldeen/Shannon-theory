import algebra.big_operators
import algebra.big_operators.order.finset
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

variables {f : ι → ℝ}
variable (f)

/-
A deterministic, normalized random variable must be equal to 1 for some i
-/
lemma
pure_norm_eq_one (h1 : ∀ (i : ι), f i = 0 ∨ f i = 1) (h2 : ∑ i, f i = 1) : ∃ (j : ι), f j = 1 :=
begin
    by_contradiction H,
    push_neg at H,
    have H0 : ∀ i, f i = 0,
    {
        finish,
    },
    have H1 : ∑ i, f i = 0,
    {
        apply sum_eq_zero,
        norm_num,
        exact H0,
    },
    linarith,
end

/-
foo
-/
lemma
deterministic_zero_or_one (X : ι → ℝ) [rnd_var X] : is_deterministic_ X → ∀ i, X i = 0 ∨ X i = 1 :=
begin
    intros h i,
    unfold is_deterministic_ at h,
    -- by_contradiction h',
    -- push_neg at h',
    cases h with j hj,
    -- specialize hj i,
    -- unfold ite at hj,
    -- cases hj with a b,
    left,
    by_contradiction hh,
    -- specialize b i,
    -- suggest,
    sorry
end

lemma
split_delta_sum (f : ℝ → ℝ) (X : ι → ℝ) [rnd_var X] : f 0 = 0 → is_deterministic X → ∃ j : ι, ∑ i, f (X i) = f (X j) :=
begin
    intros f0 det,
    unfold is_deterministic at det,
    cases det with j hj,
    -- split_ifs at hj,
    -- use j,
    -- split_if_reduction,
    sorry
end

lemma
real_zero_or_one_if_delta (f : ℝ → ℝ) : (∃ s, ∀ r, f r = if r=s then 1 else 0) → ∀ r, f r = 1 ∨ f r = 0 :=
begin
    contrapose,
    intro h,
    push_neg,
    push_neg at h,
    cases h with r hr,
    cases hr,
    intro s,
    use r,
    split_ifs,
    exact hr_left,
    exact hr_right,
end

-- same as _test_ex but need to assume equality is decidable (something you get for free in ℝ)
lemma
zero_or_one_if_delta (X : ι → ℝ) [rnd_var X] : is_deterministic X → ∀ i, X i = 0 ∨ X i = 1 :=
begin
    intro det,
    unfold is_deterministic at det,
    sorry
end
