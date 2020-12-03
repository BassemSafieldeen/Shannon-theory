import data.real.basic
import algebra.big_operators

open finset

open_locale big_operators  -- this enables the notation

universe x

variables {ι : Type x} [fintype ι]
variables {f : ι → ℝ}
variable (f)

noncomputable theory

section
open_locale classical

theorem
test (h1 : ∀ (i : ι), f i = 0 ∨ f i = 1) (h2 : (∑ (i : ι), f i = 1)) : ∃ (j : ι), f j = 1 :=
begin
    by_contradiction H,
    push_neg at H,
    have H0 : ∀ i, f i = 0,
    {
        finish,
    }, -- combine h1 & H
    have H1 : ∑ i, f i = 0,
    {
        apply sum_eq_zero,
        norm_num,
        exact H0,
    },
    linarith,
end

end

/-
contrapositive
-/
-- theorem
-- test_ (h1: ∀ (i : ι), f i ≠ 1) : (∀ (i : ι), f i = 0 ∨ f i = 1) → (∑ (i : ι), f i ≠ 1) :=
-- begin
--     intro h,
--     sorry
-- end