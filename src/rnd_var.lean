import data.real.basic
import algebra.big_operators

---- DISCRETE RANDOM VARIABLE

open finset

open_locale big_operators

universe x

variables 
{ι : Type x} 
[fintype ι]
[decidable_eq ι]

class rnd_var (X : ι → ℝ) :=
(probs_nonneg :  ∀ i, 0 ≤ X i)
(sum_probs_one : ∑ i, X i = 1)

variables {X : ι → ℝ} [rnd_var X]

lemma probs_le_one : ∀ i, X i ≤ 1 := 
begin
  intros,
  sorry
end

variable (X) -- Tell Lean to explicitly ask for X in what follows.

noncomputable theory

section
open_locale classical

/--
Kronecker delta: 
-/
def delta (i : ι) (j : ι) : ℝ := if (i = j) then 1 else 0

/--
Definition (deterministic random variable): 
-/
def is_deterministic :=  ∃ j, ∀ i, if (i = j) then (X i = 1) else (X i = 0)  

end

lemma delta_if_det {X : ι → ℝ} [rnd_var X]
  (h : ∀ i, X i = 0 ∨ X i = 1) :
  (∃ j, ∀ i, if (i = j) then (X i = 1) else (X i = 0)) :=
begin
  have h_ite : X = λ i, if (X i = 1) then 1 else 0,
  { ext i,
    cases h i with hxi0 hxi1,
    { rw [hxi0, if_neg (@zero_ne_one ℝ _ _)] },
    { rw [if_pos hxi1, hxi1] } },
  have h_norm : ∑ i, X i = 1 := rnd_var.sum_probs_one,
  rw h_ite at h_norm,
  dsimp only at h_norm,
  -- split sum into two by value of X i
  rw sum_ite at h_norm,
  have h_aux : (∑ x in univ.filter (λ x, ¬X x = 1), 0 : ℝ) = 0 := sum_const_zero,
  rw h_aux at h_norm,
  rw [add_zero, sum_const, nsmul_one, ← nat.cast_one, nat.cast_inj,
      card_eq_one] at h_norm,
  -- now h_norm is essentially the goal but needs some massaging
  cases h_norm with j hj,
  simp_rw [ext_iff, mem_filter, mem_univ, true_and, mem_singleton, nat.cast_one] at hj,
  use j,
  intro i,
  rw if_congr_prop (hj i).symm iff.rfl iff.rfl,
  cases h i with hxi0 hxi1,
  { rw [hxi0, if_neg (@zero_ne_one ℝ _ _)] },
  { rw [if_pos hxi1, hxi1] }
end

/--
Definition (uniform random variable): a random variable
whose  probabilities are equal to 1/n, where n 
is the number of symbols that the random variable 
can assume.
-/
def is_uniform := ∀ i, X i = 1 / fintype.card ι