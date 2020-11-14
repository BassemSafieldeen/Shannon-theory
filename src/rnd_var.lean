import data.real.basic
import algebra.big_operators

---- DISCRETE RANDOM VARIABLE

open_locale big_operators

universe x

variables {ι : Type x} [fintype ι]

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

section
open_locale classical

/--
Definition (deterministic random variable): 
-/
def is_deterministic :=  ∃ j, ∀ i, if (i = j) then (X i = 1) else (X i = 0)  

end

/--
Definition (uniform random variable): a random variable
whose  probabilities are equal to 1/n, where n 
is the number of symbols that the random variable 
can assume.
-/
def is_uniform := ∀ i, X i = 1 / fintype.card ι