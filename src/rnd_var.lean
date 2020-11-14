import data.real.basic
import algebra.big_operators

---- DISCRETE RANDOM VARIABLE

open_locale big_operators

universe x

class rnd_var {ι : Type x} (s : finset ι) (X : ι → ℝ) :=
(probs_nonneg :  ∀ i ∈ s, 0 ≤ X i)
(sum_probs_one : ∑ i in s, X i = 1)

variables {ι : Type x} {s : finset ι} {X : ι → ℝ} [rnd_var s X]

lemma probs_le_one {s : finset ι} {X : ι → ℝ} [rnd_var s X] : 
∀ i ∈ s, X i ≤ 1 := 
begin
    intros,
    sorry
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
Definition (uniform random variable): a random variable
whose  probabilities are equal to 1/n, where n 
is the number of symbols that the random variable 
can assume.
-/
def is_uniform (s : finset ι) (X : ι → ℝ) [rnd_var s X] : Prop :=
(∀ i ∈ s, X i = 1 / s.card)