import data.real.basic
import algebra.big_operators

---- DISCRETE RANDOM VARIABLE

open_locale big_operators

universe x

variables {ι : Type x}

class rnd_var (s : finset ι) (X : ι → ℝ) :=
(probs_nonneg :  ∀ i ∈ s, X i ≥ 0)
(sum_probs_one : ∑ i in s, X i = 1)