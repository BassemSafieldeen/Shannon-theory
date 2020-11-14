import data.real.basic
import algebra.big_operators

---- DISCRETE RANDOM VARIABLE

open_locale big_operators

universe x

class rnd_var {ι : Type x} (s : finset ι) (X : ι → ℝ) :=
(probs_nonneg :  ∀ i ∈ s, 0 ≤ X i)
(sum_probs_one : ∑ i in s, X i = 1)

variables {ι : Type x} {s : finset ι} {X : ι → ℝ} [rnd_var s X]

lemma Xᵢ_le_1 {s : finset ι} {X : ι → ℝ} [rnd_var s X] : 
∀ i ∈ s, X i ≤ 1 := 
begin
    intros,
    sorry
end

theorem probs_nonneg_of_rnd_var : ∀ i ∈ s, X i ≥ 0 := 
begin
    intros,
    exact rnd_var.probs_nonneg i H,
end