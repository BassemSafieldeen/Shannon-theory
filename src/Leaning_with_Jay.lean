import analysis.special_functions.exp_log
import data.complex.basic
-- import algebra.big_operators.basic -- doesn't work on Cocalc :(

#check 1 -- checking that Lean works
#check real.log
import rnd_var

/--
Definition: relative entropy
-/
def relative_entropy
(p q : ι → ℝ)
{hpq : supp(p) ⊆ supp(q)}
[rnd_var p q] : ℝ := 
∑ i, (p i) * real.log((p i) / (q i))

/-
Note: The ℝ type in lean contains only finite real numbers. To include ∞ we need to use enreal.

But let's not worry about that right now.
-/

/-
Note: We use curly brackets around hpq to tell Lean that it's an implicit hypothesis, and so Lean should infer it from the context instead of asking us to provide it as input to realtive_entropy.
-/

/--
Theorem 10.7.1: Relative entropy is nonnegative
-/
theorem
relative_entropy_nonneg (p q : ι → ℝ)
[rnd_var p q] : relative_entropy p q ≥ 0 := 
begin
    intros,
    rw relative_entropy,
    sorry
end

/-
Conditional probability given a joint distribution.
-/
def p_cond (p : ι → ι' → ℝ) [rnd_var p] : ℝ := if (∑ (i : ι), p i i' = 0) then 0 else (p i i') / (∑ (i : ι), p i i')

/--
Definition: conditional probability distribution
Hmmm, I need to brush up on the definitions.
-/
-- I think this should be a def and not a class
-- class cond_prob_dist (p_cond : X → Y → ℝ) :=
-- (∀ (x : X), p x y)

/--
A classical channel is a conditional probability distribution specifying the probability of receiving output i' given input i was sent.
-/
class classical_channel (N : ι → ι' → ℝ) [rnd_var (N i)] :=
(channel_is_cond_prob : ∃ (p : ι → ℝ) [rnd_var p], p_cond p = N)

/--
classical channel 2
-/
def classical_channel := p_cond

/--
Corollary 10.7.2 (Monotonicity of relative entropy)
-/
theorem
relative_entropy_monotonic (p q : ι → ℝ) (N : ι → ι' → ℝ) [rnd_var p q] [channel N] : relative_entropy_ p q ≥ relative_entropy_ (∑ (i : ι), (N i i') * (p i)) (∑ (i : ι), (N i i') * (q i)) :=
being
    sorry
end
/--
Pinsker inequality
Theorem 10.8.1 here (https://arxiv.org/pdf/1106.1445.pdf)
-/
theorem Pinsker_ineq (p q : ι → ℝ) [rnd_var p q] : 
relative_entropy p q ≥ 1 / (2*ln(2)) * ∥p - q∥₁² := 
begin
    sorry
end




---- Quantum stuff

/--
A quantum channel is a linear map between two linear operators on complex hilbert spaces ℋ₁ and ℋ₂.
-/
class quantum_channel (𝒩 : (ℋ₁ →ₗ[∁] ℋ₁) →ₗ[∁] (ℋ₂ →ₗ[∁] ℋ₂)) :=
(trace_preserving : ∀ (ρ : ℋ₁ →ₗ[∁] ℋ₁), Tr(𝒩(ρ)) = Tr(ρ))
(completely_positive : sorry)

/--
Regularized Holevo information
-/
def reg_Holevo_info (𝒩 : (ℋ₁ →ₗ[∁] ℋ₁) →ₗ[∁] (ℋ₂ →ₗ[∁] ℋ₂)) [quantum_channel 𝒩] : ℝ := sorry

notation `χ_reg` 𝒩 := reg_Holevo_info 𝒩

/--
Theorem 20.3.1:
"The classical capacity of a quantum channel is equal to the regularization of the Holevo information of the channel"
-/
theorem Holevo_Schumacher_Westmoreland (𝒩 : (ℋ₁ →ₗ[∁] ℋ₁) →ₗ[∁] (ℋ₂ →ₗ[∁] ℋ₂)) [quantum_channel 𝒩] : capacity(𝒩) = χ_reg(𝒩) := 
begin
    sorry
end


