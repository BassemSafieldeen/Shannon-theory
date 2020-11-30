/- 
Theorem 2: uniqueness of the entropy function

Hypotheses:

1. H is continuous in p
2. If p is uniform, H is monotonically increasing in n
3. Partitioning/coarse-graining - I think the proper way to express this is through conditional probabilities like:
    Let X be a random variable with probabilities p_0, ..., p_N
    Pick any j ≤ N
    Define X_coarse j = if (X = j) then 1 else 0
    Define X_hat = X | X_coarse = 1
    Then H X = H X_coarse + (1-p_j) * H X_hat

Proof sketch:

1. Let p be uniform. Use 3 iteratively to decompose the process into a series of N steps.
2. This implies that H restricted to uniform distributions is "essentially" a logarithm since A(s^m) = m * A(s) - proving this requires manipulating some inequalities, & using 2
3. Use 3 to reduce the non-uniform (but rational) to the uniform case
4. Continuity argument to extend it from the rationals to the reals
-/

/-
Binary coarse graining of a finite random variable
-/
def coarse (X : ι → ℝ) (j : ι) [rnd_var X] : (ι → ℝ) := λ i, if (i = j) then (X j) else (1 - (X j))

/-
Conditional probability of X given coarse X i = 1
Assumes X j != 0
-/
-- TODO: maybe define this invoking the p_cond method instead of writing custom code
def cond_coarse (X : ι → ℝ) (j : ι) [rnd_var X] : (ι → ℝ) := λ i, (X i) / (1 - (X j))

/--
Definition: Shannon's H
-/
class Shannons_H (N : ℕ) (X : ι → ℝ) [rnd_var X] :=
-- We have defined X : ι → ℝ
-- This is isomorphic to X : ℝ^|ι|
-- But maybe Lean cannot infer that - and there is no obvious topology for the first type
(continuous : topology.basic.continuous_def λ X, Shannons_H N X)
-- If we want to state monotonicity in N maybe we'll have to make H's dependence on N explicit in the type definition. Otherwise, we may be able to use fintype.card ι ? Yes, I think you're right.
(monotonic : is_uniform X → λ N, order.basic.monotone Shannons_H N X)
(coarse_graining : ∀ (i : ι), Shannons_H X = Shannons_H (coarse X i) + (1 - X j) * Shannons_H (cond_coarse X i) )

/--
Theorem: Shannon_entropy of Shannon's H
-/
theorem theorem2 (H : ι → ℝ) [Shannons_H H] : 
-- K cannot be a free variable. I see two choices:
-- 1. define a family of H's parametrized by K (same entropy in diff units)
-- 2. Re-state the theorem with an existential quant on K
∀ (K : ℝ>0), H = - K * ∑ i, pᵢ * real.log(pᵢ) :=
begin
    sorry
end

/--
Theorem: Shannon_entropy of Shannon's H with existential quantifier
-/
theorem theorem2' (H : ι → ℝ) [Shannons_H H] : 
-- K cannot be a free variable. I see two choices:
-- 1. define a family of H's parametrized by K (same entropy in diff units)
-- 2. Re-state the theorem with an existential quant on K
∃ (K : ℝ>0), H = - K * ∑ i, pᵢ * real.log(pᵢ) :=
begin
    sorry
end

/--
Theorem: Shannon_entropy of Shannon's H
-/
theorem theorem2'' (H : ι → ℝ) [Shannons_H H] {K : ℝ>0} : 
-- K cannot be a free variable. I see two choices:
-- 1. define a family of H's parametrized by K (same entropy in diff units)
-- 2. Re-state the theorem with an existential quant on K
H = - K * ∑ i, pᵢ * real.log(pᵢ) :=
begin
    sorry
end

/--
Consider the expression H(p₁, ..., pₙ). 
We have an unordered set of probabilities? i.e. a point in the (n-1)-simplex modulo permutations (random variables or outcomes from the sample space?)
-/
theorem H (...) : 
continuous H over p₁, .. pₙ 
→ 
(∀ i, pᵢ = 1/n → monotonically_increasing H)
→
(...)
→ 
H = - K * ∑ i, pᵢ * real.log(pᵢ) := 
begin
    sorry
end


---- Theorem 3

/--
Definition: probability expression (helper definition)
-/
def helper_prop (p : ℝ) (N : ℕ) (H : ...) (δ : ℝ>0) := 
|real.log(p⁻¹) / N - H| ≤ δ

/--
Theorem 3
-/
theorem theorem3 : 
∀ ε>0, ∀ δ>0, ∃ N₀, ∀ N ≥ N₀
p < ε
∨
helper_prop p N H δ
:=
begin
    sorry
end



---- Theorem 4

/--
"Consider again the sequences of length N and let them be arranged in order of decreasing probabilities.

We define n(q) to be the number we must take from this set starting with the most probable one in order to accumulate a total probability q for those "
-/
def n (q : ℝ) (hq1 : q > 0) (hq2 : q < 1)


/--
Theorem 4
-/
theorem theorem4 (q : ℝ) (hq1 : q > 0) (hq2 : q < 1) : 
lim N → ∞ real.log(n(q)) / N = H :=
begin
    sorry
end

