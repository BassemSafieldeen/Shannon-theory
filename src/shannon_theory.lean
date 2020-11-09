import algebra.big_operators
import linear_algebra.basic
import data.real.basic
import data.list.basic
import analysis.special_functions.exp_log
import probability_theory

---- SHANNON ENTROPY 

open_locale big_operators  -- this enables the notation

universe x

variables 
{ι : Type x} (s : finset ι) -- indexing type and indexing set
{X : ι → ℝ} {hX₁ : ∀ i ∈ s, X i ≥ 0} {hX₂ : ∑ i in s, X i = 1} -- discrete probability distribution

noncomputable theory

/--
Definition: Shannon entropy. 
-/
def Shannon_entropy (s : finset ι) (X : ι → ℝ) (hX₁ : ∀ i ∈ s, X i ≥ 0) (hX₂ : ∑ i in s, X i = 1) : ℝ := 
- ∑ i in s, (X i) * real.log(X i)

-- notation `H(`X`)` := Shannon_entropy X

lemma Xᵢ_le_1 (s : finset ι) (X : ι → ℝ) (hX₁ : ∀ i ∈ s, X i ≥ 0) (hX₂ : ∑ i in s, X i = 1) : 
∀ i ∈ s, X i ≤ 1 := 
begin
    intros,
    sorry
end

/--
Theorem (non-negativity): Shannon entropy is non-negative for 
any random variable.
-/
theorem Shannon_entropy_nonneg : 
∀ (s : finset ι) (X : ι → ℝ) {hX₁ : ∀ i ∈ s, X i ≥ 0} {hX₂ : ∑ i in s, X i = 1}, 
Shannon_entropy s X hX₁ hX₂ ≥ 0 := 
begin
    intros,
    rw Shannon_entropy,
    -- move the minus inside
    simp only [← mul_neg_eq_neg_mul_symm, ← finset.sum_neg_distrib],
    -- each term in the sum is nonnegative
    have H2 : ∀ i ∈ s, - (X i) * real.log(X i) ≥ 0, {
        intros,
        have h : - (X i) * real.log(X i) = (X i) * (- real.log(X i)), by linarith,
        rw h,
        apply mul_nonneg,
        {exact hX₁ i H},
        {
            rw neg_nonneg,
            apply real.log_nonpos,
            {exact hX₁ i H},
            {exact Xᵢ_le_1 s X hX₁ hX₂ i H},
        },
    },
    -- so we have that the whole sum is nonneg
    apply finset.sum_nonneg,
    simp only [neg_mul_eq_neg_mul_symm, ge_iff_le, mul_neg_eq_neg_mul_symm, neg_nonneg] at *,
    exact H2,
end

/-
Theorem (concavity): Shannon entropy is concave in the probability 
density.
-/
theorem concavity := sorry

/-
Definition (deterministic random variable): 
-/
-- def is_deterministic (X : multiset ℝ) : Prop := sorry

/-
Theorem (Minimum value): Shannon entropy vanishes if and only if 
X is a deterministic variable.
-/
theorem Shannon_entropy_minimum_value : 
∀ (X : multiset ℝ), Shannon_entropy(X) = 0 ↔ is_deterministic X :=
begin
    sorry
end

theorem Shannon_entropy_minimum_value' {α : Type} : 
∀ (X : random_variable α), Shannon_entropy(X) = 0 ↔ is_deterministic X :=
begin
    sorry
end

/-
Definition (uniform random variable): a random variable
whose  probabilities are equal to 1/n, where n 
is the number of symbols that the random variable 
can assume.
-/
def is_uniform_rnd_var (X : multiset ℝ) : Prop :=
X = multiset.repeat (1/X.card) X.card

/-
Theorem: The Shannon entropy of a uniform 
random variable is log(n).
-/
theorem Shnn_entropy_uniform_rdm_var (X : multiset ℝ) (hX : X.card ≠ 0) : 
is_uniform_rnd_var(X) → Shannon_entropy X = real.log(X.card)
:=
begin
    intro,
    unfold is_uniform_rnd_var at a,
    rw a,
    simp,
    unfold Shannon_entropy,
    rw multiset.map_repeat,
    simp,
    -- generalize_hyp : X.card = c at hX,
    -- generalize : X.card = c,
    rw ← mul_assoc,
    rw mul_inv_cancel,
    simp,
    norm_cast,
    exact hX,
end

theorem Shnn_entropy_uniform_rdm_var' (s : finset ι) (X : ι → ℝ) {hX₁ : ∀ i ∈ s, X i ≥ 0} {hX₂ : ∑ i in s, X i = 1} : 
(∀ i ∈ s, X i = 1 / s.card) → Shannon_entropy s X hX₁ hX₂ = real.log(s.card)
:=
begin
    intro hX₃,
    rw Shannon_entropy,
    have : -∑ i in s, X i * real.log (X i) = ∑ i in s, X i * real.log (1 / (X i)) ,
        by simp only [one_div, real.log_inv, mul_neg_eq_neg_mul_symm, finset.sum_neg_distrib],
    rw this,
    clear this,
    -- we need to subsitute 1 / s.card for  (X i).
    sorry
end



---- CONDITIONAL ENTROPY

-- def cond_entropy {Xdim Ydim : ℕ} (XY : matrix (fin Xdim) (fin Ydim) ℝ) : ℝ := 
-- - ∑ x in finset.range(Xdim), 
-- ∑ y in finset.range(Ydim), 
-- (cond_prob XY x y) * real.log(cond_prob XY x y)
-- XY is a joint prob dist of X and Y
-- Note that XY.card = X.card * Y.card
-- We can write it as a matrix containing the probabilities, 
-- which we can then access by saying something like XY(x,y).
-- The events are encoded in the indices of the matrix. For two 
-- dice we would write something like XY(1,4). For two fair dice 
-- would come out to XY(1,4) = 1/6 * 1/6.

-- notation `H(` XY `#` X `|` Y `)` := cond_entropy XY X Y 
-- we need to know which rndm variable is dependent on 
-- which rndm variable.

/-
"The conditional entropy H(X|Y) as well deserves an interpretation. Suppose that 
Alice possesses random variable X and Bob possesses random variable Y . The 
conditional entropy H(X|Y ) is the amount of uncertainty that Bob has about X 
given that he already possesses Y."
https://arxiv.org/pdf/1106.1445.pdf
-/

/-
Theorem () : conditioning does not increase entropy.
"The above interpretation of the conditional entropy H(X|Y ) immediately suggests that
it should be less than or equal to the entropy H(X). That is, having access to a side
variable Y should only decrease our uncertainty about another variable."
https://arxiv.org/pdf/1106.1445.pdf    
-/
theorem conditioning_and_entropy_inequality : 
H(X) ≥ H(X|Y) :=
begin
    sorry,
end




---- JOINT ENTROPY

/-
Definition (joint entropy): 
-/
-- def joint_entropy {Xdim Ydim : ℕ} (XY : matrix (fin Xdim) (fin Ydim) ℝ) : ℝ :=
-- - ∑ x in finset.range(Xdim), 
-- ∑ y in finset.range(Ydim), 
-- (joint_prob XY x y) * real.log(joint_prob XY x y)




---- CHAIN RULE

/-
Theorem (chain rule): ...
-/
@[simp]
theorem chain_rule_1 {Xdim Ydim : ℕ} {XY : matrix (fin Xdim) (fin Ydim) ℝ} : 
joint_entropy XY = Shannon_entropy X + cond_entropy XY Y X := 
begin
    sorry,
end

@[simp]
theorem chain_rule_2 {Xdim Ydim : ℕ} {XY : matrix (fin Xdim) (fin Ydim) ℝ} : 
joint_entropy XY = Shannon_entropy Y + cond_entropy XY X Y :=
begin
    sorry,
end

theorem chain_rule : 
H(X₁, ..., Xₙ) = H(X₁) + H(X₂|X₁) + ... + H(Xₙ|X_{n-1}, ..., X₁) :=
begin
    sorry,
end




---- SUBADDITIVITY

/-
Theorem (entropy is subadditive): ...
-/
theorem entropy_subadditive : 
H(X₁, ..., Xₙ) ≤ ∑ i in finset.range(n), H(Xᵢ) :=
begin
    sorry,
end




---- MUTUAL INFORMATION

/-
Definition (mutual information): Let X and Y be discrete random variables with
joint probability distribution pX,Y (x, y). The mutual information I(X; Y ) is the marginal
entropy H(X) less the conditional entropy H(X|Y):
I(X; Y ) ≡ H(X) − H(X|Y).
https://arxiv.org/pdf/1106.1445.pdf 
-/
def mutual_info : ℝ := Shannon_entropy(X) - (cond_entropy XY X Y)

notation `I(`X`;`Y`)` := mutual_info X Y

/-
Lemma (symmetry in the input): mutual information is symmetric in the input.
-/
@[simp]
lemma mutual_info_symmetric : 
I(X;Y) = I(Y;X) :=
begin
    sorry,
end

/-
Lemma (nonnegativity): The mutual information I(X; Y) is non-negative for any 
random variables X and Y :
I(X; Y ) ≥ 0.
-/
lemma mutual_info_nonneg : I(X;Y) ≥ 0 := 
begin
    sorry,
end

/-
Lemma (mutual info zero iff independent random variable) : I(X;Y) = 0 if and 
only if X and Y are independent random variables (i.e., if pX,Y (x, y) =
pX(x)pY (y)).
-/
lemma mutual_info_zero_iff_indpndnt_rnd_vars : 
I(X;Y) = 0 ↔ indpndnt_rnd_vars X Y :=
begin
    sorry,
end




--------------------------------- SCRATCH WORK

-- NOTE: finset is defined as a multiset with no no duplicate elements.
-- But you can only do ∑ to a finset. Hmmm ...
-- Try list. Or try multiset, a list with duplicates allowed.
-- Don't use ∑ if it only works with finset.
-- Wait, but how do they do sums in the pmf file?

-- NOTE: Switch to measure_theory.probability_mass_function.pmf at some point.

/-
Testing finset.sum stuff
-/
example (X : finset ℕ) : X = {1,1,1,1,1} → (∑ x in X, x) = 5 :=
begin
    intro,
    sorry
end

example (X : finset ℕ) (hX : ∀ x ∈ X, x = 1) :  ∑ x in X, x = X.card :=
begin
sorry
end

#eval finset.range(2)


/-
Testing pmf stuff
-/
#check pmf ℕ


/-
Testing multiset stuff
-/
#eval list.repeat 5 10

#eval ({1,2,3,4} : multiset ℕ).prod

#eval ({1,2,3,4} : multiset ℕ).sum

#eval (multiset.map (λ (a:ℕ), 2 ) {1,2,3,4})  -- cool, this works!


/-
A function that doubles every element in a given multiset of ℝ.
-/
-- def myFunc : multiset ℝ → multiset ℝ := 
-- begin
-- intro X,
-- exact multiset.map (λ x:ℝ, 2*x) X,
-- end

-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F
def myFunc (X : multiset ℝ) : multiset ℝ :=
X.map $ λ x, 2 * x

/-
For a multiset of 10 elements, all of which are 5, doubling 
each element and summing gives 100.
-/

-- proof 1
example (X : multiset ℝ) (hX' : X.card = 10) : 
(∀(x:ℝ), x ∈ X → x = 5) → (myFunc X).sum = 100  := 
begin
    intro hX'',
    rw multiset.eq_repeat_of_mem hX'',
    rw hX',
    rw myFunc,
    -- unfold myFunc,
    rw multiset.map_repeat,
    rw multiset.sum_repeat,
    norm_num,
end

-- proof 2
example (X : multiset ℝ) (hX1 : X.card = 10) (hX2 : ∀ x ∈ X, (x : ℝ) = 5) : (myFunc X).sum = 100 :=
by { rw [multiset.eq_repeat_of_mem hX2, hX1, myFunc, multiset.map_repeat, multiset.sum_repeat], norm_num }

-- proof 2 (rewritten for learning purposes)
example (X : multiset ℝ) (hX1 : X.card = 10) (hX2 : ∀ x ∈ X, (x : ℝ) = 5) : 
(myFunc X).sum = 100 :=
begin
    rw multiset.eq_repeat_of_mem hX2,
    rw hX1,
    rw myFunc,
    rw multiset.map_repeat,
    rw multiset.sum_repeat,
    norm_num,
end

-- proof 3
example (X : multiset ℝ) (hX' : X.card = 10) :
(∀(x:ℝ), x ∈ X → x = 5) → (myFunc X).sum = 100  :=
begin
    intro hX'',
    have : X = list.repeat (5:ℝ) 10, { 
        obtain ⟨l⟩ := X,
        change (l : multiset ℝ) = _, congr,
        exact list.eq_repeat.2 ⟨hX', hX''⟩,
    },
    subst X,
    rw show (100:ℝ) = (10:ℕ) * (2 * 5), by norm_num,
    generalize_hyp : 10 = a at *,
    rw myFunc,
    simp,
end

-- proof 4
example (X : multiset ℝ) (hX' : X.card = 10) :
(∀(x:ℝ), x ∈ X → x = 5) → (myFunc X).sum = 100  :=
begin
    intro hX'',
    have := multiset.eq_repeat.2 ⟨hX', hX''⟩,
    subst X,
    rw show (100:ℝ) = (10:ℕ) * (2 * 5), by norm_num,
    generalize_hyp : 10 = a at *,
    simp [myFunc, multiset.repeat],
end

/-
State and prove the previous theorem using the indexing set 
from linear algebra.
-/

variables (hs : s.card = n)

include hs hu
example : ∑ i in s, u i = 1 := 
begin
    exact hu,
end

--------------------------------

