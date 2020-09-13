import algebra.big_operators
import data.real.basic
import analysis.special_functions.exp_log
import measure_theory.probability_mass_function

-- open_locale big_operators -- this enables the notation

noncomputable theory -- without this there is an error

---- HELPERS

-- I got this from the Lean Zulip
theorem multiset.map_repeat {α β : Sort*} (f : α → β) (x : α) (n : ℕ) :
  (multiset.repeat x n).map f = multiset.repeat (f x) n :=
nat.rec_on n rfl $ λ n ih, by simp_rw [multiset.repeat_succ, multiset.map_cons, ih]




---- SHANNON ENTROPY 

/-
Definition: Shannon entropy. 
-/
def Shannon_entropy (X : multiset ℝ) : ℝ
:= - (multiset.map (λ (x : ℝ), x * real.log(x)) X).sum

-- def Shannon_entropy (X : finset ℝ) : ℝ
-- := - ∑ x in X, x * real.log(x)

/-
Theorem (non-negativity): Shannon entropy is non-negative for 
any random variable.
-/
theorem is_nonnegative_Shannon_entropy : 
∀ (X : multiset ℝ), Shannon_entropy(X) ≥ 0 := 
begin
    sorry
end

/-
Theorem (concavity): Shannon entropy is concave in the probability 
density.
-/
theorem concavity := sorry

/-
Definition (deterministic random variable): 
-/
def is_deterministic (X : multiset ℝ) : Prop := sorry

/-
Theorem (Minimum value): Shannon entropy vanishes if and only if 
X is a deterministic variable.
-/
theorem Shannon_entropy_minimum_value : 
∀ (X : multiset ℝ), Shannon_entropy(X) = 0 ↔ is_deterministic X :=
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




---- CONDITIONAL ENTROPY

def cond_entropy (XY : multiset ℝ) (y : ℕ) : ℝ := sorry 
-- XY is a joint prob dist of X and Y
-- Note that XY.card = X.card * Y.card
-- We can write it as a matrix containing the probabilities, 
-- which we can then access by saying something like XY(x,y).
-- The events are encoded in the indices of the matrix. For two 
-- dice we would write something like XY(1,4). For two fair dice 
-- would come out to XY(1,4) = 

notation `H(` X `|` y `)` := cond_entropy XY y



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

--------------------------------