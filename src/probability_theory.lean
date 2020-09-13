import data.real.basic
import linear_algebra.matrix

    --    .-------.    ______
    --   /   o   /|   /\     \
    --  /_______/o|  /o \  o  \
    --  | o     | | /   o\_____\
    --  |   o   |o/ \o   /o    /
    --  |     o |/   \ o/  o  /
    --  '-------'     \/____o/

---- NOTES

-- We think of discrete joint probability distributions as 
-- matrices. The probability that information source gives 
-- X = x and Y = y is stored in XY(x,y).




---- JOINT PROBABILITY

/-
Definition (joint probability):
-/
def joint_prob {Xdim Ydim : ℕ} (XY : matrix (fin Xdim) (fin Ydim) ℝ) (x y : ℕ) : ℝ := 
XY x y




---- CONDITIONAL PROBABILITY

/-
Definition (conditional probability): Given a joint probability
distribution XY, cond prob is p_XY(x|y) = p_XY(x ∩ y) / p_XY(y).
-/
def cond_prob {Xdim Ydim : ℕ} (XY : matrix (fin Xdim) (fin Ydim) ℝ) (x y : ℕ) : ℝ := 
XY(x,y) / (∑ x in finset.range(Xdim), XY(x,y))




---- INDEPENDENT RANDOM VARIABLES

def indpndnt_rdm_vars (X Y : random_variable) : Prop := 
p_XY(x,y) = p_X(x) * p_Y(y)




---- SCRATCH WORK

noncomputable theory

structure random_variable (α : Type) (n : ℕ) : Type :=
(outcomes      : multiset α)
(probabilities : multiset ℝ) -- do we know of probabilities that are not real numbers?
-- need to add hypothesis that outcomes.card = probabilities.card?
(normalized    : probabilities.sum = 1)

/-
An example of a random variable: A 6-faced die. It is a 
random variable that can take one of 6 values, all of 
which have type ℕ.
-/
def six_faced_die : random_variable ℕ 6 :=
{
    outcomes := {1,2,3,4,5,6},
    probabilities := {1/6, 1/6, 1/6, 1/6, 1/6, 1/6},
    normalized := by norm_num
}

/-
Another example of a random variable: A quantum information 
that outputs one of the 4 Bell states
-/
def Bell_die : random_variable (pure_state 2) 4 :=
{
    outcomes := {|ψ⁺⟩, |ψ⁻⟩, |φ⁺⟩, |φ⁻⟩},
    probabilities := {1/4, 1/4, 1/4, 1/4},
    normalized := by norm_num
}




---- INDEPENDENT RANDOM VARIABLES

def indpndnt_rdm_vars 
{α : Type} {n m : ℕ} 
(X : random_variable α n) (Y : random_variable α m) : Prop := 
p_XY(x,y) = p_X(x) * p_Y(y)