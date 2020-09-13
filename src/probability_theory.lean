import data.real.basic
import data.finset.basic
-- import linear_algebra.matrix

open_locale big_operators



    --    .-------.    ______
    --   /   o   /|   /\     \
    --  /_______/o|  /o \  o  \
    --  | o     | | /   o\_____\
    --  |   o   |o/ \o   /o    /
    --  |     o |/   \ o/  o  /
    --  '-------'     \/____o/




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

---- AN PROBABILITY EVENT

structure event (α : Type) : Type :=
(outcome : α) -- α is the type of the outcome
(probability : ℝ)

def coin_heads : event ℕ := {outcome := 4, probability := 1/4}


---- RANDOM VARIABLE

/-
Definition (random variable): A random variable is a finset of events, 
and a hypothesis that the probabilities of all the events add up to 1.
-/
structure random_variable (α : Type) : Type :=
(events : list (event α))
(normalized : (list.map (λ (e : event α), e.probability) events).sum = 1) 
-- (normalized : ∑ e in events, e.probability = 1)
-- (outcomes      : multiset α)
-- (probabilities : multiset ℝ) -- do we know of probabilities that are not real numbers?
-- need to add hypothesis that outcomes.card = probabilities.card?
-- (normalized    : probabilities.sum = 1)


/-
An example of a random variable: A 6-faced die. It is a 
random variable that can take one of 6 values, all of 
which have type ℕ.
-/
def e1 : event ℕ := {outcome := 1, probability := 1/6}
def e2 : event ℕ := {outcome := 2, probability := 1/6}
def e3 : event ℕ := {outcome := 3, probability := 1/6}
def e4 : event ℕ := {outcome := 4, probability := 1/6}
def e5 : event ℕ := {outcome := 5, probability := 1/6}
def e6 : event ℕ := {outcome := 6, probability := 1/6}

@[simp]
lemma temp1 : e1.probability = 1/6 := rfl
@[simp]
lemma temp2 : e2.probability = 1/6 := rfl
@[simp]
lemma temp3 : e3.probability = 1/6 := rfl
@[simp]
lemma temp4 : e4.probability = 1/6 := rfl
@[simp]
lemma temp5 : e5.probability = 1/6 := rfl
@[simp]
lemma temp6 : e6.probability = 1/6 := rfl

def six_faced_die : random_variable ℕ :=
{
    events := [e1,e2,e3,e4,e5,e6],
    normalized := by {simp, norm_num},
}



example : (list.map (λ (e : event ℕ), e.probability) [e1,e2,e3,e4,e5,e6]).sum = 1 :=
begin
    simp,
    norm_num,
end

example : 2 * e1.probability  = 2/6 := 
begin
    simp,
end


#check ({1,2,3,4,4} : finset ℕ)

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

-- How do we refer to the probability associated with a given 
-- outcome? Ideally we would like to be able to say 
-- #check six_faced_die(5) and get ℝ for the type.




---- INDEPENDENT RANDOM VARIABLES

def indpndnt_rdm_vars 
{α : Type} {n m : ℕ} 
(X : random_variable α n) (Y : random_variable α m)
(XY : random_variable α (n*m))
{hXY : XY.outcomes = zip(X.outcomes, Y.outcomes)} : Prop := 
∀ x in  XY(x,y) = X(x) * Y(y)