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

---- A PROBABILITY EVENT

structure event (α : Type) : Type :=
(outcome : α) -- α is the type of the outcome
(probability : ℝ)

def coin_heads : event ℕ := {outcome := 1, probability := 1/2}


---- RANDOM VARIABLE

/-
Definition (random variable): A random variable is a finset of events, 
and a hypothesis that the probabilities of all the events add up to 1.
-/
structure random_variable (α : Type) : Type :=
(events : list (event α))
(normalized : (list.map (λ (e : event α), e.probability) events).sum = 1) 

/-
A function that takes two random variables and gives a random variable 
that represents the joint probability distribution on both variables.
-/
def from_indpndnt_rnd_vars {α β : Type} 
(X : random_variable α) (Y : random_variable β) :
random_variable := 
{
    events := sorry, -- all the permutations
    normalized := sorry,
}


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
    norm_num,
end


#check ({1,2,3,4,4} : finset ℕ)

/-
Another example of a random variable: A quantum information 
that outputs one of the 4 Bell states
-/
def Bell1 : event (pure_state 2) := {outcome := |ψ⁺⟩, probability := 1/4}
def Bell2 : event (pure_state 2) := {outcome := |ψ⁻⟩, probability := 1/4}
def Bell3 : event (pure_state 2) := {outcome := |φ⁺⟩, probability := 1/4}
def Bell4 : event (pure_state 2) := {outcome := |φ⁻⟩, probability := 1/4}

@[simp]
lemma tempBell1 : Bell1.probability = 1/4 := rfl
@[simp]
lemma tempBell2 : Bell2.probability = 1/4 := rfl
@[simp]
lemma tempBell3 : Bell3.probability = 1/4 := rfl
@[simp]
lemma tempBell4 : Bell4.probability = 1/4 := rfl


def Bell_die : random_variable (pure_state 2):=
{
    events := [Bell1, Bell2, Bell3, Bell4],
    normalized := by {simp, norm_num},
}

-- How do we refer to the probability associated with a given 
-- outcome? Ideally we would like to be able to say 
-- #check six_faced_die(5) and get ℝ for the type.




---- INDEPENDENT RANDOM VARIABLES

def indpndnt_rdm_vars 
{α : Type}
(XY : random_variable α) : Prop := sorry