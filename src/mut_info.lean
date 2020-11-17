import shannon_theory

---- MUTUAL INFORMATION

open_locale big_operators

universe x

variables {ι : Type x} [fintype ι]
(X Y : ι → ℝ) [rnd_var X] [rnd_var Y]

/--
Definition (mutual information): Let X and Y be discrete random variables with
joint probability distribution pX,Y (x, y). The mutual information I(X; Y ) is the marginal
entropy H(X) less the conditional entropy H(X|Y):
I(X; Y ) ≡ H(X) − H(X|Y).
https://arxiv.org/pdf/1106.1445.pdf 
-/
def mut_info : ℝ := 
Shannon_entropy(X) - (cond_entropy XY X Y)

notation `I(`X`;`Y`)` := mut_info X Y

variables {X} {Y}

/--
Lemma (symmetry in the input): mutual information is symmetric in the input.
-/
@[simp] lemma mut_info_comm : I(X;Y) = I(Y;X) :=
begin
    sorry,
end

/--
Lemma (nonnegativity): The mutual information I(X;Y) is non-negative for any 
random variables X and Y :
I(X; Y ) ≥ 0.
-/
lemma mut_info_nonneg : I(X;Y) ≥ 0 := 
begin
    sorry,
end

/--
Lemma (mutual info zero iff independent random variable) : I(X;Y) = 0 if and 
only if X and Y are independent random variables (i.e., if pX,Y (x, y) =
pX(x)pY (y)).
-/
lemma mut_info_zero_iff_independent : 
I(X;Y) = 0 ↔ indpndnt_rnd_vars X Y :=
begin
    sorry,
end