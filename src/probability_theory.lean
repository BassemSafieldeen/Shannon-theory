import data.real.basic

    --    .-------.    ______
    --   /   o   /|   /\     \
    --  /_______/o|  /o \  o  \
    --  | o     | | /   o\_____\
    --  |   o   |o/ \o   /o    /
    --  |     o |/   \ o/  o  /
    --  '-------'     \/____o/

def cond_prob (AB : multiset (multiset ℝ)) (a b : ℕ) : ℝ := 
AB(a,b) / (∑ x, AB(x,b))

