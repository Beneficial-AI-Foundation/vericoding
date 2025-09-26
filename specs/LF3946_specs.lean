-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gcd (x y : Nat) : Nat :=
sorry

def rat_at (n : Nat) : Nat × Nat :=
sorry

def index_of (a b : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
def coprime (x y : Nat) : Prop :=
  gcd x y = 1

theorem rat_at_index_inverse (n : Nat) :
  let (a, b) := rat_at n
  index_of a b = n :=
sorry

theorem base_cases :
  rat_at 0 = (1, 1) ∧
  index_of 1 1 = 0 :=
sorry
-- </vc-theorems>