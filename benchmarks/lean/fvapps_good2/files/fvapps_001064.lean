-- <vc-preamble>
def list_sum : List Nat → Nat
  | [] => 0
  | x::xs => x + list_sum xs

def alternating_elements : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | x::_::xs => x :: alternating_elements xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_stones_removed (n : Nat) (piles : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_stones_removed_identity (n : Nat) (piles : List Nat) (h : piles.length > 0) :
  max_stones_removed n piles = max_stones_removed n piles :=
sorry

theorem max_stones_removed_n_independent (n₁ n₂ : Nat) (piles : List Nat) (h : piles.length > 0) :
  max_stones_removed n₁ piles = max_stones_removed n₂ piles :=
sorry
-- </vc-theorems>