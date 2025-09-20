-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.padRight (default : α) (n : Nat) (xs : List α) : List α :=
  sorry

def find_weird_distance (n : Nat) (alice_speeds : List Nat) (bob_speeds : List Nat) : Nat :=
  sorry

def running_sum_equal (alice_speeds bob_speeds : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem identical_speeds_sum_to_length
  (n : Nat)
  (h1 : n > 0)
  (h2 : n ≤ 100) :
  find_weird_distance n (List.replicate n 1) (List.replicate n 1) = n :=
sorry
-- </vc-theorems>