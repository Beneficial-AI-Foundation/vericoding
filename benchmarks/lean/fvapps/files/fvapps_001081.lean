-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_operations_to_alternating (n : Nat) (s : String) : Nat :=
  sorry

def is_alternating (s : String) : Bool :=
  sorry

def make_alternating_01 (n : Nat) : String :=
  sorry

def make_alternating_10 (n : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem uniform_string_flips (n : Nat) (c : Char) :
  let s := String.mk (List.replicate n c)
  let ops := min_operations_to_alternating n s
  ops = n/2 ∨ ops = (n+1)/2 :=
sorry

theorem length_result_bounded (n : Nat) (s : String) :
  s.length = n →
  let ops := min_operations_to_alternating n s
  0 ≤ ops ∧ ops ≤ n :=
sorry
-- </vc-theorems>