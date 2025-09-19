-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum_ints (xs : List Int) : Int :=
  sorry

def range (n : Int) : List Int :=
  sorry

def arithmetic_sequence_sum (a r n : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem arithmetic_sequence_properties
  (a r n : Int)
  (h : n > 0) :
  let sum := arithmetic_sequence_sum a r n
  let manual_sum := sum_ints (range n |>.map (fun i => a + r * i))
  (sum = manual_sum) ∧
  (arithmetic_sequence_sum a r 1 = a) ∧
  (n > 1 → sum = arithmetic_sequence_sum a r (n-1) + (a + (n-1)*r)) :=
sorry

theorem sequence_symmetry
  (a r n : Int)
  (h : n > 0) :
  let last := a + (n-1)*r
  arithmetic_sequence_sum a r n = arithmetic_sequence_sum last (-r) n :=
sorry
-- </vc-theorems>