-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_pizza_time (n : Nat) (k : Nat) (s : String) : Nat :=
  sorry

def count_ones (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_pizza_time_bounds (n k: Nat) (s: String) :
  n > 0 → s.length = n →
  let result := max_pizza_time n k s
  0 ≤ result ∧ result ≤ n :=
sorry

theorem max_pizza_time_upper_bound (n k: Nat) (s: String) :
  n > 0 → s.length = n →
  max_pizza_time n k s ≤ n :=
sorry

theorem max_pizza_time_all_ones (n: Nat) :
  n > 0 →
  let s := String.mk (List.replicate n '1')
  max_pizza_time n 0 s = n :=
sorry

theorem max_pizza_time_all_zeros (n: Nat) :
  n > 0 →
  let s := String.mk (List.replicate n '0')
  let k := n / 2
  max_pizza_time n k s = k :=
sorry
-- </vc-theorems>