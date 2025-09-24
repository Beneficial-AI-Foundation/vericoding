-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.sort : List Nat → List Nat := sorry

def solve_bus_payback (n p q : Nat) (amounts : List Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_bounds (n p q : Nat) (amounts : List Nat) 
  (h : amounts.length = n) :
  let result := solve_bus_payback n p q amounts
  0 ≤ result ∧ result ≤ n := sorry

theorem zero_money_zero_creatures (n : Nat) (amounts : List Nat)
  (h : amounts.length = n) :
  solve_bus_payback n 0 0 amounts = 0 := sorry

theorem enough_money_even_amounts (n p q : Nat) (amounts : List Nat)
  (h1 : amounts.length = n)
  (h2 : ∀ i < n, amounts.get ⟨i, sorry⟩ = 2 * (i + 1))
  (h3 : p + 2*q ≥ List.sum amounts) :
  solve_bus_payback n p q amounts = n := sorry

theorem sorting_invariant (n p q : Nat) (amounts : List Nat)
  (h : amounts.length = n) :
  solve_bus_payback n p q amounts = 
  solve_bus_payback n p q (List.sort amounts) := sorry
-- </vc-theorems>