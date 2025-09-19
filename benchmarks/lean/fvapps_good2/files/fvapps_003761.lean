-- <vc-preamble>
def list_sum : List Nat → Nat
  | [] => 0
  | x::xs => x + list_sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_divs (n : Nat) : List Nat := 
  sorry

def amicable_numbers (n1 n2 : Nat) : Bool := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_divs_properties (n : Nat) (h : n > 0) :
  let divs := get_divs n
  (∀ d ∈ divs, n % d = 0) ∧
  (∀ d ∈ divs, d > 0) ∧
  (1 ∈ divs) ∧
  (n = 1 → n ∈ divs) :=
sorry

theorem amicable_symmetric_property (n : Nat) (h : n > 0) :
  let divs_sum := list_sum (get_divs n)
  (divs_sum > 0 ∧ divs_sum ≠ n) →
  amicable_numbers n divs_sum = amicable_numbers divs_sum n :=
sorry

theorem non_amicable_with_self (n : Nat) (h : n > 0) :
  ¬amicable_numbers n n :=
sorry

theorem amicable_commutative (n1 n2 : Nat) (h1 : n1 > 0) (h2 : n2 > 0) :
  amicable_numbers n1 n2 = amicable_numbers n2 n1 :=
sorry
-- </vc-theorems>