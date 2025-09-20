-- <vc-preamble>
def list_sum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => x + list_sum rest
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def expanded_form (n : Nat) : String := sorry

def string_to_nat (s : String) : Nat :=
sorry

def list_sorted_desc (xs : List Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem expanded_form_sum_equals_input (n : Nat) (h : 0 < n) (h2 : n ≤ 1000000) :
  let parts := (expanded_form n).split (· = '+')
  list_sum (parts.map string_to_nat) = n :=
sorry

theorem expanded_form_divisible_by_powers_of_ten (n : Nat) (h : 0 < n) (h2 : n ≤ 1000000) :
  let parts := (expanded_form n).split (· = '+')
  ∀ (i : Nat) (p : String), i < parts.length → p ∈ parts →
  string_to_nat p % (10^i) = 0 :=
sorry

theorem expanded_form_no_leading_zeros (n : Nat) (h : 0 < n) :
  let parts := (expanded_form n).split (· = '+')
  ∀ p ∈ parts, ¬(p.get? 0 = some '0') :=
sorry

theorem expanded_form_descending_order (n : Nat) (h : 0 < n) :
  let parts := (expanded_form n).split (· = '+')
  let nums := parts.map string_to_nat
  list_sorted_desc nums = true :=
sorry

theorem expanded_form_single_digit (n : Nat) (h : 0 < n) (h2 : n < 10) :
  expanded_form n = toString n :=
sorry
-- </vc-theorems>