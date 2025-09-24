-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def add_strings (a b : String) : String :=
  sorry

def int_to_str (n : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem add_strings_matches_int_addition
  (a b : Nat) (h1 : a ≤ 10^6) (h2 : b ≤ 10^6) :
  add_strings (int_to_str a) (int_to_str b) = int_to_str (a + b) :=
sorry

theorem add_zero_right (n : Nat) (h : n ≤ 10^6) :
  add_strings (int_to_str n) "0" = int_to_str n :=
sorry

theorem add_zero_left (n : Nat) (h : n ≤ 10^6) :
  add_strings "0" (int_to_str n) = int_to_str n :=
sorry

theorem add_strings_commutative (n : Nat) (h : n ≤ 10^6) :
  add_strings (int_to_str n) (int_to_str 42) =
  add_strings (int_to_str 42) (int_to_str n) :=
sorry
-- </vc-theorems>