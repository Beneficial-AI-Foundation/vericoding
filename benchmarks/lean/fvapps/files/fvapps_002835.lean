-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def last_digits (n : Nat) (d : Int) : List Nat :=
sorry

def list_to_string (l : List Nat) : String :=
sorry

def nat_to_string (n : Nat) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem last_digits_empty_for_nonpositive (n : Nat) (d : Int) :
  d <= 0 → last_digits n d = [] :=
sorry

theorem last_digits_length_bound (n : Nat) (d : Int) :
  d > 0 → List.length (last_digits n d) = min d.toNat (nat_to_string n).length :=
sorry

theorem last_digits_are_digits (n : Nat) (d : Int) (x : Nat) :
  x ∈ last_digits n d → x ≤ 9 :=
sorry

theorem last_digits_match_string_suffix (n : Nat) (d : Int) :
  d > 0 → list_to_string (last_digits n d) = (nat_to_string n).takeRight d.toNat :=
sorry

theorem last_digits_full_number (n : Nat) :
  list_to_string (last_digits n ((nat_to_string n).length + 1)) = nat_to_string n :=
sorry
-- </vc-theorems>