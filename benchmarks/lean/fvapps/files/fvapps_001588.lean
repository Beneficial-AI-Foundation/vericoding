-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def green (n : Nat) : Nat :=
  sorry

def first_5_green_numbers (n : Nat) (h : n > 0 ∧ n ≤ 5) :
  green n = match n with
    | 1 => 1
    | 2 => 5
    | 3 => 6
    | 4 => 25
    | 5 => 76
    | _ => 0 :=
  sorry

def green_number_positive (n : Nat) (h : n > 0) :
  green n > 0 :=
  sorry

def green_numbers_ordered (n : Nat) (h : n > 1) :
  green n > green (n-1) :=
  sorry

def green_numbers_unique (n m : Nat) (h1 : n > 0) (h2 : m > 0) (h3 : n ≠ m) :
  green n ≠ green m :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>