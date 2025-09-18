-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def process_bit_queries (x : Nat) (queries : List (List Nat)) : List String :=
sorry

def countOnes (n : Nat) : Nat :=
sorry

def drop {α} (n : Nat) (xs : List α) : List α :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem binary_conversion_preserves_number (x : Nat) (h : x < 2^64) (pos : Nat)
(h2 : pos > 0 ∧ pos < 64) :
  process_bit_queries x [[1, pos]] =
    [if x &&& (1 <<< (pos - 1)) ≠ 0 then "ON" else "OFF"] :=
sorry
-- </vc-theorems>