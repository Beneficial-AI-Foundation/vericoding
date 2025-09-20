-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sequence (n : Nat) : Nat :=
sorry

def toBinaryString (n : Nat) : List Nat :=
sorry

def fromBase3 (digits : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sequence_nonnegative (n : Nat) :
  sequence n ≥ 0 :=
sorry

theorem sequence_monotonic {n : Nat} (h : n > 0) :
  sequence n > sequence (n - 1) :=
sorry
-- </vc-theorems>