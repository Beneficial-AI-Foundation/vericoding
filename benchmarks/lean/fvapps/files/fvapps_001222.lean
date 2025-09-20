-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def base5 (n : Nat) : List Nat :=
sorry

def seq (n : Nat) : Nat :=
sorry

def get_kth_magical_number (k : Nat) : Nat :=
sorry

def digitList (n : Nat) : List Nat :=
sorry

def isEvenDigit (n : Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem base5_zero :
  base5 0 = [] :=
sorry

theorem base5_digits_bounded (n : Nat) :
  ∀ d ∈ base5 n, 0 ≤ d ∧ d ≤ 4 :=
sorry

theorem magical_increasing (k : Nat) :
  k > 1 →
  get_kth_magical_number (k-1) < get_kth_magical_number k :=
sorry
-- </vc-theorems>