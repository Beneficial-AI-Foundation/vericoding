-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_f1_eq_f2 (n : Nat) (k : Nat) : Nat :=
sorry

def appears_in (d : Nat) (n : Nat) : Prop :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_f1_eq_f2_basic_case_1 :
  find_f1_eq_f2 542 5 = 547 :=
sorry

theorem find_f1_eq_f2_generates_digits (n k : Nat) (testn := find_f1_eq_f2 n k) :
  ∃ m : Nat, ∀ d : Nat, d < k → ∃ i : Nat, i ≤ m ∧ appears_in d (testn * i) :=
sorry

theorem find_f1_eq_f2_basic_case_2 :
  find_f1_eq_f2 1750 6 = 1799 :=
sorry

theorem find_f1_eq_f2_greater_than_input (n k : Nat) :
  find_f1_eq_f2 n k ≥ n :=
sorry
-- </vc-theorems>