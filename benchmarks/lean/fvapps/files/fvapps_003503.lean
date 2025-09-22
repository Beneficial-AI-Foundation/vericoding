-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (idx : Nat) : Int :=
sorry

def has_matching_parens (s : String) : Bool :=
sorry

def is_valid_idx (s : String) (idx : Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_invalid_index {s : String} {idx : Nat} :
  ¬(is_valid_idx s idx) → solve s idx = -1 :=
sorry

theorem solve_unmatched_parens {s : String} {idx : Nat} :
  ¬(has_matching_parens s) → solve s idx = -1 :=
sorry

theorem solve_valid_result {s : String} {idx : Nat} :
  (solve s idx ≠ -1) →
  is_valid_idx s idx ∧
  (∃ result : Nat, solve s idx = result ∧
    idx < s.length ∧ result < s.length ∧
    s.data[idx]! = '(' ∧
    s.data[result]! = ')' ∧
    has_matching_parens (String.mk (List.take (result + 1 - idx) (List.drop idx s.data)))) :=
sorry

theorem solve_all_open_parens {s : String} :
  (∀ c ∈ s.data, c = '(') →
  ∀ i : Nat, i < s.length →
  solve s i = -1 :=
sorry

theorem solve_all_close_parens {s : String} :
  (∀ c ∈ s.data, c = ')') →
  ∀ i : Nat, i < s.length →
  solve s i = -1 :=
sorry
-- </vc-theorems>