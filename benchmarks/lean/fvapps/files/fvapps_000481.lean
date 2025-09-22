-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def strWithout3a3b (a b : Nat) : String :=
  sorry

def count_char (s : String) (c : Char) : Nat :=
  sorry

def contains_substring (s main : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def is_valid_string (s : String) (a_count b_count : Nat) : Prop :=
  count_char s 'a' = a_count ∧
  count_char s 'b' = b_count ∧
  ¬contains_substring "aaa" s ∧
  ¬contains_substring "bbb" s

theorem equal_counts {n : Nat} (h : n > 0) :
  let s := strWithout3a3b n n
  is_valid_string s n n ∧ s.length = 2 * n
  :=
sorry

theorem double_a_count {n : Nat} :
  let s := strWithout3a3b (2 * n) n
  is_valid_string s (2 * n) n ∧ s.length = 3 * n
  :=
sorry
-- </vc-theorems>