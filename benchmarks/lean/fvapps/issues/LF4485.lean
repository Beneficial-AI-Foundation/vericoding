-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def same_col_seq (val k : Nat) (c : Color) : List Nat := sorry

theorem same_col_seq_valid_length (val k : Nat) (c : Color) :
  let result := same_col_seq val k c
  List.length result ≤ k := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem same_col_seq_greater_than_val (val k : Nat) (c : Color) :
  let result := same_col_seq val k c
  ∀ x ∈ result, x > val := sorry

theorem same_col_seq_ascending (val k : Nat) (c : Color) :
  let result := same_col_seq val k c
  ∀ i j, i < j → j < result.length → result[i]! < result[j]! := sorry

theorem same_col_seq_color_match (val k : Nat) (c : Color) :
  let result := same_col_seq val k c
  ∀ x ∈ result, x % 3 = c.idx := sorry

theorem same_col_seq_zero_k (val : Nat) (c : Color) :
  same_col_seq val 0 c = [] := sorry
-- </vc-theorems>