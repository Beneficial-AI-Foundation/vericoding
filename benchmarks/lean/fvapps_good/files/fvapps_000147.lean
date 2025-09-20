-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def removeDuplicates (s : String) (k : Nat) : String := sorry

theorem result_length_le_input (s : String) (k : Nat) : 
  (removeDuplicates s k).length ≤ s.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_chars_from_input (s : String) (k : Nat) (c : Char) :
  c ∈ (removeDuplicates s k).data → c ∈ s.data := sorry

theorem result_idempotent (s : String) (k : Nat) :
  removeDuplicates (removeDuplicates s k) k = removeDuplicates s k := sorry

theorem empty_string_identity (k : Nat) :
  removeDuplicates "" k = "" := sorry

theorem k_one_no_consecutive_dupes (s : String) :
  let result := removeDuplicates s 1
  ∀ n m : Nat, n + 1 = m → m < result.length → 
    result.data[n]? ≠ result.data[m]? := sorry 

theorem k_gt_length_identity (s : String) (k : Nat) :
  k > s.length → removeDuplicates s k = s := sorry
-- </vc-theorems>