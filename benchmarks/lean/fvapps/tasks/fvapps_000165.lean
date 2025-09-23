-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_construct_palindromes (s : String) (k : Int) : Bool := sorry

theorem k_greater_than_length_is_false {s : String} {k : Int} :
  k > s.length → ¬can_construct_palindromes s k := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem palindrome_negative_k {s : String} {k : Int} :
  k < 0 → ¬can_construct_palindromes s k := sorry

theorem palindrome_k_vs_odd_counts {s : String} {k : Int} : 
  can_construct_palindromes s k → k ≥ (s.data.countP (fun c => (s.data.count c) % 2 = 1)) := sorry

theorem sufficient_k_works {s : String} :
  s.length > 0 → can_construct_palindromes s s.length := sorry

theorem single_char_case {s : String} {k : Int} :
  s.length = 1 → (can_construct_palindromes s k ↔ k ≥ 1) := sorry

theorem all_same_char {s : String} {k : Int} :
  s.length > 0 → (∀ (i : Nat), i < s.length → s.data[i]? = s.data[0]?) →
  (can_construct_palindromes s k ↔ k ≥ s.length % 2) := sorry
-- </vc-theorems>