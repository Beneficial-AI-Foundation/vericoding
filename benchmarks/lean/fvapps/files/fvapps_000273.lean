-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def palindrome_partition (s : String) (k : Nat) : Nat := sorry

theorem palindrome_partition_non_negative 
  (s : String) (k : Nat) (h: k > 0) (h2: k ≤ s.length) :
  palindrome_partition s k ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem palindrome_partition_full_length
  (s : String) (h: s.length > 0) :
  palindrome_partition s s.length = 0 := sorry

theorem palindrome_partition_bounded
  (s : String) (k : Nat) (h: k > 0) (h2: k ≤ s.length) :
  palindrome_partition s k ≤ s.length := sorry

theorem palindrome_partition_single 
  (s : String) (h: s.length > 0) :
  palindrome_partition s 1 = palindrome_partition s 1 := sorry

theorem palindrome_partition_individual_chars
  (s : String) (h: s.length > 0) :
  palindrome_partition s s.length = 0 := sorry
-- </vc-theorems>