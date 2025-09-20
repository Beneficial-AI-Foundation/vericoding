-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def truncateString (s : String) (n : Nat) : String := sorry

theorem truncateString_length (s : String) (n : Nat) : 
  (truncateString s n).length ≤ max n 3 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem truncateString_preserves_short (s : String) (n : Nat) :
  s.length ≤ n → truncateString s n = s := sorry

theorem truncateString_ellipsis (s : String) (n : Nat) :
  s.length > n → (truncateString s n).endsWith "..." := sorry

theorem truncateString_prefix_long (s : String) (n : Nat) :
  n > 3 → s.length > n → 
  (truncateString s n).dropRight 3 = s.take (n-3) := sorry 

theorem truncateString_prefix_short (s : String) (n : Nat) :
  n ≤ 3 → s.length > n →
  (truncateString s n).dropRight 3 = s.take n := sorry
-- </vc-theorems>