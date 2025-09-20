-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def friends (n : Nat) : Nat := sorry

theorem zero_or_one_jar_no_friends (n : Nat) (h : n ≤ 1) : friends n = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sufficient_friends (n : Nat) (h : n ≥ 2) : 
  2^(friends n + 1) ≥ n := sorry

theorem friends_monotone (n : Nat) (h : n ≥ 2) :
  friends n ≥ friends (n-1) := sorry
-- </vc-theorems>