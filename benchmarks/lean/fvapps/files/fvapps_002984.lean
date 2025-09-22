-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def climb (n : Nat) : List Nat := sorry

theorem climb_starts_with_one {n : Nat} (h : n > 0) :
  (climb n).head? = some 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem climb_ends_with_input {n : Nat} (h : n > 0) :
  (climb n).getLast? = some n := sorry

theorem climb_strictly_increasing {n : Nat} (h : n > 0) :
  ∀ i : Nat, i + 1 < (climb n).length →
  (climb n)[i]! < (climb n)[i + 1]! := sorry

theorem climb_length_logarithmic {n : Nat} (h : n > 0) :
  (climb n).length ≤ 2 * Nat.log2 n + 2 := sorry

theorem climb_invalid_input (n : Nat) :
  n = 0 → climb n = [] := sorry
-- </vc-theorems>