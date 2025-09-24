-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_split_dosas_evenly (n : Nat) : String := sorry

theorem can_split_dosas_evenly_returns_valid_result (n : Nat) :
  can_split_dosas_evenly n = "YES" ∨ can_split_dosas_evenly n = "NO" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem can_split_dosas_evenly_matches_parity (n : Nat) :
  can_split_dosas_evenly n = (if n % 2 = 0 then "YES" else "NO") := sorry

theorem even_numbers_are_splittable {n : Nat} (h : n % 2 = 0) :
  can_split_dosas_evenly n = "YES" := sorry

theorem odd_numbers_are_not_splittable {n : Nat} (h : n % 2 ≠ 0) :
  can_split_dosas_evenly n = "NO" := sorry
-- </vc-theorems>