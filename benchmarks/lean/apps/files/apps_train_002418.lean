-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_lucky (arr : List Nat) : Int := sorry

theorem find_lucky_lower_bound (arr : List Nat) : 
  find_lucky arr ≥ -1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_lucky_freq_match (arr : List Nat) :
  find_lucky arr ≠ -1 → 
  (arr.countP (· = (find_lucky arr).toNat)) = (find_lucky arr).toNat := sorry 

theorem find_lucky_is_max (arr : List Nat) (n : Nat) :
  n ∈ arr → 
  (arr.countP (· = n)) = n →
  n ≤ (find_lucky arr).toNat := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_lucky [2, 2, 3, 4]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_lucky [1, 2, 2, 3, 3, 3]

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_lucky [2, 2, 2, 3, 3]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible