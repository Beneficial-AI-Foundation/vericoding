def isSubsequence (smaller larger : String) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def solve (n : Nat) (k : Nat) : String :=
  sorry

theorem solve_properties {n k : Nat} (h : k < (ToString.toString n).length) :
  let result := solve n k
  (result.length = (ToString.toString n).length - k) ∧ 
  (isSubsequence result (ToString.toString n) = true) ∧
  (result.toNat! ≤ n) :=
sorry

theorem remove_zero_digits (n : Nat) :
  solve n 0 = ToString.toString n :=
sorry

theorem result_is_minimal {n k : Nat} (h1 : n ≥ 10) (h2 : k ≥ 1) (h3 : k < (ToString.toString n).length) :
  let result := solve n k
  ∀ (s : String), 
    isSubsequence s (ToString.toString n) = true → 
    s.length = (ToString.toString n).length - k →
    result.toNat! ≤ s.toNat! :=
sorry

/-
info: '05'
-/
-- #guard_msgs in
-- #eval solve 123056 4

/-
info: '12456'
-/
-- #guard_msgs in
-- #eval solve 1284569 2

/-
info: '12056'
-/
-- #guard_msgs in
-- #eval solve 123056 1

-- Apps difficulty: introductory
-- Assurance level: unguarded