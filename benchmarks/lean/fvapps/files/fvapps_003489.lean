-- <vc-preamble>
def toBase (num base : Nat) : String :=
  sorry

def sumItUp (nums : List (String × Nat)) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumList (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: xs => x + sumList xs
-- </vc-definitions>

-- <vc-theorems>
theorem sum_it_up_equals_decimal_sum {nums : List (Nat × Nat)} :
  ∀ pairs : List (String × Nat),
  (∀ p : String × Nat, p ∈ pairs → 
    ∃ n ∈ nums, p.1 = toBase n.1 p.2) →
  sumItUp pairs = sumList (nums.map Prod.fst) := 
sorry

theorem sum_it_up_empty : sumItUp [] = 0 :=
sorry

theorem sum_it_up_single {n : String} {b : Nat} :
  b ≥ 2 → b ≤ 36 →
  ∃ k : Nat, sumItUp [(n, b)] = k :=
sorry

theorem base_conversion_roundtrip {n : Nat} {b : Nat} :
  n ≤ 1000000 → b ≥ 2 → b ≤ 36 →
  ∃ k : Nat, k = n ∧ String.toNat! (toBase n b) = k :=
sorry

/-
info: 13
-/
-- #guard_msgs in
-- #eval sum_it_up [["101", 2], ["10", 8]]

/-
info: 2751
-/
-- #guard_msgs in
-- #eval sum_it_up [["ABC", 16], ["11", 2]]

/-
info: 4258
-/
-- #guard_msgs in
-- #eval sum_it_up [["101", 16], ["7640", 8], ["1", 9]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval sum_it_up []
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded