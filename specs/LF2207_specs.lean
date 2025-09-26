-- <vc-preamble>
def solve (n : Nat) (arr : List Nat) : List Nat × List Nat := sorry

def abs (n m : Nat) : Nat :=
  if n ≥ m then n - m else m - n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def allDiffs (nums : List Nat) : List Nat :=
  (List.range nums.length).bind (fun i =>
    (List.range (nums.length - i - 1)).map (fun j =>
      abs (nums[i]!) (nums[i + j + 1]!)))

def disjoint (l1 l2 : List Nat) : Prop :=
  ∀ x, x ∈ l1 → x ∉ l2
-- </vc-definitions>

-- <vc-theorems>
theorem solve_output_length {n : Nat} {arr : List Nat} :
  let (_, nums) := solve n arr
  nums.length = n :=
sorry

theorem solve_different_diffs {n : Nat} {arr : List Nat} :
  let (_, nums) := solve n arr
  disjoint (allDiffs nums) (allDiffs arr) :=
sorry

theorem solve_positive {n : Nat} {arr : List Nat} :
  let (_, nums) := solve n arr
  ∀ i, i < nums.length → nums[i]! > 0 :=
sorry

theorem solve_increasing {n : Nat} {arr : List Nat} :
  let (_, nums) := solve n arr
  ∀ i, i < nums.length - 1 → nums[i]! < nums[i + 1]! :=
sorry

theorem solve_works {arr : List Nat} (h : arr.length > 0) :
  let (res, nums) := solve arr.length arr
  nums.length = arr.length ∧
  disjoint (allDiffs nums) (allDiffs arr) ∧
  (∀ i, i < nums.length → nums[i]! > 0) ∧
  (∀ i, i < nums.length - 1 → nums[i]! < nums[i + 1]!) :=
sorry

/-
info: ('YES', [1, 2, 3])
-/
-- #guard_msgs in
-- #eval solve 3 [1, 10, 100]

/-
info: ('YES', [1])
-/
-- #guard_msgs in
-- #eval solve 1 [1]

/-
info: ('YES', [1, 2])
-/
-- #guard_msgs in
-- #eval solve 2 [2, 4]
-- </vc-theorems>