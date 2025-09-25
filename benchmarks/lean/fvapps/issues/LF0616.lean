-- <vc-preamble>
def List.sum : List Nat → Nat
| [] => 0
| (h::t) => h + List.sum t

def solve (arr : List Nat) (n k : Nat) : Nat :=
  sorry

def windowSum (arr : List Nat) (start len : Nat) : Nat :=
  (arr.take (start + len)).drop start |>.sum
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countWindows (arr : List Nat) (n k : Nat) : Nat :=
  let windows := List.range (n - k + 1)
  windows.filter (fun i => windowSum arr i k = k) |>.length
-- </vc-definitions>

-- <vc-theorems>
theorem solve_basic_properties 
  (arr : List Nat) 
  (n k : Nat)
  (h1 : ∀ x ∈ arr, x ≤ 1)
  (h2 : k ≤ n)
  (h3 : n = arr.length) :
  let result := solve arr n k
  -- Result is non-negative
  (result ≥ 0) ∧ 
  -- Result does not exceed max possible windows
  (result ≤ n - k + 1) ∧
  -- For k=1, result equals sum of array
  (k = 1 → result = List.sum arr) ∧
  -- For array of all 1s, result equals n-k+1
  ((∀ x ∈ arr, x = 1) → result = n - k + 1) :=
  sorry

theorem solve_equals_manual_count
  (arr : List Nat)
  (n k : Nat) 
  (h1 : ∀ x ∈ arr, x ≤ 1)
  (h2 : k ≤ n)
  (h3 : n = arr.length)
  (h4 : n > 0) :
  solve arr n k = countWindows arr n k :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve [1, 1, 0, 1] 4 2

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve [1, 1, 1] 3 2

/-
info: 5
-/
-- #guard_msgs in
-- #eval solve [1, 1, 1, 1, 1, 0, 1, 1, 1, 1] 10 3
-- </vc-theorems>