-- <vc-preamble>
def zozonacci (pattern : List String) (n : Nat) : List Nat := sorry

def isNonNegative (l : List Nat) : Prop := 
  ∀ x ∈ l, x ≥ 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isMonotonicFrom (l : List Nat) (start : Nat) : Prop :=
  ∀ i v1 v2, start ≤ i → i < l.length - 1 → l[i]? = some v1 → l[i+1]? = some v2 → v1 ≤ v2
-- </vc-definitions>

-- <vc-theorems>
theorem empty_pattern_returns_empty (n : Nat) :
  zozonacci [] n = [] := sorry

/-
info: []
-/
-- #guard_msgs in
-- #eval zozonacci [] 10

/-
info: [0, 0, 0, 1, 1, 2, 3, 5, 8, 13]
-/
-- #guard_msgs in
-- #eval zozonacci ["fib"] 10

/-
info: [0, 0, 0, 1, 1, 2, 3]
-/
-- #guard_msgs in
-- #eval zozonacci ["fib", "tri"] 7
-- </vc-theorems>