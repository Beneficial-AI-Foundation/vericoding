-- <vc-preamble>
def List.sum : List Nat → Nat
  | [] => 0
  | x::xs => x + sum xs

def List.minimum : (l : List Nat) → l ≠ [] → Nat
  | [], h => by contradiction
  | [x], _ => x
  | (x::y::xs), _ => Nat.min x (minimum (y::xs) (by simp))
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.sublist (l : List Nat) (i j : Nat) : List Nat := sorry

def least_bribes (bribes : List Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem least_bribes_bounded
  (bribes : List Nat)
  (h : bribes ≠ []) :
  let result := least_bribes bribes
  result ≤ List.sum bribes ∧ result ≥ List.minimum bribes h := sorry

theorem least_bribes_increasing
  (bribes : List Nat)
  (h : bribes ≠ []) :
  let increased := bribes.map (· + 1)
  least_bribes increased > least_bribes bribes := sorry

theorem least_bribes_subarray
  (bribes : List Nat)
  (i j : Nat)
  (h1 : i < bribes.length)
  (h2 : j < bribes.length)
  (h3 : i < j) :
  let subarray := List.sublist bribes i j
  least_bribes subarray ≤ least_bribes bribes := sorry

/-
info: 26
-/
-- #guard_msgs in
-- #eval least_bribes [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-
info: 5
-/
-- #guard_msgs in
-- #eval least_bribes [5]

/-
info: 20
-/
-- #guard_msgs in
-- #eval least_bribes [10, 10, 10]
-- </vc-theorems>