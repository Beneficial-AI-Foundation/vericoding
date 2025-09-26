-- <vc-preamble>
def List.sum : List Nat → Nat 
| [] => 0
| x::xs => x + List.sum xs

def List.minimum : List Nat → Option Nat
| [] => none
| [x] => some x
| x::xs => match List.minimum xs with
  | none => some x
  | some m => some (min x m)

def min_dessert_cost (n : Nat) (costs : List Nat) : Nat := sorry

theorem min_dessert_cost_uniform (n : Nat)
  (h1 : n ≥ 3) :
  min_dessert_cost n (List.replicate n 1) = (n + 1) / 2 := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def alternating_sums (costs : List Nat) : Nat × Nat :=
  let rec helper (xs : List Nat) (isEven : Bool) : Nat × Nat :=
    match xs with
    | [] => (0, 0)
    | x::xs => 
      let (evens, odds) := helper xs (!isEven)
      if isEven then (evens + x, odds)
      else (evens, odds + x)
  helper costs true
-- </vc-definitions>

-- <vc-theorems>
/-
info: 4
-/
-- #guard_msgs in
-- #eval min_dessert_cost 5 [1, 2, 1, 2, 2]

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_dessert_cost 3 [1, 2, 3]

/-
info: 20
-/
-- #guard_msgs in
-- #eval min_dessert_cost 4 [5, 10, 15, 20]
-- </vc-theorems>