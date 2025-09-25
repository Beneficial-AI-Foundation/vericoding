-- <vc-preamble>
def List.sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: xs => x + List.sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def f (n m : Nat) : Nat := sorry

theorem result_non_negative (n m : Nat) (hn : n > 0) (hm : m > 0) :
  f n m ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem monotonic_increase (n delta m : Nat) 
  (hn : n > 0) (hd : delta > 0) (hm : m > 0) :
  f (n + delta) m ≥ f n m := sorry

theorem base_case_one (m : Nat) (hm : m > 1) :
  f 1 m = 1 % m := sorry

/-
info: 20
-/
-- #guard_msgs in
-- #eval f 10 5

/-
info: 6
-/
-- #guard_msgs in
-- #eval f 5 3

/-
info: 12
-/
-- #guard_msgs in
-- #eval f 7 4
-- </vc-theorems>