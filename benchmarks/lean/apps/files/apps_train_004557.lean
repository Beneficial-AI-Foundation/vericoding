-- <vc-preamble>
def spread {α β : Type u} (f : α → β) (args : List α) : β :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | h :: t => h + sum t
-- </vc-definitions>

-- <vc-theorems>
theorem spread_matches_direct_call {α β : Type u} (f : α → β) (x : α) : 
  spread f [x] = f x :=
sorry

theorem spread_list_sum (nums : List Nat) :
  spread (fun xs => sum xs) [nums] = sum nums :=
sorry

theorem spread_concat_strings (strings : List String) :
  spread (fun args => String.join args) [strings] = String.join strings :=
sorry

theorem spread_empty_unit (f : Unit → Option α) :
  spread f [] = f () :=
sorry

theorem spread_single_identity :
  spread (fun x:Nat => x) [42] = 42 :=
sorry

theorem spread_too_many_args_fails :
  ¬(∃ (res:Nat), spread (fun x:Nat => x) [1, 2] = res) :=
sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval spread lambda x, y: x + y [2, 3]

/-
info: 'abc'
-/
-- #guard_msgs in
-- #eval spread lambda x, y, z: x + y + z ["a", "b", "c"]

/-
info: 42
-/
-- #guard_msgs in
-- #eval spread lambda: 42 []
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded