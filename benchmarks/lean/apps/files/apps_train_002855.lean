-- <vc-helpers>
-- </vc-helpers>

def argsCount {α : Type} (args : List α) : Nat := sorry

theorem argsCount_equals_list_length {α : Type} (args : List α) : 
  argsCount args = args.length := by sorry

theorem argsCount_with_mixed_types {α β : Type} (args : List (Sum α β)) :
  argsCount args = args.length := by sorry

theorem argsCount_with_kwargs (map : List (String × Nat)) :
  argsCount map = map.length := by sorry

theorem argsCount_mixed_total {α : Type} (args : List α) (kwargs : List (String × α)) :
  argsCount args + argsCount kwargs = args.length + kwargs.length := by sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval args_count 1

/-
info: 3
-/
-- #guard_msgs in
-- #eval args_count 1 2 3

/-
info: 2
-/
-- #guard_msgs in
-- #eval args_count 

/-
info: 4
-/
-- #guard_msgs in
-- #eval args_count 1 2

-- Apps difficulty: introductory
-- Assurance level: unguarded