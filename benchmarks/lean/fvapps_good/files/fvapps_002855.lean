-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def argsCount {α : Type} (args : List α) : Nat := sorry

theorem argsCount_equals_list_length {α : Type} (args : List α) : 
  argsCount args = args.length := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem argsCount_with_mixed_types {α β : Type} (args : List (Sum α β)) :
  argsCount args = args.length := by sorry

theorem argsCount_with_kwargs (map : List (String × Nat)) :
  argsCount map = map.length := by sorry

theorem argsCount_mixed_total {α : Type} (args : List α) (kwargs : List (String × α)) :
  argsCount args + argsCount kwargs = args.length + kwargs.length := by sorry
-- </vc-theorems>