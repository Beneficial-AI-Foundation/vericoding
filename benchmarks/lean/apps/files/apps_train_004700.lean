-- <vc-helpers>
-- </vc-helpers>

def Map (α : Type) (β : Type) := α → Option β

def merge {α β : Type} (dicts : List (Map α β)) : Map α (List β) := sorry

theorem merge_keys_preserved
  {α β : Type} [BEq α] [BEq β]
  (dicts : List (Map α β))
  (k : α) :
  (∃ d ∈ dicts, (d k).isSome) ↔ (merge dicts k).isSome :=
sorry

theorem merge_list_lengths
  {α β : Type} [BEq α] [BEq β]
  (dicts : List (Map α β))
  (k : α)
  (h : (merge dicts k).isSome) :
  ((merge dicts k).getD []).length = 
    (dicts.filter (fun d => (d k).isSome)).length :=
sorry

theorem merge_single_dict
  {α β : Type} [BEq α] [BEq β] [Inhabited β]
  (d : Map α β)
  (k : α)
  (h : (d k).isSome) :
  ∃ v : β, ((merge [d] k).getD []) = [v] ∧ (d k) = some v :=
sorry

theorem merge_empty
  {α β : Type} [BEq α] [BEq β]
  (k : α) :
  merge ([] : List (Map α β)) k = none :=
sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval merge {"A": 1, "B": 2} {"A": 3}

/-
info: expected2
-/
-- #guard_msgs in
-- #eval merge {"A": 1, "B": 2} {"A": 1, "B": 3}

/-
info: expected3
-/
-- #guard_msgs in
-- #eval merge {"A": 1} {}

-- Apps difficulty: introductory
-- Assurance level: unguarded