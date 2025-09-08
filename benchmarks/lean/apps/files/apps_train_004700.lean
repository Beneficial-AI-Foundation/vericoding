/-
Your task is to implement a function that takes one or more dictionaries and combines them in one result dictionary.

The keys in the given dictionaries can overlap. In that case you should combine all source values in an array. Duplicate values should be preserved.

Here is an example:
```cs
var source1 = new Dictionary{{"A", 1}, {"B", 2}}; 
var source2 = new Dictionary{{"A", 3}};

Dictionary result = DictionaryMerger.Merge(source1, source2);
// result should have this content: {{"A", [1, 3]}, {"B", [2]}}

```
```python
source1 = {"A": 1, "B": 2} 
source2 = {"A": 3}

result = merge(source1, source2);
// result should have this content: {"A": [1, 3]}, "B": [2]}

```

You can assume that only valid dictionaries are passed to your function.
The number of given dictionaries might be large. So take care about performance.
-/

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