-- <vc-helpers>
-- </vc-helpers>

def createDict : List String → List Int → List (String × (Option Int)) 
  | _, _ => sorry

theorem createDict_length (keys : List String) (values : List Int) :
  List.length (createDict keys values) = List.length keys := sorry

theorem createDict_elements (keys : List String) (values : List Int) :
  (∀ (i : Nat), i < keys.length →
    match createDict keys values with
    | (k, v) :: _ => 
      if h : i < values.length then
        v = some (values.get ⟨i, h⟩)
      else
        v = none
    | _ => True) := sorry

theorem createDict_null_elements (keys : List String) (values : List Int) 
  (h₁: 1 ≤ keys.length) (h₂: values.length = 0) :
  ∃ (x : Option Int), x = none ∧ x ∈ (createDict keys values).map Prod.snd := sorry

theorem createDict_all_ints (keys : List String) (values : List Int)
  (h₁: keys.length ≤ 3) (h₂: 4 ≤ values.length) :
  ∀ x ∈ (createDict keys values).map Prod.snd, ∃ (n : Int), x = some n := sorry

/-
info: {}
-/
-- #guard_msgs in
-- #eval createDict [] []

/-
info: {'a': 1, 'b': None, 'c': None}
-/
-- #guard_msgs in
-- #eval createDict ["a", "b", "c"] [1]

/-
info: {'a': 1, 'b': 2}
-/
-- #guard_msgs in
-- #eval createDict ["a", "b"] [1, 2, 3, 4]

-- Apps difficulty: introductory
-- Assurance level: unguarded