def flatten {α : Type} : List (List α) → List α 
  | [] => sorry
  | x :: xs => sorry

-- <vc-helpers>
-- </vc-helpers>

def isNestedList {α : Type} : List (List α) → Bool
  | [] => sorry
  | x :: xs => sorry

theorem flatten_preserves_elements {α : Type} (lst : List (List α)) (inner : List α) :
  inner ∈ lst →
  ∀ x ∈ inner, x ∈ (flatten lst) :=
sorry

theorem flatten_identity_on_simple_list {α : Type} (lst : List α) :
  flatten [lst] = lst :=
sorry

theorem flatten_length_simple {α : Type} (lst : List α) :
  List.length (flatten [lst]) = List.length lst :=
sorry

theorem flatten_nested_ints (lst : List (List Int)) (n : Int) : 
  n ∈ (flatten lst) →
  ∃ inner : List Int, inner ∈ lst ∧ n ∈ inner :=
sorry

-- Apps difficulty: introductory
-- Assurance level: guarded