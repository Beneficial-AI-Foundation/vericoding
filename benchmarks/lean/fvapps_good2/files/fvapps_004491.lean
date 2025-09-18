-- <vc-preamble>
inductive Category where
  | fruit : Category
  | meat : Category
  | vegetable : Category
  | other : Category
deriving BEq, Repr

structure GroceryItem where
  category : Category
  name : String
deriving Repr

def length4 (s : List α) : Prop := s.length = 4

inductive isSorted : List String → Prop where
  | nil : isSorted []
  | single : (x : String) → isSorted [x]
  | cons : (x y : String) → (rest : List String) →
          x <= y → isSorted (y::rest) → isSorted (x::y::rest)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def group_groceries (input : String) : String :=
  sorry

def isValidCategoryName (name : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem group_groceries_produces_four_lines (input : String) :
  length4 ((group_groceries input).splitOn "\n") :=
sorry

theorem group_groceries_uses_expected_categories (input : String) :
  let lines := (group_groceries input).splitOn "\n"
  lines[0]!.startsWith "fruit:" ∧
  lines[1]!.startsWith "meat:" ∧
  lines[2]!.startsWith "other:" ∧
  lines[3]!.startsWith "vegetable:" :=
sorry

theorem group_groceries_items_sorted (input : String) (i : Nat) :
  let lines := (group_groceries input).splitOn "\n"
  let items := (lines[i]!.splitOn ":")[1]!.splitOn ","
  items.length > 0 → isSorted items :=
sorry
-- </vc-theorems>