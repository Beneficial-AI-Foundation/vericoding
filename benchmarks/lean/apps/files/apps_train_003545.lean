-- <vc-preamble>
def isInt (n : Nat) : Bool := sorry
def isDiceList (l : List Nat) : Bool := sorry

def isValidDiceDesc : String → Bool := sorry
def extractSides : String → Option Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def roll (desc : String) (verbose : Bool := false) : Bool ⊕ (List Nat × Int) := sorry

theorem valid_roll_structure {desc : String} {result : List Nat × Int}
  (h : roll desc true = Sum.inr result) :
  ∃ (dice : List Nat) (modifier : Int), result = (dice, modifier) ∧ 
  ∀ d ∈ dice, isInt d := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_roll {desc : String} (h : ¬isValidDiceDesc desc) : 
  roll desc false = Sum.inl false := sorry

theorem non_string_input {α : Type} {x : α} [ToString α] : 
  roll (toString x) false = Sum.inl false := sorry

theorem roll_range_properties {desc : String} {result : List Nat × Int} {sides : Nat} 
  (h₁ : roll desc true = Sum.inr result)
  (h₂ : extractSides desc = some sides) :
  ∀ die ∈ result.1, 1 ≤ die ∧ die ≤ sides := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval roll ""

/-
info: False
-/
-- #guard_msgs in
-- #eval roll {}

/-
info: False
-/
-- #guard_msgs in
-- #eval roll "abc"

/-
info: 2
-/
-- #guard_msgs in
-- #eval len result1["dice"]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded