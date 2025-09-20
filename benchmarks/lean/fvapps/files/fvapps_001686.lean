-- <vc-preamble>
def abs (x : Int) : Int :=
  if x < 0 then -x else x

def listSum : List Int → Int 
  | [] => 0
  | x::xs => x + listSum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def splitlist (nums : List Int) : Option (List Int × List Int) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem splitlist_length (nums : List Int) :
  match splitlist nums with
  | none => true
  | some (a, b) => List.length a + List.length b = List.length nums
  := by sorry

theorem splitlist_elements (nums : List Int) :
  match splitlist nums with
  | none => true
  | some (a, b) => ∀ x : Int, 
    ((x ∈ a ∨ x ∈ b) ↔ x ∈ nums)
  := by sorry

theorem splitlist_minimal_difference (nums : List Int) :
  match splitlist nums with
  | none => true
  | some (a, b) => ∀ split : List Int × List Int,
    (∀ x, (x ∈ split.1 ∨ x ∈ split.2) ↔ x ∈ nums) →
    abs (listSum a - listSum b) ≤ abs (listSum split.1 - listSum split.2)
  := by sorry

theorem splitlist_equal_elements (nums : List Int)
  (h_even : nums.length % 2 = 0)
  (h_equal : ∀ x ∈ nums, ∀ y ∈ nums, x = y) :
  match splitlist nums with
  | none => true
  | some (a, b) => listSum a = listSum b
  := by sorry
-- </vc-theorems>