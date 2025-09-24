-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fix_tree_sequence (n : Nat) (A : List Nat) : Nat × List Nat := sorry

def is_valid_tree (A : List Nat) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fix_tree_sequence_properties 
  (n : Nat) 
  (A : List Nat)
  (h : A.length = n) :
  let (changes, result) := fix_tree_sequence n A
  -- Result has same length
  result.length = A.length ∧ 
  -- Changes non-negative (implicit for Nat)
  -- Result is valid tree
  is_valid_tree result = true ∧
  -- Original array unchanged
  A = A ∧
  -- Changes matches actual differences
  changes = (List.zip A result).foldl (fun acc p => if p.1 = p.2 then acc else acc + 1) 0
  := sorry

theorem already_valid_tree
  (A : List Nat)
  (h : is_valid_tree A = true) :
  let (changes, result) := fix_tree_sequence A.length A
  changes = 0 ∧ result = A
  := sorry
-- </vc-theorems>