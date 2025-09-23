-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_valid_hate_pair (n : Nat) (pair : Nat × Nat) : Bool := sorry

def count_dangerous_triples (n : Nat) (hate_pairs : List (Nat × Nat)) (salary_changes : List Nat) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dangerous_triples_empty_inputs
  (n : Nat)
  (h : n > 0) :
  count_dangerous_triples n [] [] = [0] := sorry
-- </vc-theorems>