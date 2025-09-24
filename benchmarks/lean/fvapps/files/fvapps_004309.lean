-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_children (s : String) : String := sorry

instance : LE (Char × Bool) where
  le := λ a b => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)
-- </vc-definitions>

-- <vc-theorems>
theorem find_children_empty : find_children "" = "" := sorry
-- </vc-theorems>