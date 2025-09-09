-- <vc-helpers>
-- </vc-helpers>

def find_children (s : String) : String := sorry

instance : LE (Char × Bool) where
  le := λ a b => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

theorem find_children_empty : find_children "" = "" := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible