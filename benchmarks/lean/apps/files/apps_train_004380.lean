def gc_content (s : String) : Float := sorry

theorem gc_content_bounded (s : String) :
  0.0 ≤ gc_content s ∧ gc_content s ≤ 100.0 := sorry

-- <vc-helpers>
-- </vc-helpers>

def count (s : String) (c : String) : Nat := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible