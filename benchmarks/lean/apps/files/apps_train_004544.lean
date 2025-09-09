def FamilyRelation := String

def FamilyList := List (String × String)

-- <vc-helpers>
-- </vc-helpers>

def relations (family : FamilyList) (pair : String × String) : Option FamilyRelation := sorry

theorem relation_returns_valid (family : FamilyList) (pair : String × String) :
  let result := relations family pair
  match result with
  | some rel => rel = "Mother" ∨ rel = "Grandmother" ∨ rel = "Daughter" ∨ 
                rel = "Granddaughter" ∨ rel = "Sister" ∨ rel = "Cousin" ∨ 
                rel = "Aunt" ∨ rel = "Niece"
  | none => True
  := sorry

theorem grandmother_granddaughter_symmetry (family : FamilyList) (a b : String) :
  relations family (a, b) = some "Grandmother" → 
  relations family (b, a) = some "Granddaughter" := sorry

theorem sister_symmetry (family : FamilyList) (a b : String) :
  relations family (a, b) = some "Sister" →
  relations family (b, a) = some "Sister" := sorry

theorem aunt_niece_symmetry (family : FamilyList) (a b : String) :
  relations family (a, b) = some "Aunt" →
  relations family (b, a) = some "Niece" := sorry

/-
info: 'Grandmother'
-/
-- #guard_msgs in
-- #eval relations [("Enid", "Susan"), ("Susan", "Deborah"), ("Enid", "Dianne")] ("Deborah", "Enid")

/-
info: 'Sister'
-/
-- #guard_msgs in
-- #eval relations [("Sarah", "Emily"), ("Sarah", "Kate")] ("Emily", "Kate")

/-
info: 'Aunt'
-/
-- #guard_msgs in
-- #eval relations [("Mary", "Sarah"), ("Sarah", "Emily"), ("Mary", "Jane")] ("Emily", "Jane")

-- Apps difficulty: introductory
-- Assurance level: unguarded