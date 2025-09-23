-- <vc-preamble>
def FamilyRelation := String

def FamilyList := List (String × String)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def relations (family : FamilyList) (pair : String × String) : Option FamilyRelation := sorry

theorem relation_returns_valid (family : FamilyList) (pair : String × String) :
  let result := relations family pair
  match result with
  | some rel => rel = "Mother" ∨ rel = "Grandmother" ∨ rel = "Daughter" ∨ 
                rel = "Granddaughter" ∨ rel = "Sister" ∨ rel = "Cousin" ∨ 
                rel = "Aunt" ∨ rel = "Niece"
  | none => True
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem grandmother_granddaughter_symmetry (family : FamilyList) (a b : String) :
  relations family (a, b) = some "Grandmother" → 
  relations family (b, a) = some "Granddaughter" := sorry

theorem sister_symmetry (family : FamilyList) (a b : String) :
  relations family (a, b) = some "Sister" →
  relations family (b, a) = some "Sister" := sorry

theorem aunt_niece_symmetry (family : FamilyList) (a b : String) :
  relations family (a, b) = some "Aunt" →
  relations family (b, a) = some "Niece" := sorry
-- </vc-theorems>