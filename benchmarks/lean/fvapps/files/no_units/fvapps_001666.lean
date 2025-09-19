-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shallowest_path (river : List (List Int)) : List (Int × Int) := sorry

def abs (n : Int) : Int := 
  if n < 0 then -n else n

-- Given any valid river array:
-- 1. Path starts at first column
-- 2. Path ends at last column  
-- 3. Path is contiguous with only adjacent moves allowed
-- 4. All coordinates are valid
-- </vc-definitions>

-- <vc-theorems>
theorem path_properties {river : List (List Int)} (h : river.length > 0) (h2 : ∀ (row : List Int), row ∈ river → row.length = (List.head! river).length) :
  let path := shallowest_path river
  -- Path starts at first column
  (∀ p ∈ path, (List.head! path).2 = 0) ∧ 
  -- Path ends at last column
  ((List.head! river).length - 1 = (List.get! path (path.length - 1)).2) ∧
  -- Path is contiguous
  (∀ i < path.length - 1, 
    let p1 := List.get! path i
    let p2 := List.get! path (i+1)
    abs (p2.1 - p1.1) ≤ 1 ∧ 
    abs (p2.2 - p1.2) ≤ 1 ∧
    (p2.1 ≠ p1.1 ∨ p2.2 ≠ p1.2)) ∧
  -- All coordinates are valid
  (∀ p ∈ path, p.1 ≥ 0 ∧ p.1 < river.length ∧ p.2 ≥ 0 ∧ p.2 < (List.head! river).length) :=
  sorry

-- For a single column river:
-- Path has length 1 and is at first column

theorem single_column_path {river : List (List Int)} (h : ∀ row ∈ river, row.length = 1) :
  let path := shallowest_path river
  path.length = 1 ∧ (List.head! path).2 = 0 :=
  sorry

-- For a single row river:
-- All x coordinates are 0 and ends at first column 

theorem single_row_path {river : List (List Int)} (h : river.length = 1) :
  let path := shallowest_path river
  (∀ p ∈ path, p.1 = 0) ∧ (List.get! path (path.length - 1)).2 = 0 :=
  sorry
-- </vc-theorems>