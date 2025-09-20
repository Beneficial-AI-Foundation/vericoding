-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def dating_range (age : Int) : String := sorry

theorem dating_range_child (age : Int) (h : 1 ≤ age ∧ age ≤ 14) : 
  let result := dating_range age
  let min_age := (result.splitOn "-").head!.toInt!
  let max_age := (result.splitOn "-").getLast!.toInt!
  min_age = (age * 9/10) ∧ 
  max_age = (age * 11/10) ∧
  min_age ≤ age ∧ age ≤ max_age := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dating_range_adult (age : Int) (h : 15 ≤ age ∧ age ≤ 100) :
  let result := dating_range age
  let min_age := (result.splitOn "-").head!.toInt!
  let max_age := (result.splitOn "-").getLast!.toInt!
  min_age = age/2 + 7 ∧
  max_age = (age-7) * 2 ∧
  min_age ≤ age ∧ age ≤ max_age := sorry

theorem dating_range_format (age : Int) (h : 1 ≤ age ∧ age ≤ 100) :
  let result := dating_range age
  let parts := result.splitOn "-"
  result.length > 0 ∧
  parts.length = 2 ∧
  let min_age := parts.head!.toInt!
  let max_age := parts.getLast!.toInt!
  min_age ≤ max_age := sorry
-- </vc-theorems>