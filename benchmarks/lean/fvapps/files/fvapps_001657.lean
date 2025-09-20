-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def blast_sequence (aliens : List (List Int)) (position : Int × Int) : Option (List Int) := sorry

theorem empty_aliens {aliens : List (List Int)} {pos : Int × Int} 
  (h1 : ∀ row ∈ aliens, ∀ x ∈ row, x = 0)
  (h2 : aliens.length > 0) 
  (h3 : ∀ row ∈ aliens, row.length > 0)
  (h4 : ∀ row ∈ aliens, row.length ≤ 20)
  (h5 : aliens.length = 1)
  (h6 : pos.1 ≥ 0)
  (h7 : pos.1 ≤ 50) 
  (h8 : pos.2 ≥ 0)
  (h9 : pos.2 ≤ 19) :
  blast_sequence aliens pos = some [] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_properties {aliens : List (List Int)} {pos : Int × Int} {result : List Int}
  (h1 : ∀ row ∈ aliens, row.length > 0)
  (h2 : ∀ row ∈ aliens, row.length ≤ 10)
  (h3 : aliens.length > 0)
  (h4 : aliens.length = 1)
  (h5 : ∀ row ∈ aliens, ∀ x ∈ row, x ≥ -5 ∧ x ≤ 5)
  (h6 : pos.1 ≥ 0)
  (h7 : pos.1 ≤ 20)
  (h8 : pos.2 ≥ 0) 
  (h9 : pos.2 ≤ 9)
  (h10 : blast_sequence aliens pos = some result) :
  (∀ i < result.length - 1, result[i]! < result[i+1]!) ∧ 
  (∀ x ∈ result, x ≥ 0) := sorry
-- </vc-theorems>