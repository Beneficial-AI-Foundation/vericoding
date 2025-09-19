-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def prisonAfterNDays (cells : List Nat) (n : Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem prison_result_format 
  (cells : List Nat) (n : Nat) 
  (h1 : cells.length = 8)
  (h2 : ∀ x ∈ cells, x = 0 ∨ x = 1) :
  let result := prisonAfterNDays cells n
  (result.length = 8) ∧ 
  (∀ x ∈ result, x = 0 ∨ x = 1) :=
sorry

theorem prison_endpoint_cells
  (cells : List Nat)
  (h1 : cells.length = 8)
  (h2 : ∀ x ∈ cells, x = 0 ∨ x = 1) :
  let result := prisonAfterNDays cells 1
  result.get ⟨0, sorry⟩ = 0 ∧ 
  result.get ⟨7, sorry⟩ = 0 :=
sorry
-- </vc-theorems>