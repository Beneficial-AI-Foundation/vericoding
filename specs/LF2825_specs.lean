-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def advice (agents : List Pos) (n : Nat) : List Pos :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem advice_empty_grid (n : Nat) :
  let result := advice [] n
  n = 0 → result = [] ∧
  n > 0 → (
    result.length = n * n ∧
    result.all (fun (x,y) => x < n ∧ y < n)
  ) := sorry

theorem advice_result_properties (n : Nat) (agents : List Pos) :
  n > 0 →
  let result := advice agents n
  result.all (fun (x,y) => x < n ∧ y < n) ∧
  let validAgents := agents.filter (fun (x,y) => x < n ∧ y < n)
  ∀ p, p ∈ validAgents → p ∉ result
  := sorry

theorem advice_connected_safe_spaces (n : Nat) (agents : List Pos) :
  n > 0 →
  let result := advice agents n
  result.isEmpty ∨
  ∀ x y, (x,y) ∈ result →
    let adjacent := [(x,y+1), (x,y), (x+1,y), (x,y)].filter (fun (nx,ny) => nx < n ∧ ny < n)
    let safeAdj := adjacent.filter (fun p => p ∈ result)
    safeAdj.isEmpty ∨ ∃ p, p ∈ safeAdj
  := sorry
-- </vc-theorems>