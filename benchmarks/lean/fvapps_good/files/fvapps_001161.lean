-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_mercury_leak (grid : List (List Nat)) (height width : Nat) (queries : List (Nat × Nat × Nat)) : List Nat := sorry

theorem solve_mercury_leak_results_length 
  (grid : List (List Nat)) (h w : Nat) (queries : List (Nat × Nat × Nat)) :
  (List.length (solve_mercury_leak grid h w queries)) = List.length queries := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_mercury_leak_results_bounds
  (grid : List (List Nat)) (h w : Nat) (queries : List (Nat × Nat × Nat))
  (res := solve_mercury_leak grid h w queries) :
  ∀ x ∈ res, 0 ≤ x ∧ x ≤ 4 := sorry

theorem solve_mercury_leak_monotonic
  (grid : List (List Nat)) (h w : Nat) (queries : List (Nat × Nat × Nat))
  (res := solve_mercury_leak grid h w queries)
  (i : Fin queries.length) (hi : i.val + 1 < queries.length)
  (hres : res.length = queries.length) :
  let q₁ := queries.get i
  let q₂ := queries.get ⟨i.val + 1, hi⟩
  let i' : Fin res.length := ⟨i.val, by rw [hres]; exact i.isLt⟩
  let i1 : Fin res.length := ⟨i.val + 1, by rw [hres]; exact hi⟩
  let r₁ := res.get i'
  let r₂ := res.get i1
  q₁.1 = q₂.1 → 
  q₁.2.1 = q₂.2.1 →
  q₁.2.2 < q₂.2.2 →
  r₁ ≤ r₂ := sorry

theorem solve_mercury_leak_connectivity
  (grid : List (List (Nat))) 
  (h : List.length grid = 3)
  (w : ∀ row ∈ grid, List.length row = 3)
  (center_val := (grid[1]!)[1]!) :
  let query := [(2, 2, 5)]
  let res := solve_mercury_leak grid 3 3 query
  center_val < 5 →
  (∃ (r c : Nat), (r,c) ∈ [(0,1), (1,0), (1,2), (2,1)] ∧ 
    ((grid[r]!)[c]!) < 5) →
  res[0]! > 1 := sorry

theorem solve_mercury_leak_power_bounds
  (grid : List (List Nat))
  (h w : Nat) 
  (hlen : List.length (solve_mercury_leak grid h w [(1,1,0), (2,2,10)]) > 1) :
  let queries := [(1,1,0), (2,2,10)]
  let res := solve_mercury_leak grid h w queries
  res[0]! = 0 ∧ res[1]! ≤ h * w := sorry
-- </vc-theorems>