-- <vc-preamble>
def solve_snuffles_array (n d : Nat) (arr : List Int) : Int :=
  sorry

def verify_solution (n d: Nat) (arr : List Int) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_sum (xs : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem snuffles_array_properties {n d : Nat} {arr : List Int}
  (h1 : n > 0)
  (h2 : d > 0) 
  (h3 : d ≤ n)
  (h4 : arr.length = n) :
  let result := solve_snuffles_array n d arr
  (result ≥ 0 → verify_solution n d arr = true) ∧ 
  (result = -1 → 
    (∃ i : Nat, i < d ∧ 
      let group := (List.range arr.length).filter (fun j => j % d = i)
      let group_sum := list_sum (group.map (fun j => arr.get! j))
      let group_avg := group_sum / group.length
      group_avg ≠ (list_sum arr / arr.length))) :=
sorry

theorem all_equal_array_zero {n : Nat} {x : Int}
  (h1 : n > 0) :
  solve_snuffles_array n 1 (List.replicate n x) = 0 :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_snuffles_array 5 2 [1, 4, 5, 2, 3]

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_snuffles_array 3 1 [1, 4, 1]

/-
info: -1
-/
-- #guard_msgs in
-- #eval solve_snuffles_array 4 2 [3, 4, 3, 5]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded