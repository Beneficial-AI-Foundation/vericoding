-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_dentist (n : Nat) (kids : List (List Nat)) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_dentist_result_valid (n : Nat) (kids : List (List Nat)) 
    (h1 : n > 0) (h2 : ∀ k ∈ kids, k.length = 3) : 
    let result := solve_dentist n kids
    ∀ x ∈ result, 1 ≤ x ∧ x ≤ n :=
sorry

theorem solve_dentist_result_increasing (n : Nat) (kids : List (List Nat))
    (h1 : n > 0) (h2 : ∀ k ∈ kids, k.length = 3) :
    let result := solve_dentist n kids
    ∀ (a b : Nat), a ∈ result → b ∈ result → 
      result.indexOf a < result.indexOf b → a < b :=
sorry

theorem solve_dentist_result_unique (n : Nat) (kids : List (List Nat))
    (h1 : n > 0) (h2 : ∀ k ∈ kids, k.length = 3) :
    let result := solve_dentist n kids
    ∀ (x y : Nat), x ∈ result → y ∈ result → x = y → x = y :=
sorry

theorem solve_dentist_preserves_input (n : Nat) (kids : List (List Nat))
    (h1 : n > 0) (h2 : ∀ k ∈ kids, k.length = 3) :
    let orig := kids
    let _ := solve_dentist n kids
    kids = orig :=
sorry

theorem solve_dentist_single_kid :
    solve_dentist 1 [[1, 1, 10]] = [1] :=
sorry

theorem solve_dentist_zero_patience (kids : List (List Nat))
    (h1 : ∀ k ∈ kids, k.length = 3)
    (h2 : ∀ k ∈ kids, k.getD 2 0 = 0) :
    let n := kids.length
    (solve_dentist n kids).length = 0 :=
sorry
-- </vc-theorems>