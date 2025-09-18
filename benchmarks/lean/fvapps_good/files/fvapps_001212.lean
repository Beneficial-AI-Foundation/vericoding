-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_unique_string (s : List Char) (k : Nat) : List Char := sorry

theorem solve_unique_string_properties 
  (s : List Char) (k : Nat) (result : List Char)
  (h : result = solve_unique_string s k)
  (h₁ : result ≠ []) :
  List.length result = List.length s ∧ 
  (∀ i j, i < j → j < List.length result → List.get! result i ≤ List.get! result j) ∧
  List.length (List.filter (fun c => c ∈ s) result) ≤ k ∧
  (∀ c ∈ result, c.isLower) ∧
  List.length result = List.length (List.eraseDups result) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_zero_k_property
  (s : List Char) (result : List Char) 
  (h : result = solve_unique_string s 0)
  (h₁ : result ≠ []) :
  ∀ c ∈ result, c ∉ s := sorry
-- </vc-theorems>