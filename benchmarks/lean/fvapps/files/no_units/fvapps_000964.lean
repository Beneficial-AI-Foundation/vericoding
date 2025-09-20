-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_supermarket (slots : List Nat) : List String := sorry
def check (n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_supermarket_correct_length (slots : List Nat) 
  (h : slots.length ≥ 1 ∧ slots.length ≤ 100) 
  (h2 : ∀ x ∈ slots, x ≤ 1000) : 
  let result := solve_supermarket slots 
  (result.length = slots.length) ∧ 
  (∀ x ∈ result, x = "YES" ∨ x = "NO") := sorry

theorem solve_supermarket_single_slot (slot : Nat) (h : slot ≤ 1000) :
  let result := solve_supermarket [slot]
  (slot < 3 → result = ["NO"]) ∧ 
  (∃ n : Nat, n * n = slot → 
    (check n = 1 → result = ["YES"]) ∧
    (check n ≠ 1 → result = ["NO"])) ∧
  ((¬ ∃ n : Nat, n * n = slot) → result = ["NO"]) := sorry

theorem solve_supermarket_perfect_squares 
  (primes : List Nat := [2, 3, 5, 7, 11, 13]) :
  let squares := primes.map (λ p => p * p)
  solve_supermarket squares = List.replicate squares.length "YES" := sorry

theorem solve_supermarket_non_perfect_squares
  (non_squares : List Nat := [5, 6, 7, 8, 10, 11, 12, 13, 14, 15]) :
  solve_supermarket non_squares = List.replicate non_squares.length "NO" := sorry
-- </vc-theorems>