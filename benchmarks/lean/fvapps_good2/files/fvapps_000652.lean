-- <vc-preamble>
def min_list (l : List Nat) : Nat :=
match l with
| [] => 0
| h::t => List.foldl min h t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_complete_team (N : Nat) (S : Nat) (prices : List Nat) (positions : List Nat) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_lists :
  can_complete_team 0 0 [] [] = "no" :=
sorry

theorem all_defenders_or_forwards_only (p₁ p₂ p₃ : Nat) :
  can_complete_team 3 50 [p₁, p₂, p₃] [0, 0, 0] = "no" ∧
  can_complete_team 3 50 [p₁, p₂, p₃] [1, 1, 1] = "no" :=
sorry

theorem valid_input_result {N S : Nat} {prices positions : List Nat}
  (h₁ : N ≥ 2)
  (h₂ : S < 100)
  (h₃ : prices.length = N)
  (h₄ : positions.length = N)
  (h₅ : ∀ p ∈ prices, p ≥ 1 ∧ p ≤ 100)
  (h₆ : ∀ p ∈ positions, p = 0 ∨ p = 1)
  (h₇ : positions.get! 0 = 0)
  (h₈ : positions.get! 1 = 1) :
  can_complete_team N S prices positions = "yes" ∨
  can_complete_team N S prices positions = "no" :=
sorry

theorem valid_input_cost {N S : Nat} {prices positions : List Nat}
  (h₁ : N ≥ 2)
  (h₂ : S < 100)
  (h₃ : prices.length = N)
  (h₄ : positions.length = N)
  (h₅ : ∀ p ∈ prices, p ≥ 1 ∧ p ≤ 100)
  (h₆ : ∀ p ∈ positions, p = 0 ∨ p = 1)
  (h₇ : positions.get! 0 = 0)
  (h₈ : positions.get! 1 = 1) :
  let min_defender := min_list (List.filterMap (λ i => if positions.get! i = 0 then some (prices.get! i) else none) (List.range N))
  let min_forward := min_list (List.filterMap (λ i => if positions.get! i = 1 then some (prices.get! i) else none) (List.range N))
  100 - S ≥ min_defender + min_forward ↔ can_complete_team N S prices positions = "yes" :=
sorry

theorem team_costs {N S : Nat} {prices : List Nat}
  (h₁ : N ≥ 2)
  (h₂ : S < 100)
  (h₃ : prices.length = N)
  (h₄ : ∀ p ∈ prices, p ≥ 1 ∧ p ≤ 100)
  (h₅ : can_complete_team N S prices (List.map (λ i => i % 2) (List.range N)) = "yes") :
  100 - S ≥ min_list (List.filterMap (λ i => if i % 2 = 0 then some (prices.get! i) else none) (List.range N)) +
           min_list (List.filterMap (λ i => if i % 2 = 1 then some (prices.get! i) else none) (List.range N)) :=
sorry
-- </vc-theorems>