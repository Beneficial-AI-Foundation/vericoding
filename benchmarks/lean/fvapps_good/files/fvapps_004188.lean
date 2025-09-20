-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reg_sum_hits (dices : Nat) (sides : Nat) : List (Nat × Nat) := sorry 

theorem reg_sum_hits_valid_results (dices sides : Nat) 
  (h1 : dices > 0) (h2 : sides > 1) (h3 : sides ≤ 10) :
  let result := reg_sum_hits dices sides
  (∀ x, x ∈ result → 
    (x.1 ≥ dices ∧ x.1 ≤ dices * sides) ∧ 
    x.2 > 0) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reg_sum_hits_consecutive_sums (dices sides : Nat)
  (h1 : dices > 0) (h2 : sides > 1) (h3 : sides ≤ 10) :
  let result := reg_sum_hits dices sides
  let sums := List.map Prod.fst result
  ∀ i, i < sums.length - 1 →
    List.get! sums (i+1) = List.get! sums i + 1 := sorry

theorem reg_sum_hits_symmetric_probs (dices sides : Nat)
  (h1 : dices > 0) (h2 : sides > 1) (h3 : sides ≤ 10) :
  let result := reg_sum_hits dices sides
  let probs := List.map Prod.snd result
  probs = List.reverse probs := sorry

theorem reg_sum_hits_single_die (sides : Nat)
  (h1 : sides > 1) (h2 : sides ≤ 10) :
  let result := reg_sum_hits 1 sides
  (List.length result = sides) ∧
  (∀ x, x ∈ result → Prod.snd x = 1) ∧
  (List.map Prod.fst result = List.map (· + 1) (List.range sides)) := sorry
-- </vc-theorems>