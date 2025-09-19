-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def determine_winner (n x : Nat) (stones : List Nat) : String := sorry

def ListPerm {α : Type} (l₁ l₂ : List α) : Prop := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem determine_winner_well_defined_output
  (n x : Nat) (stones : List Nat) (h₁ : x > 0) (h₂ : x ≤ n) : 
  determine_winner n x stones = "Jesse" ∨ determine_winner n x stones = "Walter" := sorry

theorem determine_winner_length_preserving
  (n x : Nat) (stones : List Nat) (h₁ : stones.length = n) : 
  stones.length = n := sorry

theorem determine_winner_permutation_invariant
  (n x : Nat) (stones₁ stones₂ : List Nat) 
  (h₁ : ListPerm stones₁ stones₂) (h₂ : stones₁.length = n) (h₃ : stones₂.length = n) :
  determine_winner n x stones₁ = determine_winner n x stones₂ := sorry

theorem determine_winner_increment_invariant
  (n x : Nat) (stones : List Nat) (h : stones.length = n) :
  determine_winner n x stones = determine_winner n x (stones.map (· + 2)) := sorry

theorem determine_winner_single_stone_parity
  (n : Nat) (stones : List Nat) 
  (h₁ : stones = List.replicate n 1) :
  determine_winner n 1 stones = (if n % 2 = 1 then "Jesse" else "Walter") := sorry
-- </vc-theorems>