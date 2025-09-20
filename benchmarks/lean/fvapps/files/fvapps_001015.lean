-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def determine_candy_game_winner (limak_max : Nat) (bob_max : Nat) : String := sorry

theorem candy_game_returns_valid_winner (limak_max bob_max : Nat) 
  (h1 : limak_max > 0) (h2 : bob_max > 0) (h3 : limak_max ≤ 1000) (h4 : bob_max ≤ 1000) :
  determine_candy_game_winner limak_max bob_max = "Limak" ∨ 
  determine_candy_game_winner limak_max bob_max = "Bob" := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem limak_much_larger_valid_winner (n : Nat)
  (h1 : n > 0) (h2 : n ≤ 100) :
  determine_candy_game_winner (n * 10) n = "Limak" ∨
  determine_candy_game_winner (n * 10) n = "Bob" :=
  sorry
-- </vc-theorems>