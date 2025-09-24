-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_winner (n : Nat) : String := sorry

theorem find_winner_valid_values (n : Nat) : 
  n > 0 → (find_winner n = "Me" ∨ find_winner n = "Grinch") := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_winner_powers_of_two_one :
  find_winner 2 = "Me" := sorry

theorem find_winner_powers_of_two (n : Nat) :
  n > 1 → find_winner (2^n) = "Grinch" := sorry

theorem find_winner_one :
  find_winner 1 = "Grinch" := sorry

theorem find_winner_odd_numbers (n : Nat) :
  n > 1 → n % 2 = 1 → find_winner n = "Me" := sorry

theorem find_winner_known_cases_four :
  find_winner 4 = "Grinch" := sorry

theorem find_winner_known_cases_six :
  find_winner 6 = "Grinch" := sorry

theorem find_winner_known_cases_twelve :
  find_winner 12 = "Me" := sorry

theorem find_winner_known_cases_sixteen :
  find_winner 16 = "Grinch" := sorry
-- </vc-theorems>