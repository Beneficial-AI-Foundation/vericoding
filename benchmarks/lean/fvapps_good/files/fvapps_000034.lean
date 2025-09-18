-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_display (n : Nat) : Nat := sorry

theorem result_only_valid_digits {n : Nat} (h : n ≥ 3) (h₂ : n ≤ 100) :
  ∀ c : Char, c ∈ (toString (find_max_display n)).data → c = '1' ∨ c = '7' := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem odd_lengths_start_with_seven {n : Nat} (h : n ≥ 3) (h₂ : n ≤ 100) (h₃ : n % 2 = 1) :
  ((toString (find_max_display n)).data).get! 0 = '7' := sorry

theorem even_lengths_all_ones {n : Nat} (h : n ≥ 4) (h₂ : n ≤ 100) (h₃ : n % 2 = 0) :
  ∀ c : Char, c ∈ (toString (find_max_display n)).data → c = '1' := sorry

theorem result_is_positive {n : Nat} (h : n ≥ 3) (h₂ : n ≤ 100) :
  find_max_display n > 0 := sorry
-- </vc-theorems>