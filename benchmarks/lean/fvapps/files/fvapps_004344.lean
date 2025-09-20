-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_nth_digit (a b n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_nth_digit_result_is_digit (a b n : Nat) 
    (h1 : a ≤ 9) (h2 : b ≤ 9) : 
    find_nth_digit a b n ≤ 9 :=
  sorry

theorem find_nth_digit_first_pos (a b : Nat)
    (h1 : a ≤ 9) (h2 : b ≤ 9) :
    find_nth_digit a b 0 = a :=
  sorry

theorem find_nth_digit_second_pos (a b : Nat) 
    (h1 : a ≤ 9) (h2 : b ≤ 9) :
    find_nth_digit a b 1 = b :=
  sorry

theorem find_nth_digit_zero_sequence (n : Nat) :
    find_nth_digit 0 0 n = 0 :=
  sorry

theorem find_nth_digit_cycle (a b i : Nat)
    (h1 : a ≤ 9) (h2 : b ≤ 9) :
    find_nth_digit a b (20 + i) = find_nth_digit a b (40 + i) :=
  sorry
-- </vc-theorems>