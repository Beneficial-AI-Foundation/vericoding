-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def do_math (input : String) : Int :=
  sorry

def make_alpha_num (nums : List Int) (letters : List String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem do_math_returns_int {nums : List Int} {letters : List String}
  (h_nums_size : nums.length ≥ 2 ∧ nums.length ≤ 10)
  (h_letters_size : letters.length ≥ 2 ∧ letters.length ≤ 10)
  (h_nums_bound : ∀ n ∈ nums, 1 ≤ n ∧ n ≤ 1000)
  (h_letters_single : ∀ l ∈ letters, l.length = 1)
  : ∃ n : Int, do_math (make_alpha_num nums letters) = n :=
sorry

theorem letter_position_invariant {letter : String}
  (h_letter_single : letter.length = 1) :
  do_math ("123" ++ letter ++ " 456" ++ letter) =
  do_math (letter ++ "123 " ++ letter ++ "456") :=
sorry
-- </vc-theorems>