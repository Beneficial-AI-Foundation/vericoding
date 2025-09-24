-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Matrix := List (List Nat)

def count_words (matrix : Matrix) (end_char : Char) (length : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_words_non_negative (matrix : Matrix) (end_char : Char) (length : Nat) :
  count_words matrix end_char length ≥ 0 :=
sorry

theorem count_words_less_than_modulo (matrix : Matrix) (end_char : Char) (length : Nat) :
  count_words matrix end_char length < (10^9 + 7) :=
sorry

theorem empty_graph_no_words (end_char : Char) (length : Nat) :
  let empty_matrix := List.replicate 26 (List.replicate 26 0)
  count_words empty_matrix end_char length = 0 :=
sorry

theorem simple_path_one_word_length_three :
  let simple_matrix := List.replicate 26 (List.replicate 26 0)
  let m1 := simple_matrix -- TODO: Add 1 at position [0][1]
  let m2 := m1 -- TODO: Add 1 at position [1][2]
  count_words m2 'c' 3 = 1 :=
sorry

theorem simple_path_one_word_length_two :
  let simple_matrix := List.replicate 26 (List.replicate 26 0)
  let m1 := simple_matrix -- TODO: Add 1 at position [0][1]
  let m2 := m1 -- TODO: Add 1 at position [1][2]
  count_words m2 'b' 2 = 1 :=
sorry
-- </vc-theorems>