-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generate_diagonal (d : Nat) (l : Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem generate_diagonal_length
  (d l : Nat) :
  (generate_diagonal d l).length = l :=
  sorry

theorem generate_diagonal_first_element
  {d l : Nat}
  (h : l > 0) :
  (generate_diagonal d l).get ⟨0, sorry⟩ = 1 :=
  sorry

theorem generate_diagonal_pattern
  {d l i: Nat}
  (h1 : i < l)
  (h2 : i > 0) :
  let result := generate_diagonal d l
  (result.get ⟨i, sorry⟩) = (result.get ⟨i-1, sorry⟩) * (d+i) / i :=
  sorry

theorem zero_diagonal_all_ones
  (l : Nat) : 
  List.all (generate_diagonal 0 l) (· = 1) :=
  sorry

theorem empty_length
  (d : Nat) :
  generate_diagonal d 0 = [] :=
  sorry
-- </vc-theorems>