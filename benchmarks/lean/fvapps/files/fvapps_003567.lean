-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def round_to_five (numbers : List Float) : List Float := sorry

theorem round_to_five_multiple_of_five (numbers : List Float) :
  let result := round_to_five numbers
  ∀ x ∈ result, ∃ n : Float, x = n * 5 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem round_to_five_close_to_original (numbers : List Float) :
  let result := round_to_five numbers
  ∀ (orig rounded : Float), 
    orig ∈ numbers → rounded ∈ result →
    Float.abs (orig - rounded) ≤ 2.5 := sorry

theorem round_to_five_preserves_length (numbers : List Float) :
  List.length (round_to_five numbers) = List.length numbers := sorry

theorem round_to_five_empty :
  round_to_five [] = [] := sorry

theorem round_to_five_exact_multiples (n : Float) :
  round_to_five [n * 5] = [n * 5] := sorry
-- </vc-theorems>