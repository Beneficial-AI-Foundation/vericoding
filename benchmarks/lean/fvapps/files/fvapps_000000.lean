-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (words : List String) : List Int :=
  sorry

def abs (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_output_structure (n : Nat) (words : List String) :
  let result := solve n words
  (result = [-1] ∨
   (result.length ≥ 1 ∧
    ∀ x ∈ result, ∃ i : Int, x = i ∧
    let count := result[0]!
    result.length = count + 1 ∧
    ∀ i ∈ result.tail, 1 ≤ i ∧ i ≤ n)) :=
sorry

theorem solve_minimal_flips (n : Nat) (words : List String) :
  let result := solve n words
  result ≠ [-1] →
  let zeros_to_ones := (words.filter (λ w => w.front = '0' ∧ w.back = '1')).length
  let ones_to_zeros := (words.filter (λ w => w.front = '1' ∧ w.back = '0')).length
  let min_flips := (abs (zeros_to_ones - ones_to_zeros)) / 2
  result[0]! = min_flips :=
sorry
-- </vc-theorems>