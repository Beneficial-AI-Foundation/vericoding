-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_arithmetic_sequence (n : Nat) (init : List Int) : List Int := sorry

theorem arithmetic_sequence_properties
  (n : Nat) (start diff : Int) (h1 : n ≥ 4) (h2 : n ≤ 100) 
  (h3 : start ≥ -100) (h4 : start ≤ 100) 
  (h5 : diff ≥ -10) (h6 : diff ≤ 10) :
  let base_seq := [start, start + diff, start + 2*diff, start + 3*diff]
  let result := find_arithmetic_sequence n base_seq
  (result.length = n) ∧ 
  (∀ i j : Nat, i + 1 < result.length → j + 1 < result.length → 
    result.get! (i+1) - result.get! i = result.get! (j+1) - result.get! j) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem constant_sequence_property 
  (n : Nat) (const : Int) (h1 : n ≥ 4) (h2 : n ≤ 100) :
  let init := [const, const, const, const]
  let result := find_arithmetic_sequence n init
  (result.length = n) ∧
  (∀ i : Nat, i < result.length → result.get! i = const) := sorry

theorem basic_cases :
  (find_arithmetic_sequence 4 [1, 3, 10, 7] = [1, 3, 5, 7]) ∧
  (find_arithmetic_sequence 5 [-10, -5, 0, 5, 10] = [-10, -5, 0, 5, 10]) ∧
  (find_arithmetic_sequence 4 [2, 2, 2, 10] = [2, 2, 2, 2]) := sorry
-- </vc-theorems>